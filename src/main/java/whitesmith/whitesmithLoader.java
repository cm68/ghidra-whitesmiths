/* ###
 * IP: GHIDRA
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 *      http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package whitesmith;

import java.io.IOException;
import java.util.*;

import ghidra.app.util.Option;
import ghidra.app.util.bin.BinaryReader;
import ghidra.app.util.bin.ByteProvider;
import ghidra.app.util.importer.MemoryConflictHandler;
import ghidra.app.util.importer.MessageLog;
import ghidra.app.util.opinion.AbstractLibrarySupportLoader;
import ghidra.app.util.opinion.LoadSpec;
import ghidra.app.util.opinion.Loader;
import ghidra.framework.model.DomainObject;
import ghidra.framework.store.LockException;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressOutOfBoundsException;
import ghidra.program.model.address.AddressOverflowException;
import ghidra.program.model.address.AddressSpace;
import ghidra.program.model.lang.CompilerSpecDescription;
import ghidra.program.model.lang.Endian;
import ghidra.program.model.lang.LanguageCompilerSpecPair;
import ghidra.program.model.lang.LanguageDescription;
import ghidra.program.model.listing.Program;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryAccessException;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.mem.MemoryConflictException;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.symbol.SymbolTable;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.DuplicateNameException;
import ghidra.util.exception.InvalidInputException;
import ghidra.util.task.TaskMonitor;


/**
 * the whitesmith's c defined a quirky object file format that had some flexibility
 * it supported 16 and 32 bit integers in little and big endian, and 1 to 15 byte symbol lengths
 * there were 4 segments, of which 3 were meaningful in the object file: text, data, and bss
 * this is coded to deal with all options, but I've only got sample files with 1 flavor: 
 * 		2 byte integers, 1 byte alignment, little endian, 9 character symbols
 */
public class whitesmithLoader extends AbstractLibrarySupportLoader {

	private BinaryReader reader;
	private MemoryBlock low;
	private MemoryBlock code;
	private MemoryBlock data;
	private MemoryBlock bss;

	private long file_textoff;			// file offsets of each chunk
	private long file_dataoff;
	private long file_symoff;
	private long file_relocoff;
	
	private	int symbolsize;				// the size of a symbol in file
	private Endian ness;
	private int intsize;

	private header header;
	private symbol[] symbols;
	private HashMap<Integer, symbol> relocs;
	
	private final static short MAGIC 			= 0x99;
	private final static short CONF_SYM_MASK 	= 0x07;
	private final static short	CONF_SYM_1		= 0x00;
	private final static short 	CONF_SYM_3		= 0x01;
	private final static short 	CONF_SYM_5		= 0x02;
	private final static short 	CONF_SYM_7		= 0x03;
	private final static short 	CONF_SYM_9		= 0x04;
	private final static short 	CONF_SYM_11		= 0x05;
	private final static short 	CONF_SYM_13		= 0x06;
	private final static short 	CONF_SYM_15		= 0x07;
	private final static short CONF_INT_4 		= 0x08;
	private final static short CONF_LITTLE		= 0x10;
	private final static short CONF_ALIGNMASK	= 0x60;
	private final static short 	CONF_ALIGN_1	= 0x00;
	private final static short 	CONF_ALIGN_2	= 0x20;
	private final static short 	CONF_ALIGN_4	= 0x40;
	private final static short 	CONF_ALIGN_8	= 0x60;
	private final static short CONF_NORELOCS 	= 0x80;


	/*
	 * since we have different sized integers based on the config byte, we need
	 * to deal with that.  endianness is handled by the reader.
	 */
	private int getint() throws IOException {
		int retval;
		
		if (intsize == 32) {
			retval = reader.readNextInt() & 0xffffffff;
		} else {
			retval = reader.readNextShort() & 0xffff;
		}
		return retval;
	}

	private int getbyte() throws IOException {
		int retval;
		retval = reader.readNextByte() & 0xff;
		return retval;
	}
	
	/*
	 * make me a header from the data in the file
	 */
	private class header {
		int w_magic;		// 0x99
		int w_conf;			// I have files with 0x14 or 0x94
		int w_symbol;		// size of symbol table
		int w_text;			// size of text segment
		int w_data;			// size of data segment
		int w_bss;			// size of bss (not in file)
		int w_heap;			// size of heap/stack (not in file)
		int w_textoff;		// address of text in memory
		int w_dataoff;		// address of data in memory

		header(ByteProvider provider) throws IOException {
			reader = new BinaryReader(provider, true);

			w_magic = getbyte();
			w_conf = getbyte();

			ness = ((w_conf & CONF_LITTLE) != 0) ? Endian.LITTLE : Endian.BIG;
			intsize = ((w_conf & CONF_INT_4) != 0) ? 32 : 16;
			switch (w_conf & CONF_SYM_MASK) {
			case CONF_SYM_1:	symbolsize = 1; break;
			case CONF_SYM_3:	symbolsize = 3; break; 
			case CONF_SYM_5:	symbolsize = 5; break;
			case CONF_SYM_7:	symbolsize = 7; break;
			case CONF_SYM_9:	symbolsize = 9; break;
			case CONF_SYM_11:	symbolsize = 11; break;
			case CONF_SYM_13:	symbolsize = 13; break;
			case CONF_SYM_15:	symbolsize = 15; break;
			}
			reader.setLittleEndian(!ness.isBigEndian());

			w_symbol = reader.readNextShort() & 0xffff;
			w_text = getint();
			w_data = getint();
			w_bss = getint();
			w_heap = getint();
			w_textoff = getint();
			w_dataoff = getint();
			file_textoff = reader.getPointerIndex();
			file_dataoff = file_textoff + w_text;
			file_symoff = file_dataoff + w_data;
		}
	}
	
	private final static byte SYM_SEGMASK	= 0x07;
	private final static byte SYM_UNDEF 	= 0x00;
	private final static byte SYM_ABSOLUTE	= 0x04;
	private final static byte SYM_TEXT		= 0x05;
	private final static byte SYM_DATA		= 0x06;
	private final static byte SYM_BSS		= 0x07;
	private final static byte SYM_GLOBAL	= 0x08;
	
	private class symbol {
		int value;
		byte flag;
		String name;
		
		symbol() throws IOException {
			value = getint();
			flag = reader.readNextByte();
			name = reader.readNextAsciiString(symbolsize);
		}
	}

	/*
	 * whitesmith's relocation entries are variable length: 1, 2 or 3 bytes
	 * relocation control bytes take the following values:
	 * 0 :      end of relocs
	 * 1 - 31 : skip 1 - 31 bytes
	 * 32 - 63 :    skip 0 to 31 pages, plus the next byte
	 * 64 :     unused
	 * 68 :     text offset
	 * 72 :     data offset
	 * 76 :     bss offset
	 * 80 - 248 :   symbol table entry 0 - 42
	 * 252 :    symbol table 43 and beyond read next byte
	 *     0 - 127   symbol table entries 43 - 170
	 *     128-256   symbol table entries 256 * (n - 128) + 175 + next byte
	 */
	
	private final static short RELOC_STOP 			= 0;		// end of relocations
	private final static short RELOC_SKIP_MIN 		= 1;		// skip N bytes
	private final static short RELOC_SKIP_MAX 		= 31;		// 
	private final static short RELOC_CHAIN_MIN		= 32;		// skip 32 + (256 * (N - 32))
	private final static short RELOC_CHAIN_MAX		= 63;		// 	plus next byte

	private final static short RELOC_SEGMENT_INT		= 0x1;
	private final static short RELOC_SEGMENT_LONG		= 0x2;

	private final static short RELOC_NONE			= 16;
	private final static short RELOC_TEXT			= 17;
	private final static short RELOC_DATA			= 18;
	private final static short RELOC_BSS			= 19;
	private final static short RELOC_SYM_MIN		= 20;
	private final static short RELOC_SYM_MAX		= 46;
	private final static short RELOC_SYM_EXTEND		= 47;
	private final static short RELOC_EXTEND_1		= 128;
	
	private final static short REL_SIZEMASK			= 0x3;
	private final static short REL_OFF2				= 0x1;		// relocate 2 bytes
	private final static short REL_OFF4				= 0x2;		// relocate 4 bytes
	
	private final static short 	RT_END				= 0;
	private final static short	RT_BIAS				= 1;		// not sure what load bias means in doc
	private final static short 	RT_SEG_TEXT			= 2;
	private final static short 	RT_SEG_DATA			= 3;
	private final static short 	RT_SEG_BSS			= 4;

	/*
	 * read a relocation from the input stream and return it.
	 * it advances the stream.  the first time you call it, you
	private class relocation {
		int offset;
		int type;
		boolean is_4byte;
		symbol symbol;
		int location = 0;

		void reset()
		{
			reader.setPointerIndex(file_relocoff);
			location = header.w_textoff;
		}
		
		relocation() throws IOException {
			int control;
			int size;
			
			control = reader.readNextByte();

			while (true) {
				if (control == RELOC_STOP) {
					type = RT_END;
					return;
				}
				if ((control >= RELOC_SKIP_MIN) && (control <= RELOC_SKIP_MAX)) {
					location += control;
					continue;
				}
				if ((control >= RELOC_CHAIN_MIN) && (control <= RELOC_CHAIN_MAX)) {
					location += ((control - 32) * 256) + 32 + reader.readNextByte();
					continue;
				}
				control -= 64;

				size = control & REL_SIZEMASK;
				control = (control >> 2) - 16;
				
				offset = location;
				is_4byte = (size & REL_OFF4) == REL_OFF4;

				switch (control) {
				case 0:
					type = RT_BIAS;
					symbol = null;
					break;
				case 1:
					type = RT_SEG_TEXT;
					symbol = null;
					break;
				case 2:
					type = RT_SEG_DATA;
					symbol = null;
					break;
				case 3:
					type = RT_SEG_BSS;
					symbol = null;
					break;
				case RELOC_SYM_EXTEND:
					control = reader.readNextByte();
					if (control < RELOC_EXTEND_1) {
						control += RELOC_SYM_EXTEND;
					} else {
						control = ((control - 128) * 256) + 175 + reader.readNextByte();
					}
					// fall through
				default:
					symbol = lookupsymbol(control);
					type = RT_BIAS;
				}
				return;
			}
		}
	}
	 */
	
	@Override
	public String getName() {
		return "whitesmith";
	}

	@Override
	public Collection<LoadSpec> findSupportedLoadSpecs(ByteProvider provider) throws IOException {
		List<LoadSpec> loadSpecs = new ArrayList<>();

		header = new header(provider);
		
		// make this a loader for everybody that matches things in the header we read
		if (header.w_magic == MAGIC) {
			List<LanguageDescription> languageDescriptions =
				getLanguageService().getLanguageDescriptions(false);
			for (LanguageDescription languageDescription : languageDescriptions) {
				if (languageDescription.getEndian() != ness)
					continue;
				if (languageDescription.getSize() != intsize)
					continue;
				Collection<CompilerSpecDescription> compilerSpecDescriptions =
					languageDescription.getCompatibleCompilerSpecDescriptions();
				for (CompilerSpecDescription compilerSpecDescription : compilerSpecDescriptions) {
					LanguageCompilerSpecPair lcs =
						new LanguageCompilerSpecPair(languageDescription.getLanguageID(),
							compilerSpecDescription.getCompilerSpecID());
					loadSpecs.add(new LoadSpec(this, header.w_textoff, lcs, false));
				}
			}
		}
		return loadSpecs;
	}

	@Override
	protected void load(ByteProvider provider, LoadSpec loadSpec, List<Option> options,
			Program program, MemoryConflictHandler handler, TaskMonitor monitor, MessageLog log)
			throws CancelledException, IOException {
		AddressSpace space = program.getAddressFactory().getDefaultAddressSpace();
		SymbolTable stab = program.getSymbolTable();
		Memory memory = program.getMemory();
		reader = new BinaryReader(provider, true);
		Address addr;
		
		// make some memory sections
		try {
			if (header.w_textoff > 0) {
				low = memory.createInitializedBlock("low", space.getAddress(0), 
						header.w_textoff, (byte)0, monitor, false);
			}
			code = memory.createInitializedBlock("text", space.getAddress(header.w_textoff), 
					header.w_text, (byte)0, monitor, false);
			data = memory.createInitializedBlock("data", space.getAddress(header.w_dataoff), 
					header.w_data, (byte)0, monitor, false);
			if (header.w_bss > 0) {
				bss = memory.createInitializedBlock("bss", space.getAddress(header.w_dataoff + header.w_data), 
						header.w_text, (byte)0, monitor, false);
			}
		} catch (LockException | DuplicateNameException | MemoryConflictException | AddressOverflowException
				| AddressOutOfBoundsException e) {
			e.printStackTrace();
		}

		// snarf the code and data from the file into the memory we just created
		try {
			reader.setPointerIndex(file_textoff);
			for (addr = code.getStart(); addr.getOffset() < header.w_textoff + header.w_text; addr = addr.next()) {
					code.putByte(addr, reader.readNextByte());
			}
			reader.setPointerIndex(file_dataoff);
			for (addr = data.getStart(); addr.getOffset() < header.w_dataoff + header.w_data; addr = addr.next()) {
				data.putByte(addr, reader.readNextByte());
			}
		} catch (MemoryAccessException e) {
			e.printStackTrace();
		}

		// now, let's load the symbols
		reader.setPointerIndex(file_symoff);
		symbols = new symbol[header.w_symbol / symbolsize];

		try {
			for (int i = 0; i < symbols.length; i++) {
				symbols[i] = new symbol();
				stab.createLabel(space.getAddress(symbols[i].value), symbols[i].name, SourceType.IMPORTED);
			}
		} catch (InvalidInputException | AddressOutOfBoundsException e) {
			e.printStackTrace();
		}
		//  TODO: then do the relocations
	}

	@Override
	public List<Option> getDefaultOptions(ByteProvider provider, LoadSpec loadSpec,
			DomainObject domainObject, boolean isLoadIntoProgram) {
		List<Option> list =
			super.getDefaultOptions(provider, loadSpec, domainObject, isLoadIntoProgram);

		// TODO: If this loader has custom options, add them to 'list'
		list.add(new Option("Option name goes here", "Default option value goes here"));

		return list;
	}

	@Override
	public String validateOptions(ByteProvider provider, LoadSpec loadSpec, List<Option> options) {

		// TODO: If this loader has custom options, validate them here.  Not all options require
		// validation.

		return super.validateOptions(provider, loadSpec, options);
	}
}
