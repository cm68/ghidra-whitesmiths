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
package whitesmith80;

import java.io.IOException;
import java.util.*;

import ghidra.app.util.Option;
import ghidra.app.util.bin.BinaryReader;
import ghidra.app.util.bin.ByteProvider;
import ghidra.app.util.importer.MessageLog;
import ghidra.app.util.opinion.AbstractLibrarySupportLoader;
import ghidra.app.util.opinion.LoadSpec;
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
 * the whitesmith's c defined a quirky object file format that had some 
 * flexibility:
 * <p>
 * it supported 16 and 32 bit integers in little and big endian, 
 * and 1 to 15 byte symbol lengths <br>
 * there were 4 segments, of which 3 were meaningful in the object file: 
 * text, data, and bss <br>
 * <p>
 * this is coded to deal with all options, but I've only got sample files 
 * with 1 flavor: <br>
 * 		2 byte integers, 1 byte alignment, little endian, 9 character symbols
 * <p>
 * presumably, this loader would work with Idris binaries, as well as
 * morrow micronix and CP/M.
 * 
 * support added to deal with unlinked binary files like libraries.   to make
 * this work, a segment is created for external undefined symbols and fixup
 * is done using these bogus addresses.
 * 
 * no real support for the 4 byte integer, big endian, etc options is here, but
 * can be somewhat easily added.
 * 
 * @author curt@zen-room.org
 */
public class whitesmith80Loader extends AbstractLibrarySupportLoader {

	private MessageLog log;
	private BinaryReader reader;
	// private MemoryBlock low;
	private MemoryBlock code;
	private MemoryBlock data;
	private MemoryBlock bss;
	private MemoryBlock undefined;

	private long file_textoff;			// file offsets of each chunk
	private long file_dataoff;
	private long file_symoff;
	private long file_relocoff;
	
	private	int symbolsize;				// the size of a symbol name in file
	private Endian ness;
	private int intsize;
	private int location;

	private header header;
	private symbol[] symbols;
	private ArrayList<relocation> relocs;
	
	private final static short MAGIC 			= 0x99;
	private final static short CONF_SYM_MASK 	= 0x07;		// symname is ((conf & 7) * 2) + 1
	private final static short CONF_INT_4 		= 0x08;		// 4 byte integers
	private final static short CONF_LITTLE		= 0x10;		// little endian
	private final static short CONF_ALIGNMASK	= 0x60;		// alignment is 1 << ((conf >> 5) & 3)
	private final static short CONF_NORELOCS 	= 0x80;		// no relocs present
	
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
	 * also, if we have a buck-naked code signature, we fake up a header.
	 * this is when we have a byte string that looks like:
	 * 0xc1 0x21 0x00 0x00 0x39 0xe5 0xc5
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
		byte[] w_code;		// to check for naked signature
		int main;			// the real entry point
		
		private final byte[] signature = {
				(byte)0xc1, 0x21, 0x00, 0x00, 0x39, (byte)0xe5, (byte)0xc5, (byte)0xcd
		};
		
		header(ByteProvider provider) throws IOException {
			reader = new BinaryReader(provider, true);
			w_magic = getbyte();
			if (w_magic == 0xc1) {
				int i;
				w_code = new byte[8];
				w_code[0] = (byte)w_magic;
				for (i = 1; i < 8; i++) {
					w_code[i] = (byte)getbyte();
				}
				if (Arrays.equals(w_code, signature)) {
					w_magic = 0x99;
					w_conf = 0x94;
					w_symbol = 0;
					w_text = (int) reader.length();
					w_data = 0;
					w_bss = 0;
					w_heap = 0;
					w_textoff = 0x100;
					w_dataoff = 0;
					intsize = 16;
					ness = Endian.LITTLE;
					symbolsize = 9;
					reader.setLittleEndian(true);
					file_textoff = 0;
					file_dataoff = 0;
					file_symoff = 0;
					file_relocoff = 0;
					main = getint();
				}
				return;
			}
			w_conf = getbyte();

			ness = ((w_conf & CONF_LITTLE) != 0) ? Endian.LITTLE : Endian.BIG;
			intsize = ((w_conf & CONF_INT_4) != 0) ? 32 : 16;
			symbolsize = ((w_conf & CONF_SYM_MASK) * 2) + 1;
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
			if ((w_conf & CONF_NORELOCS) == 0) {
				file_relocoff = file_symoff + w_symbol;
			} else {
				file_relocoff = 0;
			}
		}
	}
	
	private final static byte SYM_SEGMASK	= 0x03;
	private final static byte SYM_ABSOLUTE	= 0x00;
	private final static byte SYM_TEXT		= 0x01;
	private final static byte SYM_DATA		= 0x02;
	private final static byte SYM_BSS		= 0x03;
	private final static byte SYM_DEFINED	= 0x04;
	private final static byte SYM_GLOBAL	= 0x08;
	
	String[] sseg = { "absolute", "text", "data", "bss" };
	
	private class symbol {
		int value;
		byte flag;
		String name;
		
		void dump()
		{
			log.appendMsg("symbol: " + name + 
					" flag: " + String.format("0x%02x ", flag) + 
					sseg[flag & SYM_SEGMASK] +
					(((flag & SYM_DEFINED) != 0) ? " defined" : " undefined") +
					(((flag & SYM_GLOBAL) != 0) ? " global" : " local") +
					" value: " + String.format("0x%04x", value));
		}
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

	// control bytes > = 64 have the low 2 bits encoding bias and length
	private final static short RELOC_BIAS			= 0x1;
	private final static short RELOC_LONG			= 0x2;

	private final static short RELOC_NONE			= 0;
	private final static short RELOC_TEXT			= 1;
	private final static short RELOC_DATA			= 2;
	private final static short RELOC_BSS			= 3;

	private enum rtype { END, BIAS, TEXT, DATA, BSS, SYMBOL }
	
	/*
	 * read a relocation from the input stream and return it.
	 * it advances the stream. RT_END marks the end of the reloc stream.
	 */
	private class relocation {
		MemoryBlock segment;
		rtype type;
		int offset;		// address of relocation 
		int size;		// size of relocation - should be 2 for micronix
		int bias;		// never seen this
		symbol symbol;

		void dump()
		{
			log.appendMsg(
					"reloc:" + segment.getName() + String.format("0x%04x",offset) + 
					" " + type +
					" len: " + size + " " +
					" bias: " + bias + " " +
					((symbol == null) ? "<null>" : symbol.name));
		}


		pwdrelocation(MemoryBlock seg) throws IOException {
			segment = seg;
			type = rtype.END;
			
			while (reader.hasNext(1)) {
				int control = getbyte();

				// this terminates the relocations
				if (control == 0) {
					return;
				}

				if ((control >= 1) && (control <= 31)) {		// short skips
					location += control;
					continue;
				}

				if ((control >= 32) && (control <= 63)) {		// long skips
					location += 32 + ((control - 32) * 256) + getbyte();
					continue;
				}

				size = ((control & 0x2) == 0) ? 2 : 4;
				bias = ((control & 0x1) == 0) ? 0 : 1;
				offset = location;
				
				control -= 64;
				control >>= 2;
				
				switch (control) {
				case 0:
					type = rtype.BIAS;
					location += size;
					symbol = null;
					return;
				case 1:
					type = rtype.TEXT;
					location += size;
					symbol = null;
					return;
				case 2:
					type = rtype.DATA;
					location += size;
					symbol = null;
					return;
				case 3:
					type = rtype.BSS;
					location += size;
					symbol = null;
					return;
				default:
					break;
				}
				control -= 4;
				
				if (control == 47) {
					control = getbyte();
					if (control < 128) {
						control += 128;
					} else {
						control = ((control - 128) * 256) + 175 + getbyte();
					}
				}
				type = rtype.SYMBOL;
				location += size;
				symbol = symbols[control];
				return;
			}
		}
	}

	void
	addrelocs(MemoryBlock seg) throws IOException {
		relocation g;
		
		while (((g = new relocation(seg)).type) != rtype.END) {
			g.dump();
			relocs.add(g);
		}
	}
	
	@Override
	public String getName() {
		return "micronix";
	}

	@Override
	public Collection<LoadSpec> findSupportedLoadSpecs(ByteProvider provider) 
		throws IOException {
		List<LoadSpec> loadSpecs = new ArrayList<>();

		header = new header(provider);
		
		// make this a loader for everybody that matches the header we read
		if (header.w_magic == MAGIC) {
			List<LanguageDescription> languageDescriptions =
				getLanguageService().getLanguageDescriptions(false);
			for (LanguageDescription languageDescription : languageDescriptions) {
				if (languageDescription.getEndian() != ness)
					continue;
				if (languageDescription.getSize() != intsize)
					continue;
				if (!languageDescription.getProcessor().toString().equalsIgnoreCase("z80"))
					continue;
				if (!languageDescription.getVariant().equalsIgnoreCase("default"))
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
	protected void load(ByteProvider provider, LoadSpec loadSpec, 
		List<Option> options, Program program, TaskMonitor monitor, 
		MessageLog mlog)
			throws CancelledException, IOException {
		AddressSpace space = 
			program.getAddressFactory().getDefaultAddressSpace();
		SymbolTable stab = program.getSymbolTable();
		Memory memory = program.getMemory();
		reader = new BinaryReader(provider, true);
		Address addr;
		int undef = 0;
		log = mlog;

		// make some memory sections
		// XXX - fixme.  upm has data at 0x100, and text high
		// feels like a fencepost error
		
		try {
			/* if (header.w_textoff > 0) {
				low = memory.createInitializedBlock("low", space.getAddress(0), 
						header.w_textoff, (byte)0, monitor, false);
			}
			*/
			if (header.w_text > 0) {
				code = memory.createInitializedBlock("text", 
					space.getAddress(header.w_textoff), 
					header.w_text, (byte)0, monitor, false);
			}
			if (header.w_data > 0) {
				data = memory.createInitializedBlock("data", 
					space.getAddress(header.w_dataoff), 
					header.w_data, (byte)0, monitor, false);
			}
			if (header.w_bss > 0) {
				bss = memory.createInitializedBlock("bss",
						space.getAddress(header.w_dataoff + header.w_data), 
					header.w_text, (byte)0, monitor, false);
			}
		} catch (LockException
				| MemoryConflictException | AddressOverflowException
				| AddressOutOfBoundsException e) {
			e.printStackTrace();
		}

		// snarf the code and data from the file into the memory we just created
		try {
			reader.setPointerIndex(file_textoff);
			if (header.w_text > 0) {
				for (addr = code.getStart(); 
					addr.getOffset() < header.w_textoff + header.w_text; 
					addr = addr.next()) {
					code.putByte(addr, reader.readNextByte());
				}
			}
			if (header.w_data > 0) {
				reader.setPointerIndex(file_dataoff);
				for (addr = data.getStart(); 
					addr.getOffset() < header.w_dataoff + header.w_data; 
					addr = addr.next()) {
					data.putByte(addr, reader.readNextByte());
				}
			}
		} catch (MemoryAccessException e) {
			e.printStackTrace();
		}

		/*
		 * now, let's load the symbols, if any
		 */
		if (header.w_symbol != 0) {
			reader.setPointerIndex(file_symoff);
			symbols = new symbol[header.w_symbol / (symbolsize + 3)];

			try {
				for (int i = 0; i < symbols.length; i++) {
					symbol s = new symbol();
					s.dump();
					symbols[i] = s;
					
					if ((s.flag & SYM_DEFINED) == SYM_DEFINED) {
						addr = space.getAddress(s.value);
						stab.createLabel(addr, s.name, SourceType.IMPORTED);
						if ((s.flag & SYM_SEGMASK) == SYM_TEXT) {
							stab.addExternalEntryPoint(addr);
						}
					} else {
						undef++;
					}
				}
			} catch (InvalidInputException | AddressOutOfBoundsException e) {
				e.printStackTrace();
			}

			/*
			 * if there are any undefined symbols, make a special memory segment for them
			 */
			if (undef > 0) {
				int undef_off = header.w_dataoff + header.w_data + header.w_bss;
				
				try {
					undefined = memory.createUninitializedBlock("undefined", 
							space.getAddress(undef_off), undef * 2, false);
				} catch (LockException
					| MemoryConflictException | AddressOverflowException e) {
					e.printStackTrace();
				}
				try {
					for (int i = 0; i < symbols.length; i++) {
						symbol s = symbols[i];
						if ((s.flag & SYM_DEFINED) == 0) {
							s.value = undef_off + (i * 2);
							addr = space.getAddress(s.value);
							stab.createLabel(addr, s.name, SourceType.IMPORTED);
						}
					}
				} catch (InvalidInputException | AddressOutOfBoundsException e) {
					e.printStackTrace();
				}
			}
		}

		/*
		 * then do the relocations, if any
		 */
		if (file_relocoff != 0) {
			reader.setPointerIndex(file_relocoff);
			relocs = new ArrayList<relocation>();

			addrelocs(code);			
			addrelocs(data);
			
			try {
				for (relocation r : relocs) {
					addr = space.getAddress(r.offset);
					switch (r.type) {
					case END:
						break;
					case SYMBOL:
						program.getMemory().setShort(addr, (short) r.symbol.value);
						break;
					case BIAS:
					case TEXT:
					case DATA:
					case BSS:
						break;
					}
				}
			} catch (MemoryAccessException e) {
					e.printStackTrace();
			}
		}

		/*
		 * we'll deal with the special case of a stripped binary by sticking an entry point at textoff, usually 0x100
		 */
		if (header.w_symbol == 0 && header.w_textoff == 0x100) {
			addr = space.getAddress(header.main);
			Address entryaddr = space.getAddress(header.w_textoff);
			try {
				stab.createLabel(entryaddr, "entry", SourceType.IMPORTED);
				stab.createLabel(addr, "_main", SourceType.IMPORTED);
			} catch (InvalidInputException e) {
				e.printStackTrace();
			}
			stab.addExternalEntryPoint(addr);
			stab.addExternalEntryPoint(entryaddr);
		}
	}

	@Override
	public List<Option> getDefaultOptions(ByteProvider provider, LoadSpec loadSpec,
			DomainObject domainObject, boolean isLoadIntoProgram) {
		List<Option> list =
			super.getDefaultOptions(provider, loadSpec, domainObject, isLoadIntoProgram);

		// TODO: If this loader has custom options, add them to 'list'
		// list.add(new Option("Option name goes here", "Default option value goes here"));

		return list;
	}

	@Override
	public String validateOptions(ByteProvider provider, LoadSpec loadSpec, List<Option> options, Program program) {

		// TODO: If this loader has custom options, validate them here.  Not all options require
		// validation.

		return super.validateOptions(provider, loadSpec, options, program);
	}
}
