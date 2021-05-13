#!/usr/bin/env python3

#from ELFPatch.ELFPatch.BasicELF import BasicELF
#from ELFPatch.ELFPatch.BasicELF.constants import *
#from ELFPatch.ELFPatch.chunk_manager import ChunkManager

from loader.BasicELF import BasicELF
from loader.BasicELF.constants import *
from loader.chunk_manager import ChunkManager
import struct
import sys
from recordclass import recordclass
from bitstruct import unpack, pack


class Patch:
    def __init__(self, vaddr, data):
        self.vaddr = vaddr
        self.data = data

class CFIRewriter(BasicELF):
    def __init__(self, ELFFile):
        super().__init__(ELFFile)
        self._chunks = []
        self._patches = []

    def _translate_flags(self, flags):
        new_flags = 0
        if 'r' in flags or "R" in flags:
            new_flags |= PT_R
        if 'w' in flags or "W" in flags:
            new_flags |= PT_W
        if 'x' in flags or "X" in flags:
            new_flags |= PT_X
        
        return new_flags

    def new_chunk(self, size=None, content=b"", flags='rwx'):
        if size is None:
            size = len(content)

        flags = self._translate_flags(flags)

        for chunk in self._chunks:
            # Do a try catch because Chunk manager creates exceptions when sizes
            # or flags don't match
            try:
                new_chunk = chunk.new_chunk(size=size, flags=flags, content=content)
                # If no exception, then succeded, return
                return new_chunk
            # error in adding chunk, pass
            except Exception as e:
                # print(e)
                pass

        # No chunks could satisfy the request. Page aligned size so we can use
        # it wisely for future chunks too and do not end up wasting virtual
        # address space
        poff = (self._generate_physical_offset() & 0xfff)
        aligned = (size + 0xfff + poff) & -0x1000
        aligned -= poff
        print("rawelf length is ", hex(len(self.rawelf)))
        new_segment = self.new_segment(size=aligned, flags=flags, virtual_address=len(self.rawelf))

        managed_chunk = ChunkManager(new_segment)
        self._chunks.append(managed_chunk)
        
        return managed_chunk.new_chunk(size=size, content=content, flags=flags) 

    def do_cfi(self, vaddr, size, newtable, newtext):
        # TODO: fill gaps between 
        print('CFI on {:08x},+{:08x}'.format(vaddr, size))

        # Places a guard segment between our actual code and our CFI code
        #self.new_segment(size=0, msize=0x8000, physical_off=0, flags=PT_R|PT_W)

        olddata = self.read(vaddr, size)

        insns = [x[0] for x in struct.iter_unpack('<I', olddata)]
        insns.append(0)

        # Get new code / table
        code_sz = sum(4 for c in newtext)
        chnk = self.new_chunk(size=code_sz, flags='rx')

        newbase = len(self.rawelf)

        # Patch old code with table and insert new code
        #self._patches.append(Patch(vaddr, struct.pack('<' + 'i' * len(tbl), *tbl)))
        print("The vaddr is ", hex(vaddr))
        self._patches.append(Patch(vaddr, bytearray(newtable))) 
        #print("The type is ", type(self.rawelf))
        #print("The cool type is ", type(newtable))
        #print("The very cool type is ", type(bytearray(newtable)))
        chnk.content = bytearray(newtext)
        #print("The type is ", type(chnk.content))
        #print("The cool type is ", type(newtext))
        #print("The very cool type is ", type(bytearray(newtext)))
        return 

    def _update_raw_elf(self):
        #Call the original update to get the segments added
        super()._update_raw_elf()

        for patch in self._patches:
            #off = self.virtual_to_physical(patch.vaddr)

            print("virt to physical of vaddr says ", hex(self.virtual_to_physical(patch.vaddr)))
            print("vaddr in update says ", hex(patch.vaddr))
            off = patch.vaddr
            self.rawelf[off:off+len(patch.data)] = patch.data

if __name__ == "__main__":
    if len(sys.argv) < 5:
        print("Usage: ./glue.py <original_binary_file> <table_file> <text_file> <entrypoint>")
        exit(-1)

    original_binary_file = sys.argv[1]
    with open(sys.argv[2], "rb") as table_file:
        newtable = table_file.read()
    with open(sys.argv[3], "rb") as text_file:
        newtext = text_file.read()
    entrypoint = int(sys.argv[4], 0) # use 0 to parse hex automatically if prepended with '0x'

    elf_file = CFIRewriter(original_binary_file)
    base = -1
    size = 0
    for hdr in elf_file.elf.shdr_table:
        if hdr.sh_type == SHT_PROGBITS and hdr.sh_flags & SHF_EXECINSTR:
            #print(hdr)
            if not size: base = hdr.sh_addr
            if base + size != hdr.sh_addr:
                raise ValueError('Not contiguous exec section')
            size += hdr.sh_size
    elf_file.do_cfi(base, size, newtable, newtext) 

    # change the entry point of the program
    elf_file.elf.ehdr.e_entry = entrypoint

    # Places a guard segment between our actual code and our CFI code
    #elf_file.new_segment(size=0, msize=0x8000, physical_off=0, flags=PT_R|PT_W)

    # calls _update_raw_elf()
    elf_file.write_file(original_binary_file + '.patched')

