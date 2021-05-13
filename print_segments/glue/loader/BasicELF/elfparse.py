from construct import Array
from . import elfstructs

#The parsing of the ELF with the specific sized structs
class ELFParse:
    def __init__(self, elf_structs, data):
        self.ehdr = elf_structs.Elf_ehdr.parse(data)
        self.phdr_table = Array(self.ehdr.e_phnum, elf_structs.Elf_phdr) \
                .parse(data[self.ehdr.e_phoff:])
        self.shdr_table = Array(self.ehdr.e_shnum, elf_structs.Elf_shdr) \
                .parse(data[self.ehdr.e_shoff:])

class ELFStructs:
    def __init__(self, ehdr=None, phdr=None, shdr=None):
        self.Elf_ehdr = ehdr
        self.Elf_phdr = phdr
        self.Elf_shdr = shdr

elf_32 = ELFStructs(
        elfstructs.Elf32_Ehdr,
        elfstructs.Elf32_Phdr,
        elfstructs.Elf32_Shdr)
elf_64 = ELFStructs(
        elfstructs.Elf64_Ehdr,
        elfstructs.Elf64_Phdr,
        elfstructs.Elf64_Shdr)





