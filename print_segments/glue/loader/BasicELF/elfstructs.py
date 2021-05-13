from construct import *

#32 bit ELF struct type definitions
Elf32_Addr = Int32ul
Elf32_Half = Int16ul
Elf32_Off = Int32ul
Elf32_Sword = Int32sl
Elf32_Word = Int32ul

#64 bit ELF struct definitions
Elf64_Addr = Int64ul
Elf64_Half = Int16ul
Elf64_SHalf = Int16sl
Elf64_Off = Int64ul
Elf64_Sword = Int32sl
Elf64_Word = Int32ul
Elf64_Xword = Int64ul
Elf64_Sxword = Int64sl

#32 bit header struct
Elf32_Ehdr = Struct(
        'e_ident' / Struct(
            "MAGIC"/Const(b"\x7fELF"), #ELF Header
            'EI_CLASS'/ Int8ul,
            "OTHER_STUFF"/ Array(11, Int8ul)
            ),
        'e_type' / Elf32_Half,
        'e_machine' / Elf32_Half,
        'e_version' / Elf32_Word,
        'e_entry' / Elf32_Addr,  
        'e_phoff' / Elf32_Off,
        'e_shoff' / Elf32_Off,
        'e_flags' / Elf32_Word,
        'e_ehsize' / Elf32_Half,
        'e_phentsize' / Elf32_Half,
        'e_phnum' / Elf32_Half,
        'e_shentsize' / Elf32_Half,
        'e_shnum' / Elf32_Half,
        'e_shstrndx' / Elf32_Half
        )
#32 bit Segment (program) header struct
Elf32_Phdr = Struct(
        'p_type' / Elf32_Word,
        'p_offset' / Elf32_Off,
        'p_vaddr' / Elf32_Addr,
        'p_paddr' / Elf32_Addr,
        'p_filesz' / Elf32_Word,
        'p_memsz' / Elf32_Word,
        'p_flags' / Elf32_Word,
        'p_align' / Elf32_Word
        )

Elf32_Shdr = Struct(
        'sh_name' / Elf32_Word, 
        'sh_type' / Elf32_Word, 
        'sh_flags' / Elf32_Word, 
        'sh_addr' / Elf32_Addr, 
        'sh_offset' / Elf32_Off, 
        'sh_size' / Elf32_Word, 
        'sh_link' / Elf32_Word, 
        'sh_info' / Elf32_Word, 
        'sh_addralign' / Elf32_Word, 
        'sh_entsize' / Elf32_Word, 
        )

Elf64_Ehdr = Struct(
        'e_ident' / Struct(
            "MAGIC"/Const(b"\x7fELF"), #ELF Header
            'EI_CLASS'/ Int8ul,
            "OTHER_STUFF"/ Array(11, Int8ul)
            ),
        'e_type' / Elf64_Half,
        'e_machine' / Elf64_Half,
        'e_version' / Elf64_Word,
        'e_entry' / Elf64_Addr,
        'e_phoff' / Elf64_Off,	
        'e_shoff' / Elf64_Off,	
        'e_flags' / Elf64_Word,
        'e_ehsize' / Elf64_Half,
        'e_phentsize' / Elf64_Half,
        'e_phnum' / Elf64_Half,
        'e_shentsize' / Elf64_Half,
        'e_shnum' / Elf64_Half,
        'e_shstrndx' / Elf64_Half
        )


Elf64_Phdr = Struct(
        'p_type' / Elf64_Word,
        'p_flags' / Elf64_Word,
        'p_offset' / Elf64_Off,
        'p_vaddr' / Elf64_Addr,
        'p_paddr' / Elf64_Addr,
        'p_filesz' / Elf64_Xword,
        'p_memsz' / Elf64_Xword,
        'p_align' / Elf64_Xword
        )


Elf64_Shdr = Struct(
        'sh_name' / Elf64_Word,
        'sh_type' / Elf64_Word,
        'sh_flags' / Elf64_Xword,
        'sh_addr' / Elf64_Addr,
        'sh_offset' / Elf64_Off,
        'sh_size' / Elf64_Xword,
        'sh_link' / Elf64_Word,
        'sh_info' / Elf64_Word,
        'sh_addralign' / Elf64_Xword,
        'sh_entsize' / Elf64_Xword,
        )
