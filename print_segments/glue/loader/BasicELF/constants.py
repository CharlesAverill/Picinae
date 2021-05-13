PT_NULL =    0
PT_LOAD =    1
PT_DYNAMIC = 2
PT_INTERP =  3
PT_NOTE =    4
PT_SHLIB =   5
PT_PHDR =    6
PT_TLS =     7     
PT_LOOS =    0x60000000  
PT_HIOS =    0x6fffffff 
PT_LOPROC =  0x70000000
PT_HIPROC =  0x7fffffff
PT_GNU_EH_FRAME	= 0x6474e550
PT_GNU_STACK = PT_LOOS + 0x474e551

PT_X = 0x1
PT_W = 0x2
PT_R = 0x4

# Valid section types
SHT_NULL =       0
SHT_PROGBITS =   1
SHT_SYMTAB =     2
SHT_STRTAB =     3
SHT_RELA =       4
SHT_HASH =       5
SHT_DYNAMIC =    6
SHT_NOTE =       7
SHT_NOBITS =     8
SHT_REL =        9
SHT_SHLIB =      10
SHT_DYNSYM =     11
SHT_INIT_ARRAY = 14
SHT_FINI_ARRAY = 15
SHT_PREINIT_ARRAY = 16
SHT_GROUP =      17
SHT_SYMTAB_SHNDX = 18
SHT_NUM =        19

# Valid section flags
SHF_WRITE =      (1 << 0)
SHF_ALLOC =      (1 << 1)
SHF_EXECINSTR =  (1 << 2)
SHF_MERGE =      (1 << 4)
SHF_STRINGS =    (1 << 5)
SHF_INFO_LINK =  (1 << 6)
SHF_LINK_ORDER = (1 << 7)
SHF_OS_NONCONFORMING = (1 << 8)
SHF_GROUP =      (1 << 9)
SHF_TLS =        (1 << 10)
SHF_COMPRESSED = (1 << 11)
SHF_ORDERED =    (1 << 30)
SHF_EXCLUDE =    (1 << 31)
