#!/usr/bin/env python3
# Grok Bot (agent coqettu): generate proofs for musl's branch-free ctype range tests.
import sys
FUNS = {
 # name: (ghidra entry, lo, k, C body, man text)
 'isdigit': (0x11ee64, 0x30, 9,  "return (unsigned)c-'0' < 10;", "isdigit()\n                   checks for a digit (0 through 9)."),
 'isupper': (0x11ef00, 0x41, 25, "return (unsigned)c-'A' < 26;", "isupper()\n                   checks for an uppercase letter."),
 'islower': (0x11ee8c, 0x61, 25, "return (unsigned)c-'a' < 26;", "islower()\n                   checks for a lowercase character."),
 'isprint': (0x11eea0, 0x20, 0x5e, "return (unsigned)c-0x20 < 0x5f;", "isprint()\n                   checks for any printable character including space."),
 'isgraph': (0x11ee78, 0x21, 0x5d, "return (unsigned)c-0x21 < 0x5e;", "isgraph()\n                   checks for any printable character except space."),
 'isascii': (0x11ee30, 0, 0x7f, "return !(c&~0x7f);", "isascii()\n                   checks whether c is a 7-bit unsigned char value that fits\n                   into the ASCII character set."),
}
TEMPLATE = open('tools/ctype_template.v').read()
for name in sys.argv[1:]:
    entry, lo, k, body, man = FUNS[name]
    s = TEMPLATE
    asm = ('cmp w0,#k; cset w0,ls; ret' if lo == 0 else 'sub w0,w0,#lo; cmp w0,#k; cset w0,ls; ret')
    s = s.replace('@ASM@', asm)
    for a, b in [('@NAME@', name), ('@ENTRY@', hex(entry)), ('@RET@', hex(entry + (8 if lo == 0 else 12))),
                 ('@ELF@', hex(entry-0x100000)), ('@LO@', str(lo)), ('@HI@', str(lo+k)),
                 ('@K@', str(k)), ('@BODY@', body), ('@MAN@', man),
                 ('@LOX@', hex(lo)), ('@HIX@', hex(lo+k))]:
        s = s.replace(a, b)
    assert '(*' not in s.split('*)',1)[0][2:], name
    open(f'proofs/{name}_proof.v', 'w').write(s)
    open(f'headers/{name}.txt', 'w').write(s.split('\nFrom Stdlib',1)[0] + '\n')
