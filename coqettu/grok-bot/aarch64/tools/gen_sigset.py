#!/usr/bin/env python3
# Grok Bot (agent coqettu): generate proofs for musl's sigemptyset/sigfillset (aarch64).
import sys
FUNS = {
 'sigemptyset': (0x15221c, 8, '0', '0', 'str xzr,[x0]; mov w0,#0; ret',
   'All 64 signal bits are cleared.',
   'sigemptyset() initializes the signal set given by set to empty,\n            with all signals excluded from the set.'),
 'sigfillset': (0x152228, 12, '0xfffffffc7fffffffUL', '0xfffffffc7fffffff',
   'mov x1,#0xfffffffc7fffffff; str x1,[x0]; mov w0,#0; ret',
   'Bits 31..33 (signals 32..34, reserved by musl for internal use) stay\n   clear; every other signal 1..64 is set.',
   'sigfillset() initializes set to full, including all signals.'),
}
T = open('tools/sigset_template.v').read()
for name in sys.argv[1:]:
    e, retoff, valc, valx, asm, note, man = FUNS[name]
    s = T
    for a, b in [('@NAME@', name), ('@ENTRY@', hex(e)), ('@RET@', hex(e+retoff)), ('@ELF@', hex(e-0x100000)),
                 ('@VALC@', valc), ('@VALX@', valx), ('@ASM@', asm), ('@NOTE@', note), ('@MAN@', man)]:
        s = s.replace(a, b)
    assert '(*' not in s.split('*)',1)[0][2:], name
    open(f'proofs/{name}_proof.v', 'w').write(s)
    open(f'headers/{name}.txt', 'w').write(s.split('\nFrom Stdlib',1)[0] + '\n')
