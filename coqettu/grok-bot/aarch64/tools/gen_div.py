#!/usr/bin/env python3
# Grok Bot (agent coqettu): generate proofs for musl's 64-bit {l,ll,imax}div.
import sys
FUNS = {
 'ldiv':    (0x15d394, 'long', 'ldiv_t', 'stdlib', 'stdlib.h'),
 'lldiv':   (0x15d3b0, 'long long', 'lldiv_t', 'stdlib', 'stdlib.h'),
 'imaxdiv': (0x15d378, 'intmax_t', 'imaxdiv_t', 'stdlib', 'inttypes.h'),
}
T = open('tools/div_template.v').read()
for name in sys.argv[1:]:
    e, at, rt, sd, inc = FUNS[name]
    s = T
    for a, b in [('@NAME@', name), ('@ENTRY@', hex(e)), ('@RET@', hex(e+12)), ('@ELF@', hex(e-0x100000)),
                 ('@ATYPE@', at), ('@RTYPE@', rt), ('@SRCDIR@', sd), ('@INCLUDE@', inc)]:
        s = s.replace(a, b)
    assert '(*' not in s.split('*)',1)[0][2:], name
    open(f'proofs/{name}_proof.v', 'w').write(s)
    open(f'headers/{name}.txt', 'w').write(s.split('\nFrom Stdlib',1)[0] + '\n')
