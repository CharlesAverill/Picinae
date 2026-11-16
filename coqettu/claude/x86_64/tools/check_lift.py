#!/usr/bin/env python3
"""Check that each lifted program covers every instruction of its function.

For programs/<fn>_amd64.v, take the function's extent from the ELF dynamic
symbol table (nm -S; for size-less asm symbols, up to the next symbol), list
its instructions with objdump (ignoring NOP padding), and report addresses
that the lift lacks or that lie outside the function (e.g. callees).
Usage: check_lift.py [fn ...]
"""
import os, re, subprocess, sys
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(HERE, '../../alpine_musl/x86_64/lib/libc.musl-x86_64.so.1')
BASE = 0x100000

def syms():
    out = subprocess.run(['nm', '-D', '--defined-only', '-S', BIN], capture_output=True, text=True).stdout
    res = {}
    for line in out.splitlines():
        p = line.split()
        if len(p) == 4: res.setdefault(p[3], (int(p[0], 16), int(p[1], 16)))
        elif len(p) == 3: res.setdefault(p[2], (int(p[0], 16), None))
    starts = sorted({a for a, _ in res.values()})
    for k, (a, s) in list(res.items()):
        if s is None:
            nxt = [x for x in starts if x > a]
            res[k] = (a, (nxt[0] - a) if nxt else 0x100)
    return res

def insns(lo, hi):
    out = subprocess.run(['objdump', '-d', '--no-show-raw-insn', f'--start-address={lo}', f'--stop-address={hi}', BIN],
                         capture_output=True, text=True).stdout
    r = []
    for line in out.splitlines():
        m = re.match(r'\s+([0-9a-f]+):\s+(.*)', line)
        if m:
            txt = m.group(2)
            if re.match(r'(nop|xchg\s+%ax,%ax|data16|cs nop|\.byte)', txt): continue
            r.append((int(m.group(1), 16), txt))
    return r

def lifted(path):
    return {int(a, 16) for a in re.findall(r'^\| (0x[0-9a-f]+) =>', open(path).read(), re.M)}

def main(names):
    S = syms()
    progs = sorted(f for f in os.listdir(os.path.join(HERE, 'programs')) if f.endswith('_amd64.v'))
    bad = 0
    for f in progs:
        fn = f[:-len('_amd64.v')]
        if names and fn not in names: continue
        if fn not in S: print(f'{fn}: no dynamic symbol'); continue
        a, sz = S[fn]
        want = {x + BASE: t for x, t in insns(a, a + sz)}
        have = lifted(os.path.join(HERE, 'programs', f))
        miss = sorted(set(want) - have); extra = sorted(have - set(want))
        status = 'OK' if not miss else 'INCOMPLETE'
        if miss: bad += 1
        print(f'{fn}: {status} ({len(have)} lifted, {len(want)} in symbol)' +
              (f' missing {[hex(x) for x in miss[:8]]}' if miss else '') +
              (f' extra {len(extra)}' if extra else ''))
    return bad

if __name__ == '__main__':
    sys.exit(1 if main(sys.argv[1:]) else 0)
