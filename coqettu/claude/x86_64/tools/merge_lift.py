#!/usr/bin/env python3
"""Merge Ghidra-split fragments into one lifted program.

  merge_lift.py <base.v> <fragment.v> ...   (rewrites <base.v> in place)

Ghidra sometimes splits one machine function into several (e.g. treating a
leading JMP as a tail call), and pcode2coq then lifts only the first piece.
All lifts use global addresses, so the match arms of the fragments can be
appended to the base program's match.  Duplicate addresses must agree.
"""
import re, sys

def arms(text):
    body = text[text.index('match a with') + len('match a with'):text.index('| _ => None')]
    parts = re.split(r'(?=\n\(\* 0x[0-9a-f]+: )', body)
    res = {}
    for p in parts:
        m = re.search(r'^\| (0x[0-9a-f]+) =>', p, re.M)
        if m: res[int(m.group(1), 16)] = p.rstrip() + '\n'
    return res

base = open(sys.argv[1]).read()
allarms = arms(base)
names = []
for f in sys.argv[2:]:
    t = open(f).read()
    names.append(re.search(r'function: (\S+)', t).group(1))
    for a, p in arms(t).items():
        if a in allarms and allarms[a].split('\n', 2)[2] != p.split('\n', 2)[2]:
            sys.exit(f'conflict at {hex(a)}')
        allarms.setdefault(a, p)
head = base[:base.index('match a with') + len('match a with')]
head = head.replace('*)\n', f'merged fragments: {", ".join(names)} (tools/merge_lift.py)\n*)\n', 1)
tail = base[base.index('| _ => None'):]
out = head + '\n' + ''.join(allarms[a] for a in sorted(allarms)) + '\n' + tail
open(sys.argv[1], 'w').write(out)
print(f'{sys.argv[1]}: {len(allarms)} instructions')
