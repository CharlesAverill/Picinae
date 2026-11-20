#!/usr/bin/env python3
"""Exact per-instruction IL AST comparison plus finite equivalence regressions.

No target execution and no functional correctness claim. Every structural
difference is retained as a unified diff; architectural effects are sampled
using the independent tiny emitted-IL evaluator in test_scalar.py.
"""
import difflib
import json
import pathlib
import random
import re
import sys

repo = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0,str(repo/'tools/ghidra-lifter'))
from test_scalar import parse, execute


def instructions(text):
    text = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
    return {int(m[1], 16): m[2].strip() for m in
            re.finditer(r'\| (0x[0-9a-f]+) => Some \(4,\s*(.*?)\n\)',text,re.S)}


class Memory(dict):
    def get(self, k, default=0): return super().get(k, (k * 197 + (k >> 8) + 17) & 255)
    def copy(self): return Memory(self)


rng = random.Random(1102)
results = []
for name in ('toascii','div','ldiv','swab','ffs','ffsl'):
    old_path = repo/f'Examples/claude/{name}_arm8.v'
    new_path = repo/f'Examples/claude/lifter/scalar_smoke/e11_{name}_arm8.v'
    old, new = instructions(old_path.read_text()), instructions(new_path.read_text())
    assert old.keys() == new.keys(), name
    differences = []
    for addr in old:
        a, b = parse(old[addr]), parse(new[addr])
        if a != b:
            differences.append(hex(addr))
        regs = set(re.findall(r'\bR_[A-Z0-9]+\b', old[addr]+new[addr]))
        for trial in range(128):
            state = {r: ((rng.randrange(2) if r in {'R_NG','R_ZR','R_CY','R_OV','R_TMPNG','R_TMPZR','R_TMPCY','R_TMPOV'} else
                          0 if trial==0 else (1<<64)-1 if trial==1 else rng.getrandbits(64)),
                         8 if r in {'R_NG','R_ZR','R_CY','R_OV','R_TMPNG','R_TMPZR','R_TMPCY','R_TMPOV'} else 64) for r in regs}
            state['V_MEM64'] = (Memory(), 'memory')
            sa, sb = state.copy(), state.copy()
            ja, jb = execute(a,sa), execute(b,sb)
            assert ja == jb, (name,hex(addr),'jump',ja,jb)
            for r in regs | {'V_MEM64'}:
                assert sa[r] == sb[r], (name,hex(addr),r,state,sa[r],sb[r])
    print(f'{name}: {len(old)} instructions; {len(old)-len(differences)} identical normalized ASTs; {len(differences)} exact explained differences; 128 effect samples/instruction PASS')
    results.append(dict(symbol=name,instructions=len(old),identical_ast=len(old)-len(differences),different_addresses=differences,samples_per_instruction=128))
    (repo/f'notes/e11-canonical-lifter/{name}.diff').write_text(''.join(difflib.unified_diff(old_path.read_text().splitlines(True),new_path.read_text().splitlines(True),fromfile=str(old_path.relative_to(repo)),tofile=str(new_path.relative_to(repo)))))
(repo/'notes/e11-canonical-lifter/comparison.json').write_text(json.dumps(results,indent=2)+'\n')
print('PASS historical IL comparison (finite regression evidence only)')
