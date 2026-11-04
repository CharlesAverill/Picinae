#!/usr/bin/env python3
"""Replay actual pinned raw pcode; compare emitted IL with Arm scalar formulas.

Finite regressions only. --generate emits separate kernel typing/finite fixtures.
"""
from copy import deepcopy
import json
from pathlib import Path
import random
import sys
import unittest

from pcode2coq_scalar import ScalarLifter, Unsupported, BITFORMS
from test_scalar import VN, Reg, Language, Op, Insn, parse, execute

ROOT = Path(__file__).resolve().parents[2]
ART = ROOT / 'Examples/claude/lifter/scalar_bitforms'
RAW = json.loads((ART / 'RAW.json').read_text())


class RawLanguage(Language):
    def __init__(self, row):
        self.regs = {(v['offset'], v['size']): v.get('base') for op in row['ops'] for v in [op['out'], *op['args']] if v and v['kind'] == 'register'}
    def getRegister(self, a, size):
        b = self.regs.get((a.offset, size))
        return Reg(b['name'], b['offset'], b['width']) if b else None


class RawInsn(Insn):
    def __init__(self, row):
        node = lambda v: VN(v['kind'], v['offset'], v['size']) if v else None
        super().__init__(row['mnemonic'], *(Op(op['code'], node(op['out']), *(node(v) for v in op['args'])) for op in row['ops']))
        self.row = row
    def getBytes(self): return bytes.fromhex(self.row['bytes'])


def lower(row):
    return ScalarLifter(RawLanguage(row)).instruction(RawInsn(row))


def cases():
    rows = RAW['fixtures'] + [r for rows in RAW['targets'].values() for r in rows if r['mnemonic'] in BITFORMS]
    return list({r['bytes']: r for r in rows}.values())


def oracle(row, before):
    # Independent architectural equations, not a pcode interpreter.
    bits = int.from_bytes(bytes.fromhex(row['bytes']), 'little')
    w = 64 if bits >> 31 else 32
    mask = (1 << w) - 1
    d, n, m = bits & 31, (bits >> 5) & 31, (bits >> 16) & 31
    a = before[f'R_X{n}'][0] & mask
    b = before.get(f'R_X{m}', (0, 64))[0] & mask
    name = row['mnemonic']
    if name == 'rev': result = int.from_bytes(a.to_bytes(w // 8, 'little'), 'big')
    elif name == 'ubfiz':
        lsb, count = w - ((bits >> 16) & 63), ((bits >> 10) & 63) + 1
        result = (a & ((1 << count) - 1)) << lsb
    elif name == 'orn': result = a | (~b & mask)
    elif name == 'bics': result = a & (~b & mask)
    else: raise AssertionError(name)
    after = before.copy()
    after[f'R_X{d}'] = (result, 64)
    if name == 'bics':
        after.update(R_NG=(result >> (w - 1), 8), R_ZR=(int(result == 0), 8), R_CY=(0, 8), R_OV=(0, 8),
                     R_TMPNG=(result >> (w - 1), 8), R_TMPZR=(int(result == 0), 8))
    return after


def initial(rng, trial):
    choices = [0, (1 << 64) - 1, 0xffffffff80000000, 0x0123456789abcdef]
    s = {f'R_X{i}': (choices[trial] if trial < len(choices) else rng.getrandbits(64), 64) for i in range(31)}
    for i, name in enumerate(('NG', 'ZR', 'CY', 'OV', 'TMPNG', 'TMPZR', 'TMPCY', 'TMPOV')):
        s['R_' + name] = ((trial >> (i % 4)) & 1, 8)
    s.update(R_SP=(0x123456789abcdef0, 64), R_PC=(0xabcdef, 64))
    return s


class Tests(unittest.TestCase):
    def test_actual_and_width_fixtures(self):
        rng = random.Random(2901)
        count = 0
        for row in cases():
            tree = parse(lower(row))
            for trial in range(512):
                before = initial(rng, trial)
                actual = before.copy()
                self.assertIsNone(execute(tree, actual))
                for r, value in oracle(row, before).items():
                    self.assertEqual(actual[r], value, (row['assembly'], trial, r))
                count += 1
        print(f'PASS {len(cases())} exact-byte shapes; {count} whole-register/flag snapshots')

    def test_malformed_pcode_and_bytes(self):
        count = 0
        for row in cases():
            variants = []
            for i, op in enumerate(row['ops']):
                bad = deepcopy(row); del bad['ops'][i]; variants.append(bad)
                bad = deepcopy(row); bad['ops'][i]['code'] = 'CALLOTHER'; variants.append(bad)
                for j, arg in enumerate(op['args']):
                    bad = deepcopy(row); v = bad['ops'][i]['args'][j]
                    v['offset'] ^= 1; variants.append(bad)
                    bad = deepcopy(row); bad['ops'][i]['args'][j]['size'] += 1; variants.append(bad)
                bad = deepcopy(row); bad['ops'][i]['out']['size'] += 1; variants.append(bad)
            bad = deepcopy(row); bad['bytes'] = '1f2003d5'; variants.append(bad)
            bad = deepcopy(row); bad['ops'].append(deepcopy(row['ops'][-1])); variants.append(bad)
            for bad in variants:
                with self.assertRaises(Unsupported): lower(bad)
                count += 1
        print(f'PASS {count} malformed/unknown/mismatched forms rejected')

    def test_unhandled_shapes(self):
        for row in RAW['fixtures']:
            bits = int.from_bytes(bytes.fromhex(row['bytes']), 'little')
            changes = [bits | 31, bits | (31 << 5)]
            if row['mnemonic'] in {'orn', 'bics'}:
                changes += [bits | (1 << 10), bits | (1 << 22), bits | (31 << 16)]
            if row['mnemonic'] == 'ubfiz': changes += [bits ^ (1 << 22), bits | (63 << 10)]
            for b in changes:
                bad = deepcopy(row); bad['bytes'] = b.to_bytes(4, 'little').hex()
                with self.assertRaises(Unsupported): lower(bad)


def generate():
    texts = []
    checks = []
    for i, row in enumerate(cases()):
        stmt = lower(row)
        texts.append(f'(* {row["assembly"]}; bytes {row["bytes"]} *)\nDefinition fixture_{i} : stmt :=\n{stmt}.\n')
        rng = random.Random(2902 + i)
        for trial in range(6):
            s = initial(rng, trial)
            out = oracle(row, s)
            init = '; '.join(f'VarVal {r} 0x{v:x} (Some {w})' for r, (v, w) in s.items())
            expect = '; '.join(f'({r}, 0x{v:x})' for r, (v, _) in out.items())
            checks.append(f'check fixture_{i} [{init}] [{expect}]')
    text = '''(* e29 finite instruction fixtures, not function correctness or lifter refinement. *)
Require Import Picinae_armv8 Picinae_finterp NArith List Bool.
Import ListNotations.
Open Scope N.
'''
    text += '\n'.join(texts)
    text += '\nDefinition fixtures : program := fun _ a => match a with\n'
    text += ''.join(f'| {i * 4} => Some (4, fixture_{i})\n' for i in range(len(texts))) + '| _ => None end.\n'
    text += '''Theorem welltyped : welltyped_prog arm8typctx fixtures.
Proof. Picinae_typecheck. Qed.
Definition check q initial expected : bool :=
  match fexec_stmt noe_setop noe_typop arm8typctx q (fun _ => 0) (fun _ => 0) initial with
  | FIS l (FIExit None) nil => forallb (fun p => N.eqb (updstr (fun _ => 0) l vupdate (fst p)) (snd p)) expected
  | _ => false
  end.
Definition finite_checks : list bool := [
'''
    text += ';\n'.join(checks) + '].\n'
    text += '''Theorem finite_execution : forallb (fun b => b) finite_checks = true.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions welltyped.
Print Assumptions finite_execution.
'''
    (ART / 'e29_bitforms.v').write_text(text)
    (ART / 'IL.json').write_text(json.dumps([dict(bytes=r['bytes'], assembly=r['assembly'], il=lower(r)) for r in cases()], indent=2) + '\n')
    print(f'Generated {len(texts)} exact-byte fixture statements and {len(checks)} kernel finite checks')


if __name__ == '__main__':
    if sys.argv[1:] == ['--generate']: generate()
    else: unittest.main(verbosity=2)
