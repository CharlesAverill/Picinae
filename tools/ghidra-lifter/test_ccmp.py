#!/usr/bin/env python3
"""Exact Ghidra CCMP fixtures vs independent A64 equations; finite evidence only."""
from copy import deepcopy
import json
from pathlib import Path
import random
import sys
import unittest

from pcode2coq_scalar import ScalarLifter, Unsupported
from test_bitforms import RawLanguage, RawInsn as BitInsn
from test_scalar import Addr, Insn, Op, VN, Language, parse, execute

ROOT = Path(__file__).resolve().parents[2]
ART = ROOT / 'Examples/claude/lifter/scalar_ccmp'
RAW = json.loads((ART / 'RAW.json').read_text())

class RawInsn(BitInsn):
    def getAddress(self): return Addr(int(self.row['address'], 16))


def lower(row, base=0):
    return ScalarLifter(RawLanguage(row), base).instruction(RawInsn(row))


def cases():
    rows = RAW['fixtures'] + [r for rows in RAW['targets'].values() for r in rows if r['mnemonic'] == 'ccmp']
    return list({r['bytes']: r for r in rows}.values())


def fields(row):
    bits = int.from_bytes(bytes.fromhex(row['bytes']), 'little')
    return 32 << (bits >> 31), (bits >> 11) & 1, (bits >> 12) & 15, bits & 15, (bits >> 5) & 31, (bits >> 16) & 31


def holds(cond, nzcv):
    n, z, c, v = [(nzcv >> i) & 1 for i in (3, 2, 1, 0)]
    # Full condition table independent of pcode and translator condition DAG.
    return [z == 1, z == 0, c == 1, c == 0, n == 1, n == 0,
            v == 1, v == 0, c == 1 and z == 0, c == 0 or z == 1,
            n == v, n != v, n == v and z == 0, n != v or z == 1,
            True, True][cond]


def initial(row, flags, a, b):
    w, immediate, cond, fallback, rn, rm = fields(row)
    s = {f'R_X{i}': ((0xfedcba9801234567 + 131*i) % (1 << 64), 64) for i in range(31)}
    if rn != 31: s[f'R_X{rn}'] = (a % (1 << 64), 64)
    if not immediate and rm != 31: s[f'R_X{rm}'] = (b % (1 << 64), 64)
    s.update({'R_' + name: ((flags >> shift) & 1, 8) for name, shift in zip(('NG','ZR','CY','OV'), (3,2,1,0))})
    # Dirty scratch bytes must be preserved on fallback and normalized on compare.
    s.update({'R_TMP' + name: (0x80+i, 8) for i,name in enumerate(('NG','ZR','CY','OV'))})
    s.update(R_SP=(0x123456789abcdef0, 64), R_PC=(0xabcdef, 64))
    return s


def oracle(row, before):
    w, immediate, cond, nzcv, rn, rm = fields(row)
    mask = (1 << w) - 1
    a = 0 if rn == 31 else before[f'R_X{rn}'][0] & mask
    b = rm if immediate else 0 if rm == 31 else before[f'R_X{rm}'][0] & mask
    old = sum(before['R_' + name][0] << shift for name,shift in zip(('NG','ZR','CY','OV'),(3,2,1,0)))
    after = before.copy()
    if holds(cond, old):
        result = (a - b) & mask
        # Signed overflow: mathematical signed difference falls outside width.
        signed = lambda x: x - (1 << w) if x >= 1 << (w - 1) else x
        diff = signed(a) - signed(b)
        flags = [result >> (w - 1), int(result == 0), int(a >= b), int(not -(1 << (w - 1)) <= diff < (1 << (w - 1)))]
        after.update({'R_TMP' + n: (v, 8) for n,v in zip(('NG','ZR','CY','OV'),flags)})
    else:
        flags = [(nzcv >> i) & 1 for i in (3,2,1,0)]
    after.update({'R_' + n: (v, 8) for n,v in zip(('NG','ZR','CY','OV'),flags)})
    return after


def inputs(row):
    w = fields(row)[0]
    sign, mask = 1 << (w - 1), (1 << w) - 1
    pairs = [(0,0), (0,1), (1,0), (mask,mask), (sign,1), (sign-1,mask),
             (sign,sign), (mask,1), (1,mask), (0xffffffff00000000,0),
             (0xfeedface80000000, 0x123456787fffffff)]
    for flags in range(16):
        for a,b in pairs: yield initial(row, flags, a,b)
    rng = random.Random(3000 + int(row['bytes'],16))
    for i in range(64): yield initial(row, i % 16, rng.getrandbits(64), rng.getrandbits(64))


class Tests(unittest.TestCase):
    def test_actual_forms(self):
        count = 0
        for row in cases():
            tree = parse(lower(row))
            self.assertEqual(lower(row), lower(row, 0x100000))  # no machine-address literal remains
            for before in inputs(row):
                actual = before.copy()
                self.assertIsNone(execute(tree, actual))
                for reg,value in oracle(row,before).items():
                    self.assertEqual(actual[reg], value, (row['assembly'],before,reg))
                count += 1
        print(f'PASS {len(cases())} actual encoding/pcode shapes; {count} architectural/scratch register snapshots')

    def test_malformed(self):
        count = 0
        for row in cases():
            variants = []
            for i, op in enumerate(row['ops']):
                bad=deepcopy(row); del bad['ops'][i]; variants.append(bad)
                bad=deepcopy(row); bad['ops'][i]['code']='CALLOTHER'; variants.append(bad)
                bad=deepcopy(row); bad['ops'][i]['args'].append({'kind':'constant','offset':0,'size':1}); variants.append(bad)
                for j, arg in enumerate(op['args']):
                    bad=deepcopy(row); bad['ops'][i]['args'][j]['offset'] ^= 1; variants.append(bad)
                    bad=deepcopy(row); bad['ops'][i]['args'][j]['size'] += 1; variants.append(bad)
                if op['out']:
                    bad=deepcopy(row); bad['ops'][i]['out']['size'] += 1; variants.append(bad)
                    bad=deepcopy(row); bad['ops'][i]['out']=None; variants.append(bad)
                else:
                    bad=deepcopy(row); bad['ops'][i]['out']={'kind':'unique','offset':123,'size':1}; variants.append(bad)
            for bit in (4,10,11,21,29,30,31):
                bad=deepcopy(row); b=int.from_bytes(bytes.fromhex(row['bytes']),'little') ^ (1 << bit); bad['bytes']=b.to_bytes(4,'little').hex(); variants.append(bad)
            bad=deepcopy(row); bad['ops'].append(deepcopy(row['ops'][-1])); variants.append(bad)
            bad=deepcopy(row); bad['ops'].reverse(); variants.append(bad)
            for bad in variants:
                with self.assertRaises(Unsupported): lower(bad)
                count += 1
        print(f'PASS {count} malformed encoding/DAG/branch/width/arity/output mutations rejected')

    def test_cfg_scope(self):
        row=deepcopy(cases()[0])
        branch=next(op for op in row['ops'] if op['code']=='CBRANCH')
        for target in (int(row['address'],16), int(row['address'],16)+8):
            bad=deepcopy(row)
            next(op for op in bad['ops'] if op['code']=='CBRANCH')['args'][0]['offset']=target
            with self.assertRaises(Unsupported): lower(bad)
        branch['args'][0]={'kind':'constant','offset':1,'size':8}
        with self.assertRaises(Unsupported): lower(row)
        # Same pcode under a generic mnemonic still hits the strict suffix gate.
        row=deepcopy(cases()[0]); row['mnemonic']='mov'
        with self.assertRaisesRegex(Unsupported,'machine CBRANCH with trailing pcode'): lower(row)
        with self.assertRaises(Unsupported):
            ScalarLifter(Language()).instruction(Insn('mov', Op('CBRANCH',None,VN('constant',0,8),VN('constant',1,1))))
        print('PASS CFG gate: only exact CCMP next-instruction compare suffix accepted')


def generate():
    rows=cases()
    text='''(* e30 exact CCMP finite fixtures. No universal instruction/function correctness. *)
Require Import Picinae_armv8 Picinae_finterp NArith List Bool.
Import ListNotations.
Open Scope N.
'''
    for i,row in enumerate(rows):
        text += f'(* {row["assembly"]}; {row["bytes"]} *)\nDefinition fixture_{i} : stmt :=\n{lower(row)}.\n'
    text += '\nDefinition fixtures : program := fun _ a => match a with\n'
    text += ''.join(f'| {i*4} => Some (4, fixture_{i})\n' for i in range(len(rows))) + '| _ => None end.\n'
    text += '''Theorem welltyped : welltyped_prog arm8typctx fixtures.
Proof. Picinae_typecheck. Qed.
Fixpoint finish expected fuel q initial : bool :=
  match fuel with
  | O => false
  | S k => match fexec_stmt noe_setop noe_typop arm8typctx q (fun _ => 0) (fun _ => 0) initial with
    | FIS l (FIExit None) nil => forallb (fun p => N.eqb (updstr (fun _ => 0) l vupdate (fst p)) (snd p)) expected
    | FIS l (FIStmt continuation) nil => finish expected k continuation l
    | _ => false
    end
  end.
Definition check q initial expected : bool := finish expected 8 q initial.
'''
    checks=[]
    covered=set()
    for i,row in enumerate(rows):
        w=fields(row)[0]
        # All old flags for every encoding; two signed-overflow edge operands.
        shape=fields(row)[:3]
        flags_to_check=range(16) if shape not in covered else (0,15)
        covered.add(shape)
        for flags in flags_to_check:
            before=initial(row,flags,1 << (w-1),1)
            after=oracle(row,before)
            init='; '.join(f'VarVal {r} 0x{v:x} (Some {w})' for r,(v,w) in before.items())
            expect='; '.join(f'({r}, 0x{v:x})' for r,(v,_) in after.items())
            checks.append(f'check fixture_{i} [{init}] [{expect}]')
    # Separate small theorems avoid a single large conversion term under the cap.
    for i in range(0,len(checks),128):
        text+=f'Definition finite_checks_{i//128} : list bool := [\n'+';\n'.join(checks[i:i+128])+'].\n'
        text+=f'Theorem finite_execution_{i//128} : forallb (fun b => b) finite_checks_{i//128} = true.\nProof. vm_compute. reflexivity. Qed.\n'
    (ART/'e30_ccmp.v').write_text(text)
    (ART/'IL.json').write_text(json.dumps([dict(bytes=r['bytes'],assembly=r['assembly'],il=lower(r)) for r in rows],indent=2)+'\n')
    print(f'Generated {len(rows)} statements; {len(checks)} finite checks in {(len(checks)+127)//128} closed facts')


if __name__=='__main__':
    if sys.argv[1:]==['--generate']: generate()
    else: unittest.main(verbosity=2)
