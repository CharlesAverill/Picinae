#!/usr/bin/env python3
"""Pinned CNEG pcode vs independent Arm equations; finite evidence only."""
from copy import deepcopy
import json
from pathlib import Path
import random
import sys
import unittest

from pcode2coq_scalar import ScalarLifter, Unsupported
from test_ccmp import RawInsn, holds
from test_bitforms import RawLanguage
from test_scalar import parse, execute

ROOT = Path(__file__).resolve().parents[2]
ART = ROOT / 'Examples/claude/lifter/scalar_cneg'
RAW = json.loads((ART / 'RAW.json').read_text())


def lower(row, base=0):
    return ScalarLifter(RawLanguage(row), base).instruction(RawInsn(row))


def cases():
    rows = RAW['fixtures'] + [r for rows in RAW['targets'].values() for r in rows if r['mnemonic'] == 'cneg']
    return list({r['bytes']: r for r in rows}.values())


def fields(row):
    bits = int.from_bytes(bytes.fromhex(row['bytes']), 'little')
    return 32 << (bits >> 31), ((bits >> 12) & 15) ^ 1, bits & 31, (bits >> 5) & 31


def initial(row, flags, operand):
    _, _, _, rn = fields(row)
    s = {f'R_X{i}': ((0xfedcba9801234567 + 131*i) % (1 << 64), 64) for i in range(31)}
    s[f'R_X{rn}'] = (operand % (1 << 64), 64)
    s.update({'R_' + name: ((flags >> shift) & 1, 8) for name,shift in zip(('NG','ZR','CY','OV'), (3,2,1,0))})
    s.update({'R_TMP' + name: (0x80+i, 8) for i,name in enumerate(('NG','ZR','CY','OV'))})
    s.update(R_SP=(0x123456789abcdef0, 64), R_PC=(0xabcdef, 64))
    return s


def oracle(row, before):
    w, cond, rd, rn = fields(row)
    mask = (1 << w) - 1
    a = before[f'R_X{rn}'][0] & mask
    old = sum(before['R_' + name][0] << shift for name,shift in zip(('NG','ZR','CY','OV'), (3,2,1,0)))
    result = (-a if holds(cond, old) else a) & mask
    after = before.copy()
    after[f'R_X{rd}'] = (result, 64)  # W write always clears upper X bits.
    return after


def operands(row):
    w = fields(row)[0]
    return [0, 1, 2, (1 << w)-1, 1 << (w-1), (1 << (w-1))-1,
            (1 << (w-1))+1, 0xfeedface80000000, 0xffffffff00000000,
            0xdeadbeef00000001, 0x123456787fffffff]


def inputs(row):
    for flags in range(16):
        for a in operands(row): yield initial(row,flags,a)
    rng = random.Random(3600 + int(row['bytes'],16))
    for i in range(64): yield initial(row, i % 16, rng.getrandbits(64))


def malformed(row):
    for i, op in enumerate(row['ops']):
        bad=deepcopy(row); del bad['ops'][i]; yield bad
        bad=deepcopy(row); bad['ops'][i]['code']='CALLOTHER'; yield bad
        bad=deepcopy(row); bad['ops'][i]['args'].append({'kind':'constant','offset':0,'size':1}); yield bad
        for j,arg in enumerate(op['args']):
            bad=deepcopy(row); bad['ops'][i]['args'][j]['offset'] ^= 1; yield bad
            bad=deepcopy(row); bad['ops'][i]['args'][j]['size'] += 1; yield bad
        if op['out']:
            bad=deepcopy(row); bad['ops'][i]['out']['size'] += 1; yield bad
            bad=deepcopy(row); bad['ops'][i]['out']=None; yield bad
        else:
            bad=deepcopy(row); bad['ops'][i]['out']={'kind':'unique','offset':123,'size':1}; yield bad
    for bit in range(32):
        bad=deepcopy(row); bits=int.from_bytes(bytes.fromhex(row['bytes']),'little') ^ (1 << bit)
        bad['bytes']=bits.to_bytes(4,'little').hex(); yield bad
    bits=int.from_bytes(bytes.fromhex(row['bytes']),'little')
    # Explicit zero registers and forbidden alias conditions.
    for mask,value in ((31,31),(31<<5,31<<5),(31<<16,31<<16),(15<<12,14<<12),(15<<12,15<<12)):
        bad=deepcopy(row); bad['bytes']=((bits & ~mask)|value).to_bytes(4,'little').hex(); yield bad
    branch=next(i for i,o in enumerate(row['ops']) if o['code']=='CBRANCH')
    for kind,offset in (('constant',0),('constant',1),('constant',3),('constant',0xffffffff),('ram',int(row['address'],16)+4)):
        bad=deepcopy(row); bad['ops'][branch]['args'][0]={'kind':kind,'offset':offset,'size':4}; yield bad
    bad=deepcopy(row); bad['ops'].append(deepcopy(row['ops'][-1])); yield bad
    bad=deepcopy(row); bad['ops'].reverse(); yield bad


class Tests(unittest.TestCase):
    def test_actual_forms(self):
        count=0
        for row in cases():
            tree=parse(lower(row))
            self.assertEqual(lower(row),lower(row,0x100000))
            for before in inputs(row):
                actual=before.copy()
                self.assertIsNone(execute(tree,actual))
                for r,v in oracle(row,before).items(): self.assertEqual(actual[r],v,(row['assembly'],before,r))
                count+=1
        print(f'PASS {len(cases())} assembled/ELF encoding shapes; {count} independent whole-register/flag snapshots')

    def test_malformed(self):
        count=0
        for row in cases():
            for bad in malformed(row):
                with self.assertRaises(Unsupported): lower(bad)
                count+=1
        print(f'PASS {count} malformed encoding/raw-control/dataflow/arity/width/output cases rejected')

    def test_temporaries(self):
        # Independent instruction objects on a reused lifter cannot retain old
        # initialization or numbering; nonoverlapping alpha-renaming is stable.
        lifter=ScalarLifter(RawLanguage(cases()[0]))
        for row in cases():
            renamed=deepcopy(row)
            for op in renamed['ops']:
                for v in [op['out'],*op['args']]:
                    if v and v['kind']=='unique': v['offset']+=0x100000
            self.assertEqual(lower(row),lower(renamed))
            lifter.lang=RawLanguage(row)
            self.assertEqual(lifter.instruction(RawInsn(row)),lower(row))
        row=deepcopy(cases()[6])
        slots=sorted({(v['offset'],v['size']) for o in row['ops'] for v in [o['out'],*o['args']] if v and v['kind']=='unique'})
        mapping={key:len(slots)-1-i for i,key in enumerate(slots)}
        for op in row['ops']:
            for v in [op['out'],*op['args']]:
                if v and v['kind']=='unique': v['offset']=mapping[v['offset'],v['size']]
        with self.assertRaisesRegex(Unsupported,'overlapping unique'): lower(row)
        print('PASS deterministic instruction-local temporaries and overlapping-unique rejection')


def generate():
    rows=cases()
    text='''(* e36 exact CNEG finite fixtures. No universal instruction/function correctness. *)
Require Import Picinae_armv8 Picinae_finterp NArith List Bool.
Import ListNotations.
Open Scope N.
'''
    for i,row in enumerate(rows):
        text+=f'(* {row["assembly"]}; {row["bytes"]} *)\nDefinition fixture_{i} : stmt :=\n{lower(row)}.\n'
    text+='\nDefinition fixtures : program := fun _ a => match a with\n'
    text+=''.join(f'| {i*4} => Some (4, fixture_{i})\n' for i in range(len(rows)))+'| _ => None end.\n'
    text+='''Theorem welltyped : welltyped_prog arm8typctx fixtures.
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
    # Share the architectural frame and snapshot construction. Repeating all
    # forty-one cells in every source literal exhausted the fixed memory cap.
    base=initial(rows[0],0,0xfedcba9801234567)
    text+='Definition frame : list varval := [\n'+';\n'.join(
        f'VarVal {r} 0x{v:x} (Some {w})' for r,(v,w) in base.items())+'].\n'
    text+='''Definition snapshot (rn : var) (operand flags : N) : list varval :=
  VarVal rn operand (Some 64) ::
  VarVal R_NG (N.land (N.shiftr flags 3) 1) (Some 8) ::
  VarVal R_ZR (N.land (N.shiftr flags 2) 1) (Some 8) ::
  VarVal R_CY (N.land (N.shiftr flags 1) 1) (Some 8) ::
  VarVal R_OV (N.land flags 1) (Some 8) :: frame.
Definition expected initial rd result : list (var * N) :=
  map (fun vv => (vvvar vv, vupdate (updstr (fun _ => 0) initial vupdate) rd result (vvvar vv))) frame.
Definition sample q rn rd operand flags result : bool :=
  let initial := snapshot rn operand flags in check q initial (expected initial rd result).
'''
    checks=[]
    for i,row in enumerate(rows):
        w,cond,rd,rn=fields(row)
        # Full Cartesian finite matrix: all legal alias conditions, old flags,
        # assembled register aliases/endpoints, widths and extreme operands.
        for flags in range(16):
            for operand in operands(row):
                before=initial(row,flags,operand)
                result=oracle(row,before)[f'R_X{rd}'][0]
                checks.append(f'sample fixture_{i} R_X{rn} R_X{rd} 0x{operand:x} {flags} 0x{result:x}')
    for i in range(0,len(checks),128):
        text+=f'Definition finite_checks_{i//128} : list bool := [\n'+';\n'.join(checks[i:i+128])+'].\n'
        text+=f'Theorem finite_execution_{i//128} : forallb (fun b => b) finite_checks_{i//128} = true.\nProof. vm_compute. reflexivity. Qed.\n'
    (ART/'e36_cneg.v').write_text(text)
    (ART/'IL.json').write_text(json.dumps([dict(bytes=r['bytes'],assembly=r['assembly'],il=lower(r)) for r in rows],indent=2)+'\n')
    print(f'Generated {len(rows)} statements; {len(checks)} finite checks in {(len(checks)+127)//128} facts')


if __name__=='__main__':
    if sys.argv[1:]==['--generate']: generate()
    else: unittest.main(verbosity=2)
