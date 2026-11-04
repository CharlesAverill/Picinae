#!/usr/bin/env python3
"""Finite emitted-IL/byte-array oracle checks; not an instruction soundness proof."""
from copy import deepcopy
import json
from pathlib import Path
import random
import sys
import unittest

from pcode2coq_scalar import ScalarLifter, Unsupported
from pcode2coq_neon_loads import NeonLoadLifter
from test_bitforms import RawLanguage
from test_ccmp import RawInsn
from test_scalar import Reg, VN, Space, parse, execute
import test_scalar as il

ROOT = Path(__file__).resolve().parents[2]
ART = ROOT / 'Examples/claude/lifter/neon_loads'
RAW = json.loads((ART/'RAW.json').read_text())
MASK = (1 << 64) - 1


class Language(RawLanguage):
    def __init__(self, row):
        super().__init__(row)
        self.bases = {b['name']: b for b in RAW['vector_bases']}

    def getRegister(self, a, size=None):
        if isinstance(a, str):
            b = self.bases.get(a)
            return Reg(b['name'], b['offset'], b['width']) if b else None
        if 0x5000 <= a.offset < 0x5400 and (a.offset-0x5000)%32==0 and size in (8,32):
            b=self.bases['z'+str((a.offset-0x5000)//32)]
            return Reg(b['name'],b['offset'],b['width'])
        return super().getRegister(a, size)

    def getAddressSpace(self, n):
        return Space() if n == 0x1b1 else None


def lower(row, base=0):
    return NeonLoadLifter(Language(row), base).instruction(RawInsn(row))


def cases():
    rows = RAW['fixtures'][:118]
    rows += [r for rr in RAW['targets'].values() for r in rr
             if r['mnemonic'] in ('ldr', 'ldp') and 'q' in r['assembly']]
    return list({r['bytes']: r for r in rows}.values())


def decode(row):
    # Separate architectural decoder, never calls the lowering gate.
    b = int.from_bytes(bytes.fromhex(row['bytes']), 'little')
    pair = row['mnemonic'] == 'ldp'
    rn = (b >> 5) & 31
    dests = [b & 31] + ([(b >> 10) & 31] if pair else [])
    if pair:
        mode = {1:'post', 2:'offset', 3:'pre'}[(b >> 23) & 3]
        imm = (b >> 15) & 127
        off = (imm - 128 if imm >= 64 else imm) * 16
    elif b & (1 << 24):
        mode, off = 'offset', ((b >> 10) & 4095) * 16
    elif b & (1 << 21):
        mode, off = 'register', 0
    else:
        mode = 'pre' if (b >> 10) & 3 == 3 else 'post'
        imm = (b >> 12) & 511
        off = imm - 512 if imm >= 256 else imm
    return b, 'R_SP' if rn == 31 else f'R_X{rn}', dests, mode, off


def oracle(row, before):
    bits, base, dests, mode, off = decode(row)
    if mode == 'register':
        index = before[f'R_X{(bits >> 16) & 31}'][0]
        ext = (bits >> 13) & 7
        if ext in (2, 6):
            index &= 0xffffffff
            if ext == 6 and index >= 0x80000000:
                index -= 1 << 32
        off = index * (16 if bits & (1 << 12) else 1)
    ea = before[base][0] + (0 if mode == 'post' else off)
    after = before.copy()
    addresses = [(ea + 16*k) & MASK for k in range(len(dests))]
    for d, a in zip(dests, addresses):
        # Architectural Q write also zeros all modeled bits above low128.
        array = before['V_MEM64'][0]
        after[f'R_Z{d}'] = (int.from_bytes(bytes(array.get((a+j)&MASK, 0) for j in range(16)), 'little'), 256)
    if mode in ('pre', 'post'):
        after[base] = ((before[base][0] + off) & MASK, 64)
    return after, addresses


def initial(row, trial, kernel=False):
    rng = random.Random(10100 + trial)
    s = {f'R_X{i}': (rng.getrandbits(64),64) for i in range(31)}
    s.update({f'R_Z{i}': (rng.getrandbits(256) | (1 << 255),256) for i in range(32)})
    s.update({'R_'+n: (0xa0+i,8) for i,n in enumerate(('NG','ZR','CY','OV','TMPNG','TMPZR','TMPCY','TMPOV'))})
    s.update(R_SP=(33,64), R_PC=(0xfeed,64))
    bits, base, _, mode, off = decode(row)
    targets = [0,1,15,31,63,127,255,(1 << 64)-8,(1 << 64)-1]
    a = targets[trial % len(targets)]
    if mode == 'register':
        index = f'R_X{(bits >> 16) & 31}'
        s[index] = ([0,1,0x7fffffff,0x80000000,0xffffffff,MASK][trial%6],64)
        if kernel and index == base:
            # Stdlib N.shiftr is Pos.iter div2: actual getmem at huge
            # addresses cannot be reduced affordably. Python retains those
            # modular/large-address cases. Kernel inputs use small EAs.
            s[index] = (trial%7,64)
        # Derive a base giving the desired effective address independently of
        # the oracle. base=index alias uses its original snapshot directly.
        if index != base:
            x=s[index][0]; ext=(bits>>13)&7
            if ext in (2,6): x &= 0xffffffff
            if ext==6 and x>=1<<31: x-=1<<32
            off=x*(16 if bits&0x1000 else 1)
            s[base]=((a-off)&MASK,64)
    else:
        s[base]=((a-(0 if mode=='post' else off))&MASK,64)
    # A finite N-backed memory for both Python and actual Rocq interpreter.
    s['V_MEM64']=({i:(i*37+trial*17+11)&255 for i in range(256)},'memory')
    return s


# Keep existing parser/arithmetic evaluator unchanged; adapt only its memory
# lookup to Picinae's byte-wise modular address semantics and record read order.
_evaluate = il.evaluate
reads = []
def evaluate(tree, state):
    if tree[0] == 'load':
        _, mem, addr, size = tree
        array, _ = evaluate(mem,state)
        a, _ = evaluate(addr,state)
        reads.append((a,size))
        return sum(array.get((a+i)&MASK,0) << (8*i) for i in range(size)), size*8
    return _evaluate(tree,state)
il.evaluate = evaluate


def raw_temporaries(row, before):
    """Independent tiny raw evaluator checks each emitted temporary as well.

    This is additional finite evidence, not the architectural oracle above.
    The accepted raw DAG has only these six expression operations and loads.
    """
    state=deepcopy(before)
    temps={}
    names={}
    def register(v):
        a=v['offset']
        if 0x5000 <= a < 0x5400:
            i,byte=divmod(a-0x5000,32)
            return f'R_Z{i}',byte*8,256
        return ('R_SP',0,64) if a==8 else (f'R_X{(a-0x4000)//8}',0,64)
    def read(v):
        if v['kind']=='constant': return v['offset']% (1<<(8*v['size']))
        if v['kind']=='unique': return temps[v['offset'],v['size']]
        name,shift,_=register(v)
        return (state[name][0]>>shift)&((1<<(8*v['size']))-1)
    for op in row['ops']:
        code=op['code']; args=op['args']; out=op['out']; w=8*out['size']
        if code=='LOAD':
            a=read(args[1]);array=state['V_MEM64'][0]
            x=int.from_bytes(bytes(array.get((a+i)&MASK,0) for i in range(out['size'])),'little')
        else:
            a=read(args[0])
            if code in ('COPY','INT_ZEXT'): x=a
            elif code=='INT_SEXT':
                sw=8*args[0]['size'];x=a-(1<<sw) if a&(1<<(sw-1)) else a
            elif code=='INT_ADD': x=a+read(args[1])
            elif code=='INT_LEFT': x=a<<read(args[1])
            else: raise AssertionError(code)
        x%=1<<w
        if out['kind']=='unique':
            key=out['offset'],out['size'];names.setdefault(key,'T'+str(len(names)));temps[key]=x
        else:
            name,shift,bw=register(out);mask=((1<<w)-1)<<shift
            state[name]=((state[name][0]&~mask)|(x<<shift),bw)
    return {names[k]:(x,8*k[1]) for k,x in temps.items()}


def malformed(row):
    for i,op in enumerate(row['ops']):
        bad=deepcopy(row); del bad['ops'][i]; yield bad
        bad=deepcopy(row); bad['ops'][i]['code']='CALLOTHER'; yield bad
        bad=deepcopy(row); bad['ops'][i]['args'].append(dict(kind='constant',offset=0,size=1)); yield bad
        for j,v in enumerate(op['args']):
            for field in ('offset','size'):
                bad=deepcopy(row); bad['ops'][i]['args'][j][field]^=1; yield bad
        if op['out']:
            bad=deepcopy(row); bad['ops'][i]['out']=None; yield bad
            bad=deepcopy(row); bad['ops'][i]['out']['size']+=1; yield bad
    for bit in range(32):
        bad=deepcopy(row); b=int.from_bytes(bytes.fromhex(row['bytes']),'little')^(1<<bit)
        bad['bytes']=b.to_bytes(4,'little').hex(); yield bad
    for data in ('',row['bytes'][:6],row['bytes']+'00'):
        bad=deepcopy(row); bad['bytes']=data; yield bad
    bad=deepcopy(row); bad['ops'].reverse(); yield bad
    bad=deepcopy(row); bad['ops'].append(deepcopy(row['ops'][-1])); yield bad


class Tests(unittest.TestCase):
    def test_finite(self):
        count=0
        for r in cases():
            tree=parse(lower(r))
            self.assertEqual(lower(r),lower(r,0x100000))
            for trial in range(36):
                before=initial(r,trial); actual=deepcopy(before); reads.clear()
                self.assertIsNone(execute(tree,actual))
                expected,addresses=oracle(r,before)
                for v,value in expected.items(): self.assertEqual(actual[v],value,(r['assembly'],trial,v))
                for v,value in raw_temporaries(r,before).items(): self.assertEqual(actual[v],value,(r['assembly'],trial,v))
                views=NeonLoadLifter(Language(r))
                for d in decode(r)[2]:
                    for size in (8,16):
                        expr,_=views.read(VN('register',0x5000+32*d,size))
                        tree_view=parse('Move R_X0 ('+expr+')')[1][0][2]
                        self.assertEqual(evaluate(tree_view,actual),
                                         (expected[f'R_Z{d}'][0]&((1<<(8*size))-1),8*size))
                self.assertEqual(reads,[(a,16) for a in addresses])
                count+=1
        print(f'PASS {len(cases())} exact encoding shapes; {count} full-register/memory/ordered-load snapshots')

    def test_strict(self):
        count=0
        for r in cases():
            with self.assertRaises(Unsupported): ScalarLifter(Language(r)).instruction(RawInsn(r))
            for bad in malformed(r):
                # SXTX/LSL share the identical 64-bit shift DAG. A change of
                # option3<->7 is another valid encoding, not a malformed DAG.
                b=int.from_bytes(bytes.fromhex(r['bytes']),'little')
                if (len(bad['bytes'])==8 and int.from_bytes(bytes.fromhex(bad['bytes']),'little')==b^(1<<15)
                        and decode(r)[3]=='register' and (b>>13)&7 in (3,7)):
                    self.assertEqual(lower(r),lower(bad)); continue
                with self.assertRaises(Unsupported, msg=(r['assembly'],bad)): lower(bad)
                count+=1
        for r in RAW['fixtures'][118:124]:
            with self.assertRaises(Unsupported): lower(r)
        print(f'PASS {count} malformed encoding/DAG/width/order mutations; scalar default still rejects all Q forms')

    def test_temporaries_and_metadata(self):
        for r in cases():
            bad=deepcopy(r)
            for o in bad['ops']:
                for v in [o['out'],*o['args']]:
                    if v and v['kind']=='unique': v['offset']+=0x100000
            self.assertEqual(lower(r),lower(bad))
        lang=Language(cases()[0]); lang.bases=deepcopy(lang.bases); lang.bases['z0']['width']=512
        with self.assertRaises(Unsupported): NeonLoadLifter(lang).instruction(RawInsn(cases()[0]))
        # Keep all identities but place two8-byte unique slots one byte apart.
        bad=deepcopy(next(r for r in cases() if decode(r)[3]=='register'))
        slots=sorted({(v['offset'],v['size']) for o in bad['ops'] for v in [o['out'],*o['args']] if v and v['kind']=='unique'})
        mapping={k:i for i,k in enumerate(slots)}
        for o in bad['ops']:
            for v in [o['out'],*o['args']]:
                if v and v['kind']=='unique': v['offset']=mapping[v['offset'],v['size']]
        with self.assertRaisesRegex(Unsupported,'overlapping unique'): lower(bad)
        # Coherent D/Q reads see exactly the same Z256 cell.
        lifter=NeonLoadLifter(Language(cases()[0]))
        for size in (8,16):
            exp,_=lifter.read(VN('register',0x5000,size))
            value,width=evaluate(parse('Move R_X0 ('+exp+')')[1][0][2],{'R_Z0':((1<<256)-1,256)})
            self.assertEqual((value,width),((1<<(size*8))-1,size*8))
        print('PASS alpha-renamed temps, Z metadata mismatch, coherent D64/Q128 views')


def generate():
    rows=cases()
    text='''(* OPEN instruction fragments only; no complete memcmp/strlen map.
Finite total modular-memory IL checks; no universal/hardware correctness. *)
Require Import Picinae_armv8 Picinae_finterp NArith List Bool.
Import ListNotations.
Open Scope N.
Definition qview z := N.land z (2^128-1).
Definition dview z := N.land z (2^64-1).
'''
    for i,r in enumerate(rows): text+=f'(* {r["assembly"]}; {r["bytes"]} *)\nDefinition fixture_{i} : stmt :=\n{lower(r)}.\n'
    text+='Definition open_fragments : program := fun _ a => match a with\n'
    text+=''.join(f'| {4*i} => Some (4,fixture_{i})\n' for i in range(len(rows)))+'| _ => None end.\n'
    text+='''Theorem welltyped : welltyped_prog arm8typctx open_fragments.
Proof. Picinae_typecheck. Qed.
Definition check q initial expected : bool :=
  match fexec_stmt noe_setop noe_typop arm8typctx q (fun _ => 0) (fun _ => 0) initial with
  | FIS l (FIExit None) _ => forallb (fun p => N.eqb (updstr (fun _ => 0) l vupdate (fst p)) (snd p)) expected
  | _ => false
  end.
'''
    # Memory access predicates are explicitly outside this finite total-memory
    # check. Python tests verify exact read order/width and zero stores.
    checks=[]
    frames={}
    for trial in range(7):
        frame=initial(rows[0],trial)
        # Use the unmodified deterministic register state as a common frame.
        rng=random.Random(10100+trial)
        frame.update({f'R_X{i}':(rng.getrandbits(64),64) for i in range(31)})
        frame['R_SP']=(33,64)
        frame['V_MEM64']=(sum(v << (8*k) for k,v in frame['V_MEM64'][0].items()),0)
        frames[trial]=frame
        text+=f'Definition frame_{trial} : list varval := [\n'+ ';\n'.join(
            f'VarVal {v} 0x{x:x} (Some {w})' if v!='V_MEM64' else f'VarVal V_MEM64 0x{x:x} (Some (8*2^64))'
            for v,(x,w) in frame.items())+'].\n'
    text+='''Definition expected initial changes : list (var * N) :=
  map (fun vv => (vvvar vv, updstr (updstr (fun _ => 0) initial vupdate) changes vupdate (vvvar vv))) frame_0.
'''
    for i,r in enumerate(rows):
        for trial in range(7):
            before=initial(r,trial,kernel=True); after,_=oracle(r,before)
            before['V_MEM64']=frames[trial]['V_MEM64']
            after['V_MEM64']=frames[trial]['V_MEM64']
            overrides=[f'VarVal {v} 0x{x:x} (Some {w})' for v,(x,w) in before.items() if before[v]!=frames[trial][v]]
            changes=[f'VarVal {v} 0x{x:x} (Some {w})' for v,(x,w) in after.items() if before[v]!=after[v]]
            name=f'snapshot_{i}_{trial}'
            text+=f'Definition {name} : list varval := ['+';'.join(overrides)+f'] ++ frame_{trial}.\n'
            checks.append(f'check fixture_{i} {name} (expected {name} ['+';'.join(changes)+'])')
    for i in range(0,len(checks),32):
        text+=f'Theorem finite_execution_{i//32} : forallb (fun b => b) [\n'+ ';\n'.join(checks[i:i+32])+'] = true.\nProof. vm_compute. reflexivity. Qed.\n'
    post=next(i for i,r in enumerate(rows) if r['bytes']==RAW['fixtures'][31]['bytes'])
    ret=lower(RAW['fixtures'][125])
    text+=f'''(* Closed synthetic body, boundaries0,4,8; return boundary12.
Exact assembled words: {rows[0]['bytes']} {rows[post]['bytes']} {RAW['fixtures'][125]['bytes']}.
This synthetic fixture is not a libc function map. *)
Definition closed_synthetic : program := fun _ a => match a with
| 0 => Some (4,fixture_0)
| 4 => Some (4,fixture_{post})
| 8 => Some (4,{ret})
| _ => None end.
Theorem closed_welltyped : welltyped_prog arm8typctx closed_synthetic.
Proof. Picinae_typecheck. Qed.
Definition closed_initial := VarVal R_X30 12 (Some 64) :: snapshot_0_1.
'''
    before=initial(rows[0],1);before['R_X30']=(12,64)
    after,_=oracle(rows[0],before);after,_=oracle(rows[post],after)
    after['R_PC']=(12,64)  # Pinned RET raw pcode copies X30 to PC before Jmp.
    changes=';'.join(f'VarVal {v} 0x{x:x} (Some {w})' for v,(x,w) in after.items() if before[v]!=(x,w))
    text+=f'''Theorem finite_closed_execution :
 match fexec_stmt noe_setop noe_typop arm8typctx
   (fixture_0 $; fixture_{post} $; {ret})
   (fun _ => 0) (fun _ => 0) closed_initial with
 | FIS l (FIExit (Some (Addr a))) _ => N.eqb a 12 &&
   forallb (fun p => N.eqb (updstr (fun _ => 0) l vupdate (fst p)) (snd p))
     (expected closed_initial [{changes}])
 | _ => false end = true.
Proof. vm_compute. reflexivity. Qed.
'''
    (ART/'e10_neon_loads.v').write_text(text)
    (ART/'IL.json').write_text(json.dumps({r['bytes']:lower(r) for r in rows},indent=2)+'\n')
    print(f'Generated {len(rows)} fragments, {len(checks)} finite executions')


if __name__=='__main__':
    if '--generate' in sys.argv: generate()
    else: unittest.main()
