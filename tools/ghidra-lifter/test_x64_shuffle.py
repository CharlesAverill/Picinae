#!/usr/bin/env python3
"""Finite independent byte-array regression and adversarial DAG checks.
No ISA correctness, hardware execution or whole-function proof is claimed.
"""
import copy
import importlib.util
import json
from pathlib import Path
import random
import tempfile
import unittest
from test_x64 import Language, instruction
from test_x64_copy import vector_state, assembly_reference
from test_scalar import parse
from pcode2coq_x64_copy import CopyLifter
from pcode2coq_x64_shuffle import ShuffleLifter, Unsupported

REPO=Path(__file__).resolve().parents[2]
NOTES=REPO/'notes/e34-x86-copy-shuffles'
STATE=Path('/home/charles/code/friends/.toolchains/e34-x86-copy-shuffles')
MASK64=(1<<64)-1

def rows(kind):return json.loads((NOTES/(kind+'-raw.json')).read_text())
def descriptor(r):
    name,tail=r['assembly'].split(' ',1);dst,src,imm=tail.split(',')
    e=assembly_reference('MOVDQU '+dst+','+src);e.immediate=int(imm,0);return e

def oracle(e,s):
    # Independent little-endian arrays: source is the low concatenation half.
    # Sources are read before any update, including dst==src and memory alias.
    old=s[f'R_YMM{e.dst}'][0].to_bytes(32,'little')
    if e.src is None:
        address=(e.address[0]+sum(s['R_'+r][0]*k for r,k in e.address[1]))&MASK64
        source=bytes(s['V_MEM64'][0].get((address+i)&MASK64,0) for i in range(16))
    else:source=s[f'R_YMM{e.src}'][0].to_bytes(32,'little')[:16]
    concatenated=source+old[:16]+bytes(256)
    low=concatenated[e.immediate:e.immediate+16]
    s[f'R_YMM{e.dst}']=(int.from_bytes(low+old[16:],'little'),256)

def evaluate(tree,s):
    op,*args=tree
    if op=='word':return args[0]%(1<<args[1]),args[1]
    if op=='var':return s[args[0]]
    if op=='extract':
        hi,lo,exp=args;return (evaluate(exp,s)[0]>>lo)% (1<<(hi-lo+1)),hi-lo+1
    if op=='concat':
        a,wa=evaluate(args[0],s);b,wb=evaluate(args[1],s);return (a<<wb)|b,wa+wb
    if op=='bin':
        code,a,b=args;x,w=evaluate(a,s);y,wy=evaluate(b,s);assert w==wy
        result={'OP_RSHIFT':lambda:x>>y,'OP_PLUS':lambda:x+y,'OP_TIMES':lambda:x*y}[code]()
        return result%(1<<w),w
    if op=='load':
        mem,_=evaluate(args[0],s);address,w=evaluate(args[1],s);assert w==64
        n=args[2];return sum(mem.get((address+i)&MASK64,0)<<(8*i) for i in range(n)),8*n
    raise AssertionError(tree)

def execute(tree,s):
    op,*args=tree
    if op=='seq':
        for t in args[0]:execute(t,s)
    elif op=='move':s[args[0]]=evaluate(args[1],s)
    else:raise AssertionError(tree)

class Tests(unittest.TestCase):
    def test_independent_byte_oracle_all_frames(self):
        comparisons=0;immediates=set()
        for kind in ('actual','synthetic'):
            rr=rows(kind);l=ShuffleLifter(Language(rr))
            for r in rr:
                if not r['assembly'].startswith('PALIGNR XMM'):continue
                e=descriptor(r);immediates.add(e.immediate);tree=parse(l.instruction(instruction(r)))
                for seed in range(40):
                    s=vector_state(seed)
                    # Zero/all-one, lane-distinct and duplicate byte values.
                    if seed<4:
                        for n in range(16):
                            data=[bytes(32),bytes([255])*32,bytes(range(32)),bytes([n,0x80])*16][seed]
                            s[f'R_YMM{n}']=(int.from_bytes(data,'little'),256)
                    if e.address is not None:
                        for name,k in e.address[1]:s['R_'+name]=([0,1,(1<<64)-7,0x345601][seed%4],64)
                        a=(e.address[0]+sum(s['R_'+name][0]*k for name,k in e.address[1]))&MASK64
                        for i in range(-2,18):s['V_MEM64'][0][(a+i)&MASK64]=(seed*23+i*47)&255
                    expected=copy.deepcopy(s);oracle(e,expected);execute(tree,s)
                    self.assertEqual(s,expected,(kind,r['assembly'],seed));comparisons+=1
        self.assertEqual(immediates,set(range(256)))
        print('PASS',comparisons,'byte-oracle comparisons; every defined YMM/GPR/flag/memory cell and byte frame')

    def test_raw_graph_mutations(self):
        tested=0
        for r in rows('synthetic')+rows('actual'):
            if not r['assembly'].startswith('PALIGNR XMM'):continue
            def reject(b):
                nonlocal tested
                with self.assertRaises(Unsupported,msg=(r['assembly'],b)):ShuffleLifter(Language([b])).instruction(instruction(b))
                tested+=1
            b=copy.deepcopy(r);b['bytes']=b['bytes'][:-2]+f'{(int(b["bytes"][-2:],16)+1)&255:02x}';reject(b)
            for i,op in enumerate(r['ops']):
                for mode in ('arity','width','opcode','operand'):
                    b=copy.deepcopy(r);o=b['ops'][i]
                    if mode=='arity':o['inputs'].append(copy.deepcopy(o['inputs'][0]))
                    if mode=='width':o['output']['size']=64
                    if mode=='opcode':o['code']='CALLOTHER'
                    if mode=='operand':o['inputs'][-1]['offset']^=1
                    reject(b)
            b=copy.deepcopy(r);b['ops'].pop();reject(b)
            b=copy.deepcopy(r);b['ops'].append(copy.deepcopy(b['ops'][-1]));reject(b)
        print('PASS',tested,'encoding/DAG/arity/width/userop mutations')

    def test_snapshot_unique_metadata_and_footprint_rejections(self):
        rr=rows('synthetic')
        for name in ('PALIGNR XMM3,XMM3,0x1', 'PALIGNR XMM15,xmmword ptr [RDI + RCX*0x2 + -0x11],0x1'):
            r=next(r for r in rr if r['assembly']==name)
            for mode in ('early-write','overlap','uninitialized','upper-write','metadata','dead','missing-input'):
                b=copy.deepcopy(r)
                if mode=='early-write':b['ops'].insert(0,copy.deepcopy(b['ops'][-1]))
                if mode=='overlap':b['ops'][1]['output']['offset']=b['ops'][0]['output']['offset']+1
                if mode=='uninitialized':b['ops'][1]['inputs'][0]['offset']+=1
                if mode=='upper-write':b['ops'][-1]['output']['offset']+=16
                if mode=='metadata':b['ops'][-1]['output']['base']='ZMM16'
                if mode=='dead':
                    o=copy.deepcopy(b['ops'][0]);o['output']['offset']=0x200000;b['ops'].insert(0,o)
                if mode=='missing-input':b['ops'][0]['inputs'].pop()
                with self.assertRaises(Unsupported,msg=(name,mode)):ShuffleLifter(Language([b])).instruction(instruction(b))

    def test_strict_encoding_and_unselected_forms(self):
        rr=rows('synthetic');r=next(r for r in rr if r['assembly']=='PALIGNR XMM1,XMM2,0x1')
        for prefix in ('f0','f2','f3','67','2e','66'):
            b=copy.deepcopy(r);b['bytes']=prefix+b['bytes']
            with self.assertRaises(Unsupported):ShuffleLifter(Language([b])).instruction(instruction(b))
        for raw in ('0f3a0fca01','66480f3a0fca01','66400f3a0fca01','66420f3a0fca01','660f3800ca','660f3a0fca','660f3a0fca0100','660f3a0fd101'):
            b=copy.deepcopy(r);b['bytes']=raw
            with self.assertRaises(Unsupported):ShuffleLifter(Language([b])).instruction(instruction(b))
        # Every assembled PSHUFB/VPSHUFB, VEX PALIGNR, MMX and masked EVEX form
        # is rejected. High-bit-zero/low-index/duplicate PSHUFB controls never
        # enter this profile; there is no PSHUFB semantic claim.
        rejected=0
        for r in rr:
            if r['assembly'].startswith(('RET','PALIGNR XMM')):continue
            with self.assertRaises(Unsupported):ShuffleLifter(Language([r])).instruction(instruction(r))
            rejected+=1
        # Pinned Ghidra underdecodes this deliberately unsupported EVEX form,
        # leaving an ADC suffix. Both are rejected; never accept that boundary.
        self.assertEqual(rejected,8)
        # Old copy profile still rejects all new forms, scalar/move behavior unchanged.
        for r in rr:
            if r['assembly'].startswith('PALIGNR XMM'):
                with self.assertRaises(Unsupported):CopyLifter(Language([r])).instruction(instruction(r))
        for kind in ('actual','synthetic'):
            old=json.loads((REPO/f'notes/e26-x86-sse-avx-lowering/{kind}-raw.json').read_text())
            for r in old:
                try:expected=CopyLifter(Language([r])).instruction(instruction(r))
                except Unsupported:continue
                self.assertEqual(expected,ShuffleLifter(Language([r])).instruction(instruction(r)))

    def test_pins_and_artifacts(self):
        import sys,hashlib
        sys.path.insert(0,str(REPO/'Examples/claude/inventory/e01-x86-inventory'))
        from inventory import ELF
        sources={'synthetic':NOTES/'fixture/shuffles.so','actual':Path('/home/charles/code/friends/.toolchains/e01-x86-inventory/runtime/lib/x86_64-linux-gnu/libc.so.6')}
        self.assertEqual(hashlib.sha256(sources['actual'].read_bytes()).hexdigest(),'9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9')
        for kind,path in sources.items():
            elf=ELF(path)
            for r in rows(kind):
                data=bytes.fromhex(r['bytes']);self.assertEqual(elf.read(int(r['address'],16)-0x100000,len(data)),data)
        for directory in ('x64_shuffle_fixture','x64_shuffle_pinned'):
            for p in (REPO/'Examples/claude/lifter'/directory).glob('*.pcode.json'):
                rr=json.loads(p.read_text());v=p.with_suffix('').with_suffix('.v').read_text();l=ShuffleLifter(Language(rr))
                for r in rr:self.assertIn('\t'+l.instruction(instruction(r))+'\n)',v)
                receipt=json.loads((p.parent/'SUCCESS.json').read_text());record=receipt['records'][0]
                self.assertEqual(hashlib.sha256(v.encode()).hexdigest(),record['output_sha256'])
                for f,sha in receipt['implementation_sha256'].items():self.assertEqual(hashlib.sha256((REPO/'tools/ghidra-lifter'/f).read_bytes()).hexdigest(),sha)
                self.assertEqual(record['coverage'],'selected-function-extents' if directory.endswith('fixture') else 'isolated-instruction-fixtures')

    def test_receipt_failures(self):
        spec=importlib.util.spec_from_file_location('shuffle_supervisor',Path(__file__).with_name('lift-x64-shuffle.py'))
        m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
        with tempfile.TemporaryDirectory(dir=STATE/'tmp') as tmp:
            stage=Path(tmp);v=stage/'e34_align_amd64.v';p=stage/'e34_align_amd64.pcode.json'
            v.write_text('partial')
            with self.assertRaises(FileNotFoundError):m.validate_receipt(stage,'fresh',['align'],'elf','synthetic','shuffle128')
            p.write_text('[]')
            receipt=dict(token='fresh',records=[dict(symbol='align',output=v.name,output_sha256=m.digest(v),pcode_sha256=m.digest(p),instructions=1,coverage='selected-function-extents')],elf_sha256='elf',source_kind='synthetic',profile='shuffle128',language='x86:LE:64:default',addressing='global')
            def check(r):
                (stage/'SUCCESS.json').write_text(json.dumps(r));return m.validate_receipt(stage,'fresh',['align'],'elf','synthetic','shuffle128')
            check(receipt)
            for field,val in [('token','stale'),('records',[]),('source_kind','glibc'),('profile','copy256'),('elf_sha256','bad')]:
                r=copy.deepcopy(receipt);r[field]=val
                with self.assertRaises(ValueError):check(r)
            p.write_text('corrupt')
            with self.assertRaises(ValueError):check(receipt)
            p.write_text('[]');(stage/'extra.v').write_text('partial')
            with self.assertRaises(ValueError):check(receipt)

if __name__=='__main__':unittest.main(verbosity=2)
