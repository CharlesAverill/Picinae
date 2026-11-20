#!/usr/bin/env python3
"""Finite byte/reference comparisons and adversarial encoding/DAG checks.
These tests validate emitted IL by a separate interpreter, not target execution
or a functional correctness proof of an instruction/function.
"""
import copy
import importlib.util
import json
from pathlib import Path
import random
import re
from types import SimpleNamespace
import tempfile
import unittest
from test_x64 import Language, instruction, state, Insn, load_rows
from test_scalar import parse
from pcode2coq_x64 import X64Lifter, Unsupported
from pcode2coq_x64_copy import CopyLifter, GPR

REPO=Path(__file__).resolve().parents[2]
NOTES=REPO/'notes/e26-x86-sse-avx-lowering'
ARTIFACTS=REPO/'Examples/claude/lifter'
MASK=(1<<256)-1


def rows(kind):return json.loads((NOTES/(kind+'-raw.json')).read_text())


def vector_state(seed):
    rng=random.Random(seed);s=state()
    for n in range(16):s[f'R_YMM{n}']=(rng.getrandbits(256),256)
    for reg in GPR:s['R_'+reg]=(0x10000000000+rng.randrange(0,0x10000)*32,64)
    return s


def value(tree,s):
    op,*args=tree
    if op=='word':return args[0] % (1<<args[1]),args[1]
    if op=='var':return s[args[0]]
    if op=='cast':
        kind,w,exp=args;assert kind=='CAST_UNSIGNED'
        return value(exp,s)[0] % (1<<w),w
    if op=='extract':
        hi,lo,exp=args;return (value(exp,s)[0]>>lo) % (1<<(hi-lo+1)),hi-lo+1
    if op=='concat':
        a,wa=value(args[0],s);b,wb=value(args[1],s);return (a<<wb)|b,wa+wb
    if op=='bin':
        name,a,b=args;x,w=value(a,s);y,wy=value(b,s);assert w==wy
        assert name in ('OP_PLUS','OP_TIMES')
        return ((x+y) if name=='OP_PLUS' else (x*y)) % (1<<w),w
    if op in ('load','store'):
        mem,aw=value(args[0],s);address,w=value(args[1],s);assert w==64
        if op=='load':
            n=args[2];return sum(mem.get((address+i) % (1<<w),0)<<(8*i) for i in range(n)),8*n
        data,dw=value(args[2],s);n=args[3];assert dw==n*8
        result=mem.copy();result.update({(address+i) % (1<<w):(data>>(8*i))&255 for i in range(n)})
        return result,aw
    raise AssertionError(tree)


def execute(tree,s):
    op,*args=tree
    if op=='seq':
        for t in args[0]:execute(t,s)
    elif op=='move':s[args[0]]=value(args[1],s)
    else:raise AssertionError(tree)


def assembly_reference(assembly):
    name,*operands=assembly.split(' ',1)
    if name=='VZEROUPPER':return SimpleNamespace(mnemonic=name,address=None)
    dst,src=operands[0].split(',')
    memory=dst if '[' in dst else src if '[' in src else None
    address=None
    if memory:
        inner=memory.split('[',1)[1].split(']',1)[0]
        disp=0;terms=[]
        for term in inner.split('+'):
            term=term.strip()
            if term.startswith('R'):
                parts=term.split('*');terms.append((parts[0],int(parts[1],0) if len(parts)>1 else 1))
            else:disp+=int(term,0)
        address=(disp,tuple(terms))
    reg=lambda x: int(re.fullmatch(r'[XY]MM([0-9]+)',x.strip()).group(1))
    return SimpleNamespace(mnemonic=name,vex=name.startswith('V'),width=32 if 'YMM' in assembly or 'ymmword' in assembly else 16,dst=None if '[' in dst else reg(dst),src=None if '[' in src else reg(src),address=address)


def reference(e,s):
    # Independent byte-array transfer oracle: address modulo 2^64, read all
    # source bytes before any write, retain exactly the architectural footprint.
    if e.mnemonic=='VZEROUPPER':
        for n in range(16):s[f'R_YMM{n}']=(s[f'R_YMM{n}'][0]&((1<<128)-1),256)
        return
    mem=s['V_MEM64'][0]
    if e.address is not None:
        disp,terms=e.address
        address=(disp+sum(s['R_'+r][0]*scale for r,scale in terms)) % (1<<64)
    if e.src is None: data=bytes(mem.get((address+i) % (1<<64),0) for i in range(e.width))
    else:data=s[f'R_YMM{e.src}'][0].to_bytes(32,'little')[:e.width]
    if e.dst is None:
        mem.update({(address+i) % (1<<64):v for i,v in enumerate(data)})
    else:
        old=s[f'R_YMM{e.dst}'][0].to_bytes(32,'little')
        result=data+(bytes(16) if e.vex else old[16:]) if e.width==16 else data
        s[f'R_YMM{e.dst}']=(int.from_bytes(result,'little'),256)


class Tests(unittest.TestCase):
    def test_all_actual_and_synthetic_finite_semantics(self):
        comparisons=0
        for kind in ('actual','synthetic'):
            rr=rows(kind);l=CopyLifter(Language(rr))
            for r in rr:
                if r['assembly'].startswith(('RET','PSHUFB')) or r['bytes'].startswith('62'):continue
                raw=bytes.fromhex(r['bytes']);e=assembly_reference(r['assembly'])
                tree=parse(l.instruction(instruction(r)))
                for seed in range(80):
                    s=vector_state(seed)
                    # Wraparound, aligned and unaligned addresses. Faults are
                    # outside the model; these are IL address-width tests.
                    if e.address:
                        for name,scale in e.address[1]:s['R_'+name]=([0,(1<<64)-16,0x123456789a00][seed%3],64)
                        address=(e.address[0]+sum(s['R_'+r][0]*k for r,k in e.address[1])) % (1<<64)
                        mem=s['V_MEM64'][0]
                        for i in range(-2, e.width+2):mem[(address+i) % (1<<64)]=(i*37+seed)&255
                    expected=copy.deepcopy(s);reference(e,expected);execute(tree,s)
                    self.assertEqual(s,expected,(kind,r['assembly'],seed));comparisons+=1
        print('finite instruction/reference comparisons:',comparisons)

    def test_encoding_and_complete_raw_graph_rejections(self):
        rr=rows('synthetic');lang=Language(rr);l=CopyLifter(lang)
        good=next(r for r in rr if r['assembly']=='VMOVDQU XMM1,XMM0')
        # Valid mnemonic never overrides exact prefixes/map/L/vvvv/operand fields.
        for raw in ['62f17e086fc8','c5f26fc8','c5fe6fc8','c4e2796fc8','c4e1fa6fc8','f0c5fa6fc8','67c5fa6fc8','c5fa6fc800','c5fa6f','f3f30f6fc8','c5fa7fc8','660f6fc8']:
            bad=copy.deepcopy(good);bad['bytes']=raw
            with self.assertRaises(Unsupported,msg=raw):l.instruction(instruction(bad))
        for r in rows('actual'):
            if r['bytes'].startswith('62'):
                with self.assertRaises(Unsupported):CopyLifter(Language([r])).instruction(instruction(r))
        for source in rr:
            if source['assembly'].startswith(('RET','PSHUFB')):continue
            bad=copy.deepcopy(source);bad['ops'].append(dict(code='CALLOTHER',output=None,inputs=[]))
            with self.assertRaises(Unsupported):l.instruction(instruction(bad))
            bad=copy.deepcopy(source);bad['ops'].pop()
            with self.assertRaises(Unsupported):l.instruction(instruction(bad))
        # A projected extension cannot read ZMM data or hide a mask/flag/GPR write.
        for size in (0,8,32,64):
            bad=copy.deepcopy(good);bad['ops'][0]['inputs'][0]['size']=size
            with self.assertRaises(Unsupported):l.instruction(instruction(bad))
        bad=copy.deepcopy(good);bad['ops'][0]['code']='COPY'
        with self.assertRaises(Unsupported):l.instruction(instruction(bad))
        bad=copy.deepcopy(good);bad['ops'][0]['output']['offset']+=64
        with self.assertRaises(Unsupported):l.instruction(instruction(bad))
        lane=next(r for r in rr if r['assembly'].startswith('MOVUPS XMM2,'))
        for index in range(2,6):
            bad=copy.deepcopy(lane);bad['ops'][index]['inputs'][1]['offset']^=4
            with self.assertRaises(Unsupported):l.instruction(instruction(bad))
        load=next(r for r in rr if r['assembly'].startswith('VMOVDQA XMM9,'))
        for mutate in ('address','space','width','order','unique','opmask'):
            bad=copy.deepcopy(load)
            if mutate=='address':bad['ops'][0]['inputs'][0]['offset']+=1
            if mutate=='space':bad['ops'][3]['inputs'][0]['offset']+=1
            if mutate=='width':bad['ops'][3]['output']['size']=32
            if mutate=='order':bad['ops'][0],bad['ops'][1]=bad['ops'][1],bad['ops'][0] # independent is valid; force undefined input instead
            if mutate=='order':bad['ops'][0],bad['ops'][3]=bad['ops'][3],bad['ops'][0]
            if mutate=='unique':bad['ops'][2]['output']['offset']=bad['ops'][0]['output']['offset']+4
            if mutate=='opmask':bad['ops'][0]['inputs'][1].update(register='K0',base='K0',base_width=64)
            with self.assertRaises(Unsupported,msg=mutate):CopyLifter(Language([bad])).instruction(instruction(bad))
        nt=next(r for r in rr if r['assembly'].startswith('VMOVNTDQ ymmword'))
        for index in (0,1):
            bad=copy.deepcopy(nt)
            if index==0:bad['ops'][0]['inputs'][0]['offset']+=1
            else:bad['ops'][1]['inputs'][2]['offset']+=16
            with self.assertRaises(Unsupported):l.instruction(instruction(bad))
        zero=next(r for r in rr if r['assembly']=='VZEROUPPER')
        for index in range(len(zero['ops'])):
            bad=copy.deepcopy(zero);bad['ops'][index]['inputs'][0]['offset']=1
            with self.assertRaises(Unsupported):l.instruction(instruction(bad))

    def test_scalar_profile_unchanged_and_copy_is_opt_in(self):
        for r in rows('synthetic'):
            if r['assembly'].startswith(('RET','PSHUFB')) or r['bytes'].startswith('62'):continue
            with self.assertRaises(Unsupported):X64Lifter(Language([r])).instruction(instruction(r))
        for dirname in ('x64_scalar_smoke','x64_scalar_fixture'):
            rr=list(load_rows(dirname).values());lang=Language(rr)
            for r in rr:
                self.assertEqual(X64Lifter(lang,True).instruction(instruction(r)),CopyLifter(lang,True).instruction(instruction(r)))
        for cet in (False,True):
            l=CopyLifter(Language(),cet);i=Insn('ENDBR64',raw=bytes.fromhex('f30f1efa'))
            if cet:self.assertEqual(l.instruction(i),'Nop')
            else:
                with self.assertRaises(Unsupported):l.instruction(i)

    def test_exact_artifact_reemission_and_pinned_bytes(self):
        import sys
        sys.path.insert(0,str(REPO/'Examples/claude/inventory/e01-x86-inventory'))
        from inventory import ELF
        selection=json.loads((NOTES/'actual-selection.json').read_text())
        inventory=json.loads((REPO/'Examples/claude/inventory/e01-x86-inventory/generated/inventory.json').read_text())
        for r in selection:
            a=int(r['elf_address'],16)
            self.assertTrue(any('copy' in e['scope'] and int(e['elf_address'],16)<=a<int(e['end_exclusive'],16) for e in inventory['extents']))
        count=0
        for directory in ('x64_copy_fixture','x64_copy_pinned'):
            for p in (ARTIFACTS/directory).glob('*.pcode.json'):
                count+=1
                rr=json.loads(p.read_text());self.assertTrue(rr);l=CopyLifter(Language(rr));v=p.with_suffix('').with_suffix('.v').read_text()
                for r in rr:self.assertIn('\t'+l.instruction(instruction(r))+'\n)',v)
        self.assertEqual(count,5)
        elf=ELF(NOTES/'fixture/moves.so')
        for r in rows('synthetic'):
            raw=bytes.fromhex(r['bytes']);self.assertEqual(elf.read(int(r['address'],16)-0x100000,len(raw)),raw)

        import hashlib
        libc=Path('/home/charles/code/friends/.toolchains/e01-x86-inventory/runtime/lib/x86_64-linux-gnu/libc.so.6')
        self.assertEqual(hashlib.sha256(libc.read_bytes()).hexdigest(),'9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9')
        elf=ELF(libc)
        self.assertEqual(len(selection),35)
        for r in rows('actual'):
            raw=bytes.fromhex(r['bytes']);self.assertEqual(elf.read(int(r['address'],16)-0x100000,len(raw)),raw)

    def test_e26_receipt_rejects_partial_stale_and_mismatch(self):
        spec=importlib.util.spec_from_file_location('copy_supervisor',Path(__file__).with_name('lift-x64-copy.py'))
        m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
        with tempfile.TemporaryDirectory() as tmp:
            stage=Path(tmp);v=stage/'e26_legacy_amd64.v';p=stage/'e26_legacy_amd64.pcode.json'
            v.write_text('partial')
            with self.assertRaises(FileNotFoundError):m.validate_receipt(stage,'fresh',['legacy'],'elf','synthetic','copy256')
            p.write_text('[]')
            receipt=dict(token='fresh',records=[dict(symbol='legacy',output=v.name,output_sha256=m.digest(v),pcode_sha256=m.digest(p),instructions=1,coverage='selected-function-extents')],elf_sha256='elf',source_kind='synthetic',profile='copy256',language='x86:LE:64:default',addressing='global')
            def check(r):
                (stage/'SUCCESS.json').write_text(json.dumps(r));return m.validate_receipt(stage,'fresh',['legacy'],'elf','synthetic','copy256')
            check(receipt)
            for field,val in [('token','stale'),('records',[]),('source_kind','glibc'),('profile','strict'),('elf_sha256','bad')]:
                r=copy.deepcopy(receipt);r[field]=val
                with self.assertRaises(ValueError):check(r)
            p.write_text('corrupt')
            with self.assertRaises(ValueError):check(receipt)
            p.write_text('[]');(stage/'extra.v').write_text('partial')
            with self.assertRaises(ValueError):check(receipt)


if __name__=='__main__':unittest.main(verbosity=2)
