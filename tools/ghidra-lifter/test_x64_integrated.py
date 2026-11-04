"""Composition/state/feature/provenance regressions using reviewed raw captures."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from pcode2coq_x64_integrated import IntegratedLifter,Unsupported
from x64_provenance import dependency_manifest
from test_x64 import Language,instruction
from test_x64_copy import rows as copy_rows
from test_bitscan import RAW as scan_rows
REPO=Path(__file__).resolve().parents[2]
ART=REPO/'Examples/claude/lifter'
REP=json.loads((ART/'x64_rep_synthetic/e27_rep_amd64.pcode.json').read_text())
SCALAR=json.loads((ART/'x64_scalar_fixture/e25_scalar_callee_amd64.pcode.json').read_text())

class Tests(unittest.TestCase):
    def test_interleaving_reuse_failure_and_features(self):
        moves=[r for r in copy_rows('synthetic') if not r['assembly'].startswith(('RET','PSHUFB')) and not r['bytes'].startswith('62')]
        scans=[r for r in scan_rows if r['assembly'].split()[0] in ('BSF','BSR','TZCNT','LZCNT') and r.get('function') not in ('reject16','rejectmem')]
        rr=moves+REP+scans+SCALAR;lang=Language(rr)
        for bmi in (None,'present','absent'):
            for abm in (None,'present','absent'):
                config=dict(bmi1=bmi,abm=abm,cet_disabled=True)
                l=IntegratedLifter(lang,**config)
                for i in range(max(len(moves),len(scans))):
                    for r in (moves[i%len(moves)],REP[i%len(REP)],scans[i%len(scans)],SCALAR[i%len(SCALAR)]):
                        missing=(r['assembly'].startswith('TZCNT') and bmi is None) or (r['assembly'].startswith('LZCNT') and abm is None)
                        if missing:
                            with self.assertRaises(Unsupported):l.instruction(instruction(r))
                        else:
                            self.assertEqual(l.instruction(instruction(r)),IntegratedLifter(lang,**config).instruction(instruction(r)))
                        self.assertEqual((l.temps,l.ranges,l.initialized),({},[],set()))
                    bad=copy.deepcopy(moves[i%len(moves)]);bad['ops'].append(dict(code='CALLOTHER',output=None,inputs=[]))
                    with self.assertRaises(Unsupported):l.instruction(instruction(bad))
                    self.assertEqual((l.temps,l.ranges,l.initialized),({},[],set()))
        for kwargs in ({'bmi1':'yes'},{'abm':True},{'cet_disabled':'yes'}):
            with self.assertRaises(Unsupported):IntegratedLifter(lang,**kwargs)

    def test_closed_mixed_program_against_sequential_reference(self):
        from unittest.mock import patch
        import test_scalar as evaluator
        from test_x64 import run
        from test_x64_copy import vector_state
        path=ART/'x64_integrated_fixture/e39_mixed_amd64.pcode.json'
        rows=json.loads(path.read_text());lang=Language(rows)
        mask=(1<<64)-1
        original_evaluate=evaluator.evaluate
        def modular(tree,s):
            op,*args=tree
            if op=='load':
                mem,_=modular(args[0],s);a,_=modular(args[1],s);n=args[2]
                return sum(mem.get((a+i)&mask,0)<<(8*i) for i in range(n)),8*n
            if op=='store':
                mem,_=modular(args[0],s);a,_=modular(args[1],s);data,_=modular(args[2],s);n=args[3]
                mem=mem.copy();mem.update({(a+i)&mask:(data>>(8*i))&255 for i in range(n)})
                return mem,'memory'
            return original_evaluate(tree,s)
        comparisons=0
        for bmi in ('present','absent'):
          for abm in ('present','absent'):
            l=IntegratedLifter(lang,cet_disabled=True,bmi1=bmi,abm=abm)
            program={int(r['address'],16):(len(bytes.fromhex(r['bytes'])),evaluator.parse(l.instruction(instruction(r)))) for r in rows}
            for n in (0,1,3,8):
              for df in (0,1):
                step=1-2*df
                for d,src in ((0x200,0x100),(0x100,0x100),(0x101,0x100),(0x100,0x101),((-step*n)&mask,0x100)):
                  for unknown in (0,mask):
                    state=vector_state(n);state['_unknown']=unknown
                    for r,v in [('RDI',d),('RSI',src),('RDX',n),('RAX',0x123456789abcdef0),('RSP',0x10000)]:state['R_'+r]=(v,64)
                    state['R_DF']=(df,1)
                    for a in range(0x80,0x240):state['V_MEM64'][0][a]=a&255
                    state['V_MEM64'][0].update({0x10000+i:(0xdeadbeef>>(8*i))&255 for i in range(8)})
                    before=copy.deepcopy(state);mem=before['V_MEM64'][0].copy()
                    vector=sum(mem.get((src+i)&mask,0)<<(8*i) for i in range(16))
                    dd,ss=d,src
                    for _ in range(n):mem[dd]=mem.get(ss,0);dd=(dd+step)&mask;ss=(ss+step)&mask
                    ctz=lambda x: (x&-x).bit_length()-1 if x else 64
                    flags={f:unknown&1 for f in ('CF','OF','SF','AF','PF')}
                    if dd:
                        dd=ctz(dd)
                        ss=ctz(ss) if ss or bmi=='present' else unknown
                        x=dd;dd=64-x.bit_length() if abm=='present' else x.bit_length()-1 if x else unknown
                        flags['ZF']=int(dd==0) if abm=='present' else int(x==0)
                        if abm=='present':flags['CF']=int(x==0)
                    else:
                        dd=unknown
                        for _ in range(n):
                            for i in range(8):mem[(dd+i)&mask]=(before['R_RAX'][0]>>(8*i))&255
                            dd=(dd+8*step)&mask
                        x=dd;dd=x.bit_length()-1 if x else unknown;flags['ZF']=int(x==0)
                    with patch.object(evaluator,'evaluate',modular):self.assertEqual(run(program,min(program),state),0xdeadbeef)
                    self.assertEqual(state['V_MEM64'][0],mem)
                    for r,v in [('RDI',dd),('RSI',ss),('RCX',0),('RSP',0x10008)]:self.assertEqual(state['R_'+r],(v,64))
                    for f,v in flags.items():self.assertEqual(state['R_'+f],(v,1))
                    for i in range(16):self.assertEqual(state['R_YMM'+str(i)],(vector if i in (0,1) else before['R_YMM'+str(i)][0]&((1<<128)-1),256))
                    changed={'R_RDI','R_RSI','R_RCX','R_RSP','R_RIP','V_MEM64',*[f'R_{f}' for f in flags],*[f'R_YMM{i}' for i in range(16)]}
                    for k,v in before.items():
                        if k not in changed:self.assertEqual(state[k],v,k)
                    comparisons+=1
        print('mixed program/reference comparisons:',comparisons)

    def test_dependency_closure_and_receipt_rejection(self):
        closure=dependency_manifest(REPO,'synthetic')
        required=['pcode2coq_x64_integrated.py','pcode2coq_x64_copy.py','pcode2coq_x64_rep.py','pcode2coq_x64.py','pcode2coq_scalar.py','pcode2coq_bitscan.py','x64_provenance.py','lift-x64-integrated.py','x64_integrated_headless.py']
        self.assertTrue(all('tools/ghidra-lifter/'+p in closure for p in required))
        self.assertIn('Examples/claude/inventory/e01-x86-inventory/retrieve.py',closure)
        spec=importlib.util.spec_from_file_location('integrated_supervisor',Path(__file__).with_name('lift-x64-integrated.py'))
        m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
        with tempfile.TemporaryDirectory() as tmp:
            stage=Path(tmp);(stage/'e39_mixed_amd64.v').write_text('program');(stage/'e39_mixed_amd64.pcode.json').write_text('[]')
            profile='integrated-cet-disabled;bmi1=present;abm=absent'
            from x64_provenance import feature_profile
            receipt=dict(token='fresh',scope='closed-selected-function-extents',elf_sha256='elf',source_kind='synthetic',language='x86:LE:64:default',addressing='global',profile=profile,features=feature_profile(profile),dependencies=closure,semantics='scalar-copy256-rep-scan-sequential-v1',records=[dict(symbol='mixed',output='e39_mixed_amd64.v',output_sha256=m.digest(stage/'e39_mixed_amd64.v'),pcode_sha256=m.digest(stage/'e39_mixed_amd64.pcode.json'),instructions=1)])
            def check(r):
                (stage/'SUCCESS.json').write_text(json.dumps(r));return m.validate_receipt(stage,'fresh',['mixed'],'elf','synthetic',profile)
            check(receipt)
            for key in closure:
                bad=copy.deepcopy(receipt);del bad['dependencies'][key]
                with self.assertRaises(ValueError):check(bad)
            for field,val in [('token','stale'),('records',[]),('profile','strict'),('features',{}),('scope','instruction-fragments'),('semantics','other'),('elf_sha256','other')]:
                bad=copy.deepcopy(receipt);bad[field]=val
                with self.assertRaises(ValueError):check(bad)
            (stage/'extra.v').write_text('partial')
            with self.assertRaises(ValueError):check(receipt)

if __name__=='__main__':unittest.main(verbosity=2)
