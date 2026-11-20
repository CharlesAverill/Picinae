#!/usr/bin/env python3
"""Finite emitted-IL checks, raw graph mutation checks, and alias regressions.

Unknown expressions are sampled independently of the reference result. These
checks do not prove the instruction lowering or any function correct.
"""
import copy
import json
import random
import unittest
from test_x64 import Language, instruction, state, parse, execute, run, ARTIFACTS, REPO
from pcode2coq_x64 import X64Lifter, Unsupported
from pcode2coq_bitscan import encoding, SCANS

NOTE=REPO/'notes/e28-x86-bitscan-lowering'
RAW=json.loads((NOTE/'pinned-raw.json').read_text())['rows']+json.loads((NOTE/'fixture-raw.json').read_text())


def config(directory):
    r=json.loads((directory/'SUCCESS.json').read_text())
    cet,bmi1,abm=r['profile'].split(';')
    return dict(cet_disabled=cet=='cet-disabled',bmi1=bmi1.split('=')[1],abm=abm.split('=')[1])


class Tests(unittest.TestCase):
    def test_all_pinned_scan_encodings_and_feature_profiles(self):
        rng=random.Random(28)
        count=0
        for row in RAW:
            if row['assembly'].split()[0] not in SCANS or row.get('function') in ('reject16','rejectmem'):continue
            insn=instruction(row);mnemonic,w,dst,src=encoding(insn)
            for feature in ('present','absent'):
                lifter=X64Lifter(Language(RAW),bmi1=feature,abm=feature)
                text=lifter.instruction(insn);tree=parse(text)
                eff={'TZCNT':'BSF','LZCNT':'BSR'}.get(mnemonic,mnemonic) if feature=='absent' else mnemonic
                inputs=[0,(1<<w)-1]+[1<<i for i in range(w)]+[rng.getrandbits(w) for _ in range(20)]
                for x in inputs:
                    # Both extreme havoc choices also exercise ffs zero paths.
                    for unknown in (0,(1<<64)-1):
                        s=state();s['_unknown']=unknown
                        s[dst]=((1<<64)-1,64);s[src]=(x | (0xabcdef<<32) if w==32 else x,64)
                        for i,f in enumerate(('CF','ZF','OF','SF','AF','PF','DF')):s['R_'+f]=(i%2,1)
                        before=copy.deepcopy(s);execute(tree,s)
                        ctz=(x & -x).bit_length()-1 if x else w
                        clz=w-x.bit_length()
                        expected={'BSF':ctz,'BSR':x.bit_length()-1,'TZCNT':ctz,'LZCNT':clz}[eff]
                        if x or eff in ('TZCNT','LZCNT'):
                            self.assertEqual(s[dst],(expected,64),(mnemonic,eff,w,x))
                        else:
                            self.assertIn('Unknown 64',text)
                            self.assertEqual(s[dst],(unknown,64))
                        zf=int(x==0) if eff in ('BSF','BSR') else int(expected==0)
                        self.assertEqual(s['R_ZF'],(zf,1))
                        cf=unknown&1 if eff in ('BSF','BSR') else int(x==0)
                        self.assertEqual(s['R_CF'],(cf,1))
                        for f in ('OF','SF','AF','PF'):self.assertEqual(s['R_'+f],(unknown&1,1))
                        for key in before:
                            if key not in {dst,'R_ZF','R_CF','R_OF','R_SF','R_AF','R_PF'}:
                                self.assertEqual(s[key],before[key],key)
                        count+=1
        print('finite scan/profile/input/Unknown checks:',count)

    def test_feature_declaration_is_required_and_independent(self):
        for mnemonic in ('TZCNT','LZCNT'):
            row=next(r for r in RAW if r['assembly'].startswith(mnemonic))
            insn=instruction(row)
            for kwargs in ({},{'bmi1':'present'} if mnemonic=='LZCNT' else {'abm':'present'}):
                with self.assertRaisesRegex(Unsupported,'feature profile'):
                    X64Lifter(Language(RAW),**kwargs).instruction(insn)

    def test_every_raw_operation_and_node_is_guarded(self):
        checked=0
        for row in RAW:
            if row['assembly'].split()[0] not in SCANS or row.get('function') in ('reject16','rejectmem'):continue
            lang=Language(RAW)
            def reject(bad):
                with self.assertRaises(Unsupported):X64Lifter(lang,bmi1='present',abm='present').instruction(instruction(bad))
            for i,o in enumerate(row['ops']):
                bad=copy.deepcopy(row);bad['ops'][i]['code']='CALLOTHER';reject(bad)
                for key in ('inputs','output'):
                    values=list(enumerate(o[key])) if key=='inputs' else [(None,o[key])]
                    for j,v in values:
                        if v is None:continue
                        bad=copy.deepcopy(row)
                        target=bad['ops'][i][key][j] if key=='inputs' else bad['ops'][i][key]
                        target['size']=3;reject(bad);checked+=1
                        if v['space']=='const':
                            bad=copy.deepcopy(row);bad['ops'][i][key][j]['offset']^=1;reject(bad);checked+=1
            for i in range(len(row['ops'])):
                bad=copy.deepcopy(row);del bad['ops'][i];reject(bad)
            bad=copy.deepcopy(row);bad['ops']+=bad['ops'][-1:];reject(bad)
            # Unique placement is immaterial, but a changed use/alias is not.
            shifted=copy.deepcopy(row)
            for o in shifted['ops']:
                for v in o['inputs']+[o['output']]:
                    if v and v['space']=='unique':v['offset']+=0x10000000
            l=X64Lifter(lang,bmi1='present',abm='present')
            self.assertEqual(l.instruction(instruction(row)),l.instruction(instruction(shifted)))
        print('mutated node/constant rejection checks:',checked)

    def test_encoding_and_unknown_loop_rejections(self):
        row=next(r for r in RAW if r['assembly'].startswith('BSF EAX'))
        for prefix in ('66','f0','f2','67','64','f3f3','4848','f34866'):
            bad=copy.deepcopy(row);bad['bytes']=prefix+bad['bytes']
            with self.assertRaises(Unsupported):X64Lifter(Language(RAW)).instruction(instruction(bad))
        for suffix in ('90','00'):
            bad=copy.deepcopy(row);bad['bytes']+=suffix
            with self.assertRaises(Unsupported):X64Lifter(Language(RAW)).instruction(instruction(bad))
        for row in RAW:
            if row.get('function') in ('reject16','rejectmem') and row['assembly'].split()[0] in SCANS:
                with self.assertRaises(Unsupported):X64Lifter(Language(RAW)).instruction(instruction(row))
        bad=copy.deepcopy(row);bad['assembly']='MOV EAX,EAX'
        with self.assertRaises(Unsupported):X64Lifter(Language(RAW)).instruction(instruction(bad))

    def test_published_programs_and_ffs_finite_results(self):
        for directory in sorted(ARTIFACTS.glob('x64_bitscan_*')):
            rows={int(r['address'],16):r for p in directory.glob('*.pcode.json') for r in json.loads(p.read_text())}
            lifter=X64Lifter(Language(rows.values()),**config(directory));prog={}
            for a,row in rows.items():
                text=lifter.instruction(instruction(row));prog[a]=(len(bytes.fromhex(row['bytes'])),parse(text))
                for p in directory.glob('*.v'):
                    if f'| {a:#x} =>' in p.read_text():self.assertIn('\t'+text+'\n)',p.read_text())
            if directory.name!='x64_bitscan_glibc':continue
            receipt=json.loads((directory/'SUCCESS.json').read_text())
            for r in receipt['records']:
                w=32 if r['symbol']=='ffs' else 64
                for x in [0,(1<<w)-1]+[1<<i for i in range(w)]:
                    for unknown in (0,12345,(1<<64)-1):
                        s=state();s['_unknown']=unknown;s['R_RDI']=(x,64);s['R_RSP']=(0x10000,64)
                        s['V_MEM64'][0].update({0x10000+i:(0xdeadbeef>>(8*i))&255 for i in range(8)})
                        self.assertEqual(run(prog,int(r['entry'],16),s),0xdeadbeef)
                        self.assertEqual(s['R_RAX'][0],(x&-x).bit_length())


if __name__=='__main__':unittest.main(verbosity=2)
