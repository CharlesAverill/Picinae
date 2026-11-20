#!/usr/bin/env python3
"""Fresh strict replay of exact target outcomes; no new function map is copied."""
import argparse,json,re
from validate import STATE,NOTES,lift,REPO
p=argparse.ArgumentParser()
p.add_argument('--run',required=True)
a=p.parse_args()
assert re.fullmatch('[A-Za-z0-9_-]+',a.run)
run=STATE/a.run
run.mkdir(parents=True,exist_ok=False)
for record in json.loads((NOTES/'TARGETS.json').read_text()):
    name=record['symbol']
    ok=record['status']=='supported-closed-map'
    raw,result=lift(run,name,[name],expected=0 if ok else 1)
    if ok:
        oldroot=REPO/'Examples/claude/lifter/scalar_ccmp'
        old='e11_'+name+'_arm8'; new='e30_'+name+'_arm8'
        assert (raw/(old+'.v')).read_text().replace(old,new)==(oldroot/(new+'.v')).read_text()
        assert (raw/(old+'.pcode.json')).read_bytes()==(oldroot/(new+'.pcode.json')).read_bytes()
        print('PASS unchanged complete e30 reference map',name)
    else:
        reason=re.sub(r'; no output accepted; Ghidra log:.*','',result.stdout.strip())
        assert reason==record['reason'],(name,reason)
        print('PASS exact frontier and no-output failure',name)
