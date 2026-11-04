#!/usr/bin/env python3
"""Malformed CNEG process failures cannot produce a unit IL output."""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
repo=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(repo/'tools/ghidra-lifter'))
from test_cneg import cases,lower
state=Path('/home/charles/code/friends/.toolchains/e36-arm-cneg/malformed')
state.mkdir(exist_ok=False)
row=cases()[0]
variants=[]
bad=deepcopy(row);next(o for o in bad['ops'] if o['code']=='CBRANCH')['args'][0]['offset']+=4;variants.append(bad)
bad=deepcopy(row);del bad['ops'][-1];variants.append(bad)
bad=deepcopy(row);bad['ops'][0]['args'][0]['offset']+=1;variants.append(bad)
bad=deepcopy(row);bad['bytes']='1f2003d5';variants.append(bad)
bad=deepcopy(row);bad['ops'].append(deepcopy(bad['ops'][-1]));variants.append(bad)
for i,bad in enumerate(variants):
    inp,out=state/f'{i}.json',state/f'{i}.il'
    inp.write_text(json.dumps(bad))
    cmd=[sys.executable,'-c','import sys,json; from pathlib import Path; sys.path.insert(0,sys.argv[1]); from test_cneg import lower; result=lower(json.loads(Path(sys.argv[2]).read_text())); Path(sys.argv[3]).write_text(result)',str(repo/'tools/ghidra-lifter'),str(inp),str(out)]
    print('COMMAND='+json.dumps(cmd),flush=True)
    r=subprocess.run(cmd)
    print('EXIT_CODE='+str(r.returncode),flush=True)
    assert r.returncode==1 and not out.exists()
# Alpha-renaming unique offsets preserves IL deterministically; overlapping
# same-shape temporaries are rejected by the independent range check.
for row in cases()[:16]:
    renamed=deepcopy(row)
    for op in renamed['ops']:
        for v in [op['out'],*op['args']]:
            if v and v['kind']=='unique': v['offset']+=0x100000
    assert lower(renamed)==lower(row)
bad=deepcopy(cases()[6])
uniques={(v['offset'],v['size']) for op in bad['ops'] for v in [op['out'],*op['args']] if v and v['kind']=='unique'}
# Shift whole unique slots to adjacent bytes, keeping expected DAG equality.
slots={key:len(uniques)-1-i for i,key in enumerate(sorted(uniques))}
for op in bad['ops']:
    for v in [op['out'],*op['args']]:
        if v and v['kind']=='unique': v['offset']=slots[v['offset'],v['size']]
try: lower(bad)
except Exception as e:
    assert 'overlapping unique' in str(e),str(e)
else: raise AssertionError('overlap accepted')
print('PASS five malformed subprocess failures/no output, unique-renumber determinism and overlapping-unique rejection')
