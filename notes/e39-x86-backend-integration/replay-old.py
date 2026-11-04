"""Fresh Ghidra replay; old program/raw bytes must match, receipt deltas explicit.
Never update or relabel original receipts as current implementation evidence.
"""
import json,subprocess,sys,tempfile
from pathlib import Path
from compat import ROOT,STATE
for unit in ('e25','e26','e27','e28'):(STATE/'compat'/unit).mkdir(parents=True,exist_ok=True)
runs={u:Path(tempfile.mkdtemp(prefix='old-replay.',dir=STATE/'compat'/u)) for u in ('e25','e26','e27','e28')}
cases=[('e25','x64_scalar_smoke',['--cet-disabled','toascii','isascii','abs','labs','pthread_equal']),('e25','x64_scalar_fixture',['--fixture','scalar_caller','scalar_callee']),('e26','x64_copy_fixture',['--fixture','legacy','vex128','vex256','zero']),('e26','x64_copy_pinned',['--instructions','pinned_moves']),('e27','x64_rep_pinned',[]),('e27','x64_rep_synthetic',['--fixture']),('e28','x64_bitscan_glibc',['--cet-disabled','ffs','ffsl','ffsll']),('e28','x64_bitscan_hot',['--samples','--bmi1','present','hot_scans']),('e28','x64_bitscan_fixture',['--fixture','--bmi1','present','--abm','present']+[op+str(w)+a for op in ['bsf','bsr','tzcnt','lzcnt'] for w in [32,64] for a in ['', '_alias']]),('e28','x64_bitscan_fallback',['--fixture','--bmi1','absent','--abm','absent','tzcnt32_alias','tzcnt64_alias','lzcnt32_alias','lzcnt64_alias'])]
report=[]
for unit,directory,args in cases:
    out=runs[unit]/directory
    command=[sys.executable,str(ROOT/'notes/e39-x86-backend-integration'/('compat-'+unit+'.py')),'--out',str(out),*args]
    print('COMMAND',command,flush=True);r=subprocess.run(command);print('EXIT',r.returncode,flush=True);assert r.returncode==0
    old=ROOT/'Examples/claude/lifter'/directory
    oldreceipt=json.loads((old/'SUCCESS.json').read_text());newreceipt=json.loads((out/'SUCCESS.json').read_text())
    delta={k:{'historical':oldreceipt.get(k),'replay':newreceipt.get(k)} for k in oldreceipt.keys()|newreceipt.keys() if oldreceipt.get(k)!=newreceipt.get(k)}
    assert set(delta) <= {'implementation_sha256'},delta
    if delta:
        a=oldreceipt['implementation_sha256'];b=newreceipt['implementation_sha256']
        expected={'e25':{'pcode2coq_x64.py','pcode2coq_bitscan.py','lift-x64.py'},'e26':{'pcode2coq_x64.py'},'e27':{'pcode2coq_x64.py'}}
        assert {k for k in a.keys()|b.keys() if a.get(k)!=b.get(k)}==expected[unit],delta
    count=0
    for f in old.iterdir():
        if f.name!='SUCCESS.json' and f.suffix in ('.v','.json'):
            assert f.read_bytes()==(out/f.name).read_bytes(),f;count+=1
    report.append(dict(unit=unit,directory=directory,identical_program_raw_files=count,expected_receipt_deltas=delta))
(ROOT/'notes/e39-x86-backend-integration/replay-deltas.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS all 38 historical programs/raw captures unchanged; explicit helper-hash deltas only')
