#!/usr/bin/env python3
"""Real unsupported-prefix/loop batches must leave no accepted or staging output."""
from pathlib import Path
import subprocess,sys,tempfile,os
repo=Path(__file__).resolve().parents[2]
state=Path('/home/charles/code/friends/.toolchains/e27-x86-rep-lowering')
run=Path(tempfile.mkdtemp(prefix='negative.',dir=state))
env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
for name in ['bad_addr32','bad_segment','bad_repne','bad_cmps','bad_scas','bad_duplicate','missing_symbol']:
    out=run/name
    cmd=[sys.executable,str(repo/'tools/ghidra-lifter/lift-x64-rep.py'),'--fixture','--out',str(out),'rep_movsb',name]
    print('COMMAND='+repr(cmd),flush=True)
    r=subprocess.run(cmd,env=env)
    print('EXPECTED_EXIT=1 ACTUAL_EXIT='+str(r.returncode),flush=True)
    assert r.returncode==1 and not out.exists() and not list(run.glob('.e27-stage-*'))
for symlink in (False,True):
    out=run/('link' if symlink else 'existing')
    if symlink:out.symlink_to(run/'absent')
    else:out.mkdir();(out/'sentinel').write_text('unchanged')
    cmd=[sys.executable,str(repo/'tools/ghidra-lifter/lift-x64-rep.py'),'--out',str(out)]
    print('COMMAND='+repr(cmd),flush=True);r=subprocess.run(cmd,env=env)
    print('EXPECTED_EXIT=2 ACTUAL_EXIT='+str(r.returncode),flush=True)
    assert r.returncode==2
    assert out.is_symlink() if symlink else (out/'sentinel').read_text()=='unchanged'
assert not list((state/'projects').glob('lift-*'))
print('PASS mixed supported/unsupported real extraction batches; no partial publication, staging or projects; existing destinations unchanged')
