#!/usr/bin/env python3
import os,sys,subprocess,tempfile
from pathlib import Path
state=Path('/home/charles/code/friends/.toolchains/e28-x86-bitscan-lowering')
root=Path(tempfile.mkdtemp(prefix='negative.',dir=state))
base=[sys.executable,'tools/ghidra-lifter/lift-bitscan.py']
for i,args in enumerate([
    ['ffs'],
    ['--fixture','bsf32','tzcnt32'],
    ['--fixture','--bmi1','present','bsf32','lzcnt32'],
    ['--fixture','--bmi1','present','--abm','present','bsf32','reject16'],
    ['--fixture','--bmi1','present','--abm','present','bsf32','rejectmem'],
    ['--samples','hot_scans'],
]):
    out=root/str(i)
    cmd=base+['--out',str(out)]+args
    print('COMMAND',cmd,flush=True)
    r=subprocess.run(cmd,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    print('EXIT',r.returncode,flush=True)
    assert r.returncode==1 and not out.exists() and not list(root.glob('.e28-stage-*'))
for n,symlink in [('existing',False),('broken',True)]:
    out=root/n
    if symlink:out.symlink_to(root/'absent')
    else:out.mkdir()
    r=subprocess.run(base+['--out',str(out),'--cet-disabled','ffs'])
    print(n,'EXIT',r.returncode,flush=True);assert r.returncode==2
print('PASS six actual decoder failures leave no partial publication; existing/symlink destinations reject')
