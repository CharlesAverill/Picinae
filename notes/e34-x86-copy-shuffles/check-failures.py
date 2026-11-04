#!/usr/bin/env python3
"""Fresh supervisor failures must publish no directory or partial artifact."""
from pathlib import Path
import subprocess,tempfile
state=Path('/home/charles/code/friends/.toolchains/e34-x86-copy-shuffles')
root=Path(tempfile.mkdtemp(prefix='negatives.',dir=state/'replays'))
driver=['python3','tools/ghidra-lifter/lift-x64-shuffle.py']
for name,args in [('partial-batch',['--fixture','align','reject']),('missing-symbol',['--fixture','missing']),('whole-ssse3',['--cet-disabled','__memcpy_ssse3']),('whole-ssse3-back',['--cet-disabled','__memcpy_ssse3_back'])]:
    out=root/name
    result=subprocess.run(driver+['--out',str(out)]+args,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print(name,'COMMAND',driver+['--out',str(out)]+args,'EXIT',result.returncode,flush=True);print(result.stdout,flush=True)
    assert result.returncode==1 and not out.exists()
    assert not list(root.glob('.e34-stage-*'))
existing=root/'existing';existing.mkdir();(existing/'sentinel').write_bytes(b'unchanged')
for out in (existing,root/'link'):
    if out!=existing:out.symlink_to(existing,target_is_directory=True)
    r=subprocess.run(driver+['--fixture','--out',str(out),'align'],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print('existing-or-symlink',out,'EXIT',r.returncode,r.stdout,flush=True)
    assert r.returncode==2 and (existing/'sentinel').read_bytes()==b'unchanged' and list(existing.iterdir())==[existing/'sentinel']
print('PASS actual atomic publication failures and existing/symlink output preservation')
