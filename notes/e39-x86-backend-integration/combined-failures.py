"""Actual mixed-feature launcher failures and explicit feature fallbacks."""
from pathlib import Path
import subprocess,sys,tempfile,json
from compat import STATE,ROOT
run=Path(tempfile.mkdtemp(prefix='combined-negatives.',dir=STATE))
base=[sys.executable,str(ROOT/'tools/ghidra-lifter/lift-x64-integrated.py')]
cases=[([],['mixed']),(['--cet-disabled'],['mixed']),(['--cet-disabled','--bmi1','present'],['mixed']),(['--cet-disabled','--bmi1','present','--abm','present'],['mixed','rejected']),(['--cet-disabled','--bmi1','present','--abm','present'],['missing'])]
for i,(args,names) in enumerate(cases):
    out=run/str(i);cmd=base+['--fixture','--out',str(out),*args,*names]
    print('COMMAND',cmd,flush=True);r=subprocess.run(cmd);print('EXIT',r.returncode,flush=True)
    assert r.returncode==1 and not out.exists() and not list(run.glob('.e39-stage-*'))
out=run/'whole-avx'
cmd=base+['--cet-disabled','--bmi1','present','--abm','present','--out',str(out),'__memmove_avx_unaligned_erms']
print('COMMAND',cmd,flush=True);r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
print(r.stdout,flush=True);print('EXIT',r.returncode,flush=True)
assert r.returncode==1 and not out.exists() and '0x2a084b JC' in r.stdout
assert not list(run.glob('.e39-stage-*'))
for i,args in enumerate([['--bmi1','unknown'],['--unknown-option'],['--abm','unspecified']]):
    out=run/('invalid'+str(i));cmd=base+['--fixture','--out',str(out),*args,'mixed']
    print('COMMAND',cmd,flush=True);r=subprocess.run(cmd);print('EXIT',r.returncode,flush=True)
    assert r.returncode==2 and not out.exists()
existing=run/'existing';existing.mkdir();(existing/'sentinel').write_bytes(b'unchanged')
for out in (existing,run/'link'):
    if out!=existing:out.symlink_to(existing,target_is_directory=True)
    cmd=base+['--fixture','--out',str(out),'mixed'];print('COMMAND',cmd,flush=True)
    r=subprocess.run(cmd);print('EXIT',r.returncode,flush=True)
    assert r.returncode==2 and (existing/'sentinel').read_bytes()==b'unchanged' and len(list(existing.iterdir()))==1
# Both explicitly absent features select the reviewed BSF/BSR projections.
out=run/'absent';cmd=base+['--fixture','--cet-disabled','--bmi1','absent','--abm','absent','--out',str(out),'mixed']
print('COMMAND',cmd,flush=True);r=subprocess.run(cmd);print('EXIT',r.returncode,flush=True);assert r.returncode==0
receipt=json.loads((out/'SUCCESS.json').read_text());assert receipt['features']==dict(cet_disabled=True,bmi1='absent',abm='absent')
assert not list((STATE/'projects').glob('lift-*'))
print('PASS combined feature, partial-batch, unknown option, existing/symlink and absent-feature publication checks')
