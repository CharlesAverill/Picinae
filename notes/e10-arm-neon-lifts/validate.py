#!/usr/bin/env python3
"""Fresh opt-in supervisor failures and unchanged scalar artifact regressions."""
import argparse,hashlib,json,os,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--run',required=True);a=p.parse_args()
assert a.run.isalnum()
repo=Path(__file__).resolve().parents[2]
state=Path('/home/charles/code/friends/.toolchains/e10-arm-neon-lifts')/a.run
state.mkdir(exist_ok=False)
results=[]
for symbols,good in [(['toascii'],True),(['memcmp'],False),(['__strlen_asimd'],False),(['toascii','memcmp'],False),(['memcmp','toascii'],False)]:
 name='-'.join(symbols);out=state/name
 cmd=[sys.executable,str(repo/'tools/ghidra-lifter/lift-neon-loads.py'),'--state',str(state/(name+'-state')),'--out',str(out),*symbols]
 print('COMMAND='+json.dumps(cmd),flush=True)
 r=subprocess.run(cmd,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
 print('EXIT_CODE='+str(r.returncode),flush=True)
 assert r.returncode==(0 if good else 1)
 assert out.is_dir()==good
 assert not list(state.glob('.e10-stage-*'))
 if good:
  receipt=json.loads((out/'SUCCESS.json').read_text())
  assert receipt['profile']=='aarch64-neon-q-loads-fixed-z256-v1'
  assert set(receipt['implementation_sha256'])=={'pcode2coq_scalar.py','pcode2coq_neon_loads.py','neon_loads_headless.py','lift-neon-loads.py'}
  old=json.loads((repo/'Examples/claude/lifter/scalar_smoke/e11_toascii_arm8.pcode.json').read_text())
  assert json.loads((out/'e10_toascii_arm8.pcode.json').read_text())==old
 else:
  logs=list((state/(name+'-state')/'logs').glob('*.log'));assert len(logs)==1
  text=logs[0].read_text()
  needle='0x194794' if 'memcmp' in symbols else '0x19c9e4'
  assert needle in text,text[-3000:]
 results.append(dict(symbols=symbols,exit=r.returncode,published=good))
print(json.dumps(results,indent=2))
print('PASS full extraction frontiers, mixed-batch atomic failure, scalar trace identity and transitive helper receipt')
