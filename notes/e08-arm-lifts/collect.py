#!/usr/bin/env python3
"""Recheck recorded fresh supervisor runs after adapter repair; never extract.

Read original commands/exits and pinned receipts; recheck every accepted map.
A separate fresh replay is required to certify deterministic reproduction.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
spec = importlib.util.spec_from_file_location('extract', Path(__file__).with_name('extract.py'))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--out',type=Path,required=True)
p.add_argument('runs',nargs='+', help='private completed raw runs in order')
a=p.parse_args()
assert not a.out.exists()
elf=m.ELF(m.DEPS/'root/lib/aarch64-linux-gnu/libc.so.6')
dbg=m.ELF(m.DEPS/f'root/usr/lib/debug/.build-id/{m.BUILD_ID[:2]}/{m.BUILD_ID[2:]}.debug')
inventory=json.loads((m.INVENTORY/'evidence/inventory.json').read_text())
assert m.sha(elf.data)==m.EXPECTED and m.sha(dbg.data)==inventory['debug_sha256']
a.out.parent.mkdir(parents=True,exist_ok=True)
stage=Path(tempfile.mkdtemp(prefix='.e08-collect-',dir=a.out.parent))
accepted,rejected,attempts=[],[],[]
try:
 for runname in a.runs:
  run=m.STATE/runname
  # The completed extraction has one exact command+exit log per invocation.
  logs=sorted(run.glob('*.log'))
  for log in logs:
   if log.name.endswith('.ghidra.log'):continue
   lines=log.read_text().splitlines()
   command=json.loads(lines[0].removeprefix('COMMAND='))
   assert command[1]==str(m.REPO/'tools/ghidra-lifter/lift-scalar.py')
   assert command[2:5]==['--state',str(m.STATE/'ghidra'),'--global-addressing']
   selected=command[7:]
   raw=Path(command[6])
   assert raw==run/log.stem
   exit_code=int(lines[-1].removeprefix('EXIT_CODE='))
   attempts.append(dict(target=log.stem,selected_symbols=selected,exit=exit_code))
   if exit_code:
    assert not raw.exists()
    reason='\n'.join(lines[1:-1]).strip()
    reason=m.re.sub(r'; no output accepted; Ghidra log:.*','',reason)
    rejected.append(dict(target=log.stem,selected_symbols=selected,reason=reason,driver_exit=exit_code))
    continue
   assert any(line.startswith('PASS ') for line in lines)
   receipt=json.loads((raw/'SUCCESS.json').read_text())
   assert [r['symbol'] for r in receipt['records']]==selected
   for name,sha in receipt['implementation_sha256'].items():
    assert m.sha((m.REPO/'tools/ghidra-lifter'/name).read_bytes())==sha
   for record in receipt['records']:
    if any(r['symbol']==record['symbol'] for r in accepted):continue
    rows=json.loads((raw/f'e11_{record["symbol"]}_arm8.pcode.json').read_text())
    accepted.append(m.publish_target(stage,raw,record,rows,selected,elf,dbg))
    print('RECHECK_PASS',record['symbol'],len(rows),'instructions',flush=True)
 # A later explicit closure success supersedes only the earlier failed scope,
 # retaining all original attempts and precise first rejection diagnostics.
 coverage=[]
 for r in inventory['ports']:
  n=r['target']
  ok=any(x['symbol']==n for x in accepted)
  bad=any(n in x['selected_symbols'] for x in rejected)
  status=('historical-preserved' if r['lift_present'] else 'absent-exact-name' if not r['symbol'] else
          'supported-generated' if ok else 'strict-rejected' if bad else
          'ifunc-resolver-not-implementation' if r['symbol']['type']=='IFUNC' else 'not-attempted')
  resolutions=sorted({s['name'] for s in dbg.symbols() if s['name'].startswith(n+'@')}) if not r['symbol'] else []
  coverage.append(dict(target=n,e02_status=r['status'],symbol=r['symbol'],status=status,exact_versioned_names=resolutions))
 assert accepted and not any(r['status']=='not-attempted' for r in coverage)
 m.dump(stage/'COVERAGE.json',dict(elf_sha256=m.EXPECTED,inventory_sha256=m.sha((m.INVENTORY/'evidence/inventory.json').read_bytes()),ports=coverage,accepted=accepted,rejected=rejected,attempts=attempts))
 m.dump(stage/'HASHES.json',{f.name:m.sha(f.read_bytes()) for f in sorted(stage.iterdir())})
 stage.rename(a.out)
 print('PASS rechecked publication',a.out,len(accepted),'artifacts')
finally:
 shutil.rmtree(stage,ignore_errors=True)
