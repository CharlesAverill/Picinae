#!/usr/bin/env python3
"""Fresh accepted-closure replay, then byte-compare every deliverable artifact.

A new --run is mandatory. All mutable Ghidra state/output remains private e08.
Rejected scopes retain the original full-batch logs; replay checks successes.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--run',required=True)
a=p.parse_args()
repo=Path(__file__).resolve().parents[2]
root=repo/'Examples/claude/lifter/scalar_ports'
coverage=json.loads((root/'COVERAGE.json').read_text())
groups={}
for r in coverage['accepted']:
 selected=r['selected_symbols']
 groups.setdefault(selected[0], selected)
state=Path('/home/charles/code/friends/.toolchains/e08-arm-lifts')
selection=state/f'{a.run}-selection.json'
if selection.exists():raise ValueError('selection already exists')
selection.write_text(json.dumps(groups,indent=2)+'\n')
out=state/f'{a.run}-published'
command=[sys.executable,str(repo/'notes/e08-arm-lifts/extract.py'),'--run',a.run,'--selection',str(selection),'--out',str(out)]
print('COMMAND='+json.dumps(command),flush=True)
subprocess.run(command,check=True)
for r in coverage['accepted']:
 for suffix in ('.v','.pcode.json','.manifest.json'):
  name=r['artifact']+suffix
  assert (out/name).read_bytes()==(root/name).read_bytes(),name
 print('DETERMINISTIC_PASS',r['artifact'],r['program_sha256'],flush=True)
# Also prove e11's unchanged original global fixture reproduces byte-for-byte.
raw=state/a.run/'mempcpy'
for name in ['e11_mempcpy_arm8.v','e11___memcpy_generic_arm8.v','e11_mempcpy_arm8.pcode.json','e11___memcpy_generic_arm8.pcode.json','SUCCESS.json']:
 assert (raw/name).read_bytes()==(repo/'Examples/claude/lifter/scalar_global'/name).read_bytes(),name
print('PASS fresh deterministic replay for all accepted artifacts and unchanged e11 global fixture/receipt')
