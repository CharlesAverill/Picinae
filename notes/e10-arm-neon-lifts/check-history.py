#!/usr/bin/env python3
"""Keep historical receipts immutable; identify pre-existing helper hash drift."""
import hashlib,json,subprocess
from pathlib import Path
repo=Path(__file__).resolve().parents[2]
base='a3a80d011dc91d51b163b9d68c33ef92ea40635b'
deltas=[]
for folder in ('scalar_bitforms','scalar_ccmp'):
 for p in (repo/'Examples/claude/lifter'/folder).glob('*.manifest.json'):
  receipt=json.loads(p.read_text())
  for name,old in receipt['implementation_sha256'].items():
   f='tools/ghidra-lifter/'+name
   prior=hashlib.sha256(subprocess.check_output(['git','show',base+':'+f])).hexdigest()
   now=hashlib.sha256((repo/f).read_bytes()).hexdigest()
   assert now==prior
   if now!=old:deltas.append(dict(receipt=str(p.relative_to(repo)),helper=f,historical=old,assigned_base=prior,current=now,classification='Inherited before e10; no e10 source delta'))
(repo/'notes/e10-arm-neon-lifts/INHERITED-RECEIPT-DELTAS.json').write_text(json.dumps(deltas,indent=2)+'\n')
print('PASS',len(deltas),'inherited old-receipt differences explicitly retained; scalar helper unchanged from assigned base')
