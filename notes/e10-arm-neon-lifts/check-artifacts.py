#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
repo=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(repo/'tools/ghidra-lifter'))
from test_neon_loads import RAW,ART,cases,lower
n=repo/'notes/e10-arm-neon-lifts'
state=Path('/home/charles/code/friends/.toolchains/e10-arm-neon-lifts')
assert (ART/'RAW.json').read_bytes()==(state/'collect02/raw.json').read_bytes()
assert json.loads((ART/'IL.json').read_text())=={r['bytes']:lower(r) for r in cases()}
frags=json.loads((state/'collect02/OPEN-FRAGMENTS.json').read_text())
assert frags==json.loads((n/'OPEN-FRAGMENTS.json').read_text())
assert all(frags[r['bytes']]==lower(r) for r in cases())
old=json.loads((repo/'Examples/claude/lifter/scalar_cneg/RAW.json').read_text())
assert RAW['targets']==old['targets']
for p,h in json.loads((n/'PROTECTED-HASHES.json').read_text()).items():
 assert hashlib.sha256((repo/p).read_bytes()).hexdigest()==h,p
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='llm-proofs/e10-arm-neon-lifts'
assert subprocess.check_output(['git','merge-base','origin/llm_generated_proofs','HEAD'],text=True).strip()=='49956416928e5b6bb3928b54ae33e3b81091f006'
allowed=json.loads((n/'ALLOWED-ANCESTRY.json').read_text())
assert subprocess.check_output(['git','rev-list','--reverse','49956416928e5b6bb3928b54ae33e3b81091f006..a3a80d011dc91d51b163b9d68c33ef92ea40635b'],text=True).splitlines()==allowed
for c in subprocess.check_output(['git','rev-list','a3a80d011dc91d51b163b9d68c33ef92ea40635b..HEAD'],text=True).splitlines():
 files=subprocess.check_output(['git','diff-tree','--no-commit-id','--name-only','-r',c],text=True).splitlines()
 assert all(f=='dune' or f.startswith(('notes/e10-arm-neon-lifts/','Examples/claude/lifter/neon_loads/')) or f in ['tools/ghidra-lifter/'+x for x in ('pcode2coq_neon_loads.py','test_neon_loads.py','lift-neon-loads.py','neon_loads_headless.py')] for f in files)
print('PASS fresh raw and actual-Ghidra IL replay; pinned old target bytes/pcode; protected baseline hashes; exact assigned ancestry and own scope')
