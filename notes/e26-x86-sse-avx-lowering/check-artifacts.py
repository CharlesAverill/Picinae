#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess
repo=Path(__file__).resolve().parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
count=0
for d in ('x64_copy_fixture','x64_copy_pinned'):
    directory=repo/'Examples/claude/lifter'/d
    receipt=json.loads((directory/'SUCCESS.json').read_text())
    for f,digest in receipt['implementation_sha256'].items():assert sha(repo/'tools/ghidra-lifter'/f)==digest,f
    if 'selection_sha256' in receipt:assert sha(Path(__file__).with_name('actual-selection.json'))==receipt['selection_sha256']
    if 'fixture_source_sha256' in receipt:assert sha(Path(__file__).with_name('fixture')/'moves.S')==receipt['fixture_source_sha256']
    for r in receipt['records']:
        v=directory/r['output'];p=v.with_suffix('.pcode.json')
        assert sha(v)==r['output_sha256'] and sha(p)==r['pcode_sha256']
        text=v.read_text()
        assert not re.search(r'\b(Admitted|admit|Axiom|Parameter)\b',text)
        assert text.count('Theorem welltyped :')==1 and text.count('Proof. Picinae_typecheck. Qed.')==1
        rows=json.loads(p.read_text());assert len(rows)==r['instructions']
        assert r['coverage']==('isolated-instruction-fixtures' if d=='x64_copy_pinned' else 'selected-function-extents')
        count+=1
assert count==5
changed=subprocess.check_output(['git','diff','--name-only','328088263ebba11786a03448808e584231504fe1','--'],text=True).splitlines()
inherited=set(subprocess.check_output(['git','ls-tree','-r','--name-only','328088263ebba11786a03448808e584231504fe1'],text=True).splitlines())
assert set(changed)&inherited<= {'dune'},changed
print('PASS all five hash receipts, complete Qed typing facts, no new admissions/axioms/parameters, and protected inherited sources')
