#!/usr/bin/env python3
import re, subprocess
from pathlib import Path
checkpoint='0093bb733adbdee3d63e3b2b5673c8b57f919f66'
module='Examples/FreeRTOS/armv6m_list_refinement.v'
paths=subprocess.check_output(['git','diff','--name-only',checkpoint],text=True).splitlines()
assert all(p==module or p.startswith('notes/r47-list-refinement-fix/') for p in paths), paths
s=Path(module).read_text()
original=Path('notes/r47-list-refinement/initial-statements.txt').read_text()
pattern=r'((?:Lemma|Theorem)\s+(\w+)\s*:.*?)(?=\nProof\.|\nAbort\.)'
actual={name:text.strip() for text,name in re.findall(pattern,s,re.S)}
expected=re.split(r'\n\s*\n',original.strip())
for statement in expected:
    name=re.match(r'(?:Lemma|Theorem)\s+(\w+)\s*:',statement)[1]
    if name=='ring_hd_member':
        statement=statement.replace('forall a xs,','forall (a:N) (xs:list N),')
    assert actual[name]==statement, (name,actual.get(name),statement)
assert len(expected)==30
print('All 30 original intended statements retained; only ring_hd_member binder types annotated.')
print('All inherited tracked files except the assigned module are byte-identical to the exact checkpoint.')
