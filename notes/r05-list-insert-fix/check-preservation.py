#!/usr/bin/env python3
import importlib.util,re,subprocess
from pathlib import Path
spec=importlib.util.spec_from_file_location('audit','tools/audit-proof-source.py')
audit=importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
def decls(s):
    s=audit.mask(s)
    s=re.sub(r'\bProof\.(?:.|\n)*?\b(?:Qed|Defined|Abort)\.', '', s)
    s=re.sub(r'Print Assumptions [^.]+\.', '', s)
    matches=re.finditer(r'(?m)^(?:Theorem|Lemma|Record|Definition|Fixpoint|Require|From|Import|Open|Ltac|Tactic)\b', s)
    offsets=[m.start() for m in matches]+[len(s)]
    return [' '.join(s[a:b].split()) for a,b in zip(offsets,offsets[1:])]
old=decls(Path('notes/r05-list-insert/initial-attempt.v.txt').read_text())
new=decls(Path('Examples/FreeRTOS/armv6m_vListInsert_proof.v').read_text())
for d in old:
    assert d in new, 'Changed original declaration: '+d[:250]
for p in ['notes/r05-list-insert','Examples/FreeRTOS/vListInsert_armv6m.v']:
    assert not subprocess.check_output(['git','diff','dae969a921f24e3541b7b406c5f6be7618e520f6','--',p]), p
print(f'PASS: {len(old)} original declarations preserved; original evidence and generated IL unchanged')
