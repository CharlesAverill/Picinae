#!/usr/bin/env python3
"""Mechanical archival only: no proof repair or second compiler invocation."""
from pathlib import Path
import re
root=Path('notes/r47-list-refinement')
p=Path('Examples/FreeRTOS/armv6m_list_refinement.v')
s=(root/'initial-attempt.v.txt').read_text()
log=(root/'dune-initial.log').read_text()
assert 'EXIT_CODE=1' in log
errors=list(re.finditer(r'File "\./Examples/FreeRTOS/armv6m_list_refinement.v", line (\d+)',log))
assert errors, 'Failure outside unit: requires a different archival explanation'
line=int(errors[-1][1])
pos=sum(len(l) for l in s.splitlines(keepends=True)[:line-1])
proofs=list(re.finditer(r'(?:Lemma|Theorem)\s+(\w+)\s*:.*?\nProof\..*?Qed\.\nCheck \1\.\nPrint Assumptions \1\.',s,re.S))
failing=next(i for i,m in enumerate(proofs) if m.start()<=pos<m.end())
print('First failed declaration:',proofs[failing][1],'at source line',line)
print('Checked prefix declarations:',*[m[1] for m in proofs[:failing]])
for m in reversed(proofs[failing:]):
    header=m[0].split('\nProof.',1)[0]
    s=s[:m.start()]+header+'\nAbort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)'+s[m.end():]
p.write_text('(* PARTIAL handoff: first full build failed. Unverified declarations are\n   aborted, never exported as assumed theorems. No second Astra compile. *)\n'+s)
(root/'assumptions-status.txt').write_text(
    'Full r47 .vo target FAILED; no main refinement theorem certified.\n'
    'Verbatim inline Check/Print Assumptions for the successful prefix are in dune-initial.log.\n'
    'tools/print-assumptions.sh was NOT run: it would retry the failed full target,\n'
    'contrary to the one-shot handoff rule. A new Sol fixer must run it on ALL\n'
    'retained results after a successful full build.\n'
    'Inherited r03/r04 raw certificates disclose exactly\n'
    'FunctionalExtensionality.functional_extensionality_dep for the IL theorems.\n'
    'Those certificates were read; they are not fresh r47 assumption checks.\n')
original=(root/'initial-statements.txt').read_text().strip()
current='\n\n'.join(m[0] for m in re.finditer(r'(?:Lemma|Theorem)\s+\w+\s*:.*?(?=\n(?:Proof\.|Abort\.))',s,re.S)).strip()
assert original==current, 'Statement changed during archival'
print('PASS: all initial theorem statements retained byte-for-byte')
