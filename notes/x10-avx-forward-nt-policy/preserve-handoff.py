#!/usr/bin/env python3
from pathlib import Path
import re
root=Path('notes/x10-avx-forward-nt-policy')
p=Path('Examples/claude/amd64_memmove_avx_forward_nt_policy_proof.v')
s=(root/'initial-attempt.v.txt').read_text()
a=s.index('Lemma ofnt_negative_gap:')
prefix=s[:a]
suffix=re.sub(r'(?ms)^Proof\..*?^(?:Time )?Qed\.', 'Proof.\n  (* PARTIAL: exact initial proof and first-build diagnostics are archived\n     under notes/x10-avx-forward-nt-policy/. No Astra repair cycle. *)\nAbort.', s[a:])
final=prefix+suffix
final=final.replace('Final proof producer: pending kernel validation.', 'Status: PARTIAL; first full build failed at ofnt_negative_gap.\n   Final proof producer: none. Main theorems below are aborted, not certified.')
statements=lambda text: re.findall(r'(?ms)^(?:Theorem|Lemma|Corollary) .*?(?=^Proof\.)',text)
assert statements(s)==statements(final)
p.write_text(final)
for declaration in statements(s):
    print('PRESERVED',declaration.split(':')[0].strip())
print('Retained only the four proof bodies accepted before the compiler error.')
print('No second Dune/Rocq build or proof repair was run.')
