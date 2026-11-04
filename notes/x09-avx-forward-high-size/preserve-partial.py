"""Archive one-shot source and replace uncertified proof attempts with Abort.

No proof repair, no statement edits, and no second compiler invocation.
Run only after the single full target fails.
"""
from pathlib import Path
import re
p=Path('Examples/claude/amd64_memmove_avx_forward_high_size_proof.v')
archive=Path('notes/x09-avx-forward-high-size/initial-attempt.v.txt')
s=p.read_text()
assert s == archive.read_text(), 'Initial source changed after snapshot'
prefix, suffix=s.split('Theorem memmove_avx_correct_forward_high_size:',1)
t,count=re.subn(r'Proof\..*?(?:Time )?Qed\.', 'Proof.\n  (* Uncertified one-shot attempt is preserved verbatim in unit notes. *)\nAbort.','Theorem memmove_avx_correct_forward_high_size:'+suffix,flags=re.S)
assert count==4, count
p.write_text(prefix+t)
print('Preserved all 11 exact statements; archived original proof bodies.')
print('Seven prefix Qeds processed before failure retained; four remaining attempts Abort.')
print('No full module certificate or assumptions audit: no completion claim.')
