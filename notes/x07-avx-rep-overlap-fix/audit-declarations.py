import re
from pathlib import Path
original=Path('notes/x07-avx-rep-overlap/initial-attempt.v.txt').read_text()
current=Path('Examples/claude/amd64_memmove_avx_rep_overlap_proof.v').read_text()
for pattern in [r'(?ms)^Definition (\w+)\b.*?\.\n',r'(?ms)^(?:Theorem|Lemma|Corollary) (\w+)\b.*?(?=\nProof\.)']:
 for m in re.finditer(pattern,original):
  candidates=[n.group(0) for n in re.finditer(pattern,current) if n.group(1)==m.group(1)]
  assert candidates==[m.group(0)], 'Changed declaration '+m.group(1)
  print('UNCHANGED',m.group(1))
