#!/usr/bin/env python3
import re
from pathlib import Path
original = Path('notes/x03-avx-overlap-forward/initial-attempt.v.txt').read_text()
current = Path('Examples/claude/amd64_memmove_avx_overlap_forward_proof.v').read_text()
patterns = [r'(?ms)^Definition (\w+)\b.*?\.\n', r'(?ms)^(?:Theorem|Lemma|Corollary) (\w+)\b.*?(?=\nProof\.)']
count = 0
for pattern in patterns:
    for match in re.finditer(pattern, original):
        name = match.group(1)
        candidates = [m.group(0) for m in re.finditer(pattern,current) if m.group(1)==name]
        assert candidates == [match.group(0)], f'changed/missing declaration: {name}'
        print('UNCHANGED', name)
        count += 1
print(f'Preserved all {count} original declarations verbatim.')
