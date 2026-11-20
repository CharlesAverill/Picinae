#!/usr/bin/env python3
import re
from pathlib import Path
old = Path('notes/x04-avx-overlap-backward/initial-attempt.v.txt').read_text()
new = Path('Examples/claude/amd64_memmove_avx_overlap_backward_proof.v').read_text()
def strip(s):
    while '(*' in s:
        t = re.sub(r'\(\*(?:(?!\(\*|\*\)).)*\*\)', '', s, flags=re.S)
        if t == s: raise ValueError('comment nesting')
        s = t
    return s
pat = r'(?ms)^(Lemma|Theorem|Corollary|Definition)\s+(\w+)\b(.*?)(?=^Proof\.|^\s*(?:Lemma|Theorem|Corollary|Definition|Ltac)\s|\Z)'
def decls(s):
    result = {}
    for kind, name, body in re.findall(pat, strip(s)):
        result[name] = (kind, re.sub(r'\s+', '', body))
    return result
before, after = decls(old), decls(new)
for name, declaration in before.items():
    assert after.get(name) == declaration, f'changed or missing: {name}'
print('Retained declarations:', len(before))
print('Retained lemma/theorem/corollary statements:', sum(k != 'Definition' for k, _ in before.values()))
print('Added declarations:', ', '.join(sorted(after.keys() - before.keys())) or '(none)')
print('PASS: all original definitions and theorem statements retained')
