#!/usr/bin/env python3
"""Keep the Astra mathematical statements exact across a partial handoff."""
from pathlib import Path
import re
root = Path(__file__).resolve().parents[2]
initial = (root/'notes/a-memcpy-large/initial-arm8_memcpy_large_proof.v.txt').read_text()
current = (root/'Examples/claude/arm8_memcpy_large_proof.v').read_text()
def statements(text):
    return {m[1]: m[0] for m in re.findall(r'((?:Theorem|Lemma)\s+(\w+)\s*:[\s\S]*?)(?=\nProof\.)', text)}
a, b = statements(initial), statements(current)
assert a == b, 'Mathematical statement changed'
# All definitions precede the first theorem and are retained verbatim.
assert initial.split('Theorem memcpy_large_nwc:')[0] == current.split('Theorem memcpy_large_nwc:')[0]
print(f'{len(a)} theorem/lemma statements and initial specification definitions unchanged')
for name in a:
    print(name)
