#!/usr/bin/env python3
import re
from pathlib import Path
initial=Path('notes/a-memcpy-medium/initial-proof.v.txt').read_text()
current=Path('Examples/claude/arm8_memcpy_medium_proof.v').read_text()
def statements(text):
    return re.findall(r'^(?:Theorem|Lemma)\s+\w+:[\s\S]*?(?=\nProof\.)',text,re.M)
def definitions(text):
    return re.findall(r'^Definition [\s\S]*?(?=\n\n)',text,re.M)
assert statements(initial)==statements(current)
assert definitions(initial)==definitions(current)
print('All',len(statements(initial)),'initial theorem/lemma statements retained verbatim.')
print('All',len(definitions(initial)),'initial definitions retained verbatim.')
