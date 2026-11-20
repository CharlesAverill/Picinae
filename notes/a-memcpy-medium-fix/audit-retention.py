#!/usr/bin/env python3
import re
from pathlib import Path
initial=Path('notes/a-memcpy-medium/initial-proof.v.txt').read_text()
current=Path('Examples/claude/arm8_memcpy_medium_proof.v').read_text()
def declarations(text):
    return {re.match(r'(?:Theorem|Lemma)\s+(\w+)',s)[1]:s for s in
        re.findall(r'^(?:Theorem|Lemma)\s+\w+:[\s\S]*?(?=\nProof\.)',text,re.M)}
def definitions(text):
    return re.findall(r'^Definition [\s\S]*?(?=\n\n)',text,re.M)
a,b=declarations(initial),declarations(current)
assert all(b.get(name)==statement for name,statement in a.items())
assert definitions(initial)==definitions(current)
assert not re.search(r'\b(?:Abort|Admitted|admit|Axiom|Parameter)\b',current)
print(f'All {len(a)} original statements and {len(definitions(initial))} definitions retained verbatim.')
print(f'{len(b)-len(a)} additional proved helper statements; no aborted/admitted declarations.')
