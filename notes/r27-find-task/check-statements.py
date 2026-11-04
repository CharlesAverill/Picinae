#!/usr/bin/env python3
"""Compare theorem statements to the immutable one-shot author snapshot."""
from pathlib import Path
import re
snapshot=Path('notes/r27-find-task/initial-attempt.v.txt').read_text()
current=Path('Examples/FreeRTOS/armv6m_prvSearchForNameWithinSingleList_proof.v').read_text()
pattern=r'(?m)^(?:Theorem|Lemma|Corollary)\s+(\w+)\s*:(.*?)\nProof\.'
def statements(text):
    return {name:body for name,body in re.findall(pattern,text,re.S)}
a,b=statements(snapshot),statements(current)
assert a == b, 'Author theorem statements changed'
print('PASS: all %d initial theorem statements preserved verbatim' % len(a))
for name in a: print(name)
