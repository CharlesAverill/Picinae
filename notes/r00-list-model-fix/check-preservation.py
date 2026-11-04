#!/usr/bin/env python3
"""Compare all original declarations/definitions, ignoring comments/proof scripts."""
from pathlib import Path
import re

def declarations(source):
    depth, i, out = 0, 0, []
    while i < len(source):
        if source[i:i+2] == '(*':
            depth += 1
            out.append(' ')
            i += 2
        elif depth and source[i:i+2] == '*)':
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(source[i])
            i += 1
    assert depth == 0
    text = ''.join(out)
    text = re.sub(r'\bProof\..*?\b(?:Qed|Abort)\.', '', text, flags=re.S)
    return re.sub(r'\s+', '', text)

original = Path('notes/r00-list-model/initial-attempt.v.txt').read_text()
current = Path('Examples/FreeRTOS/armv6m_list_model.v').read_text()
assert declarations(original) == declarations(current), 'Declarations changed'
names = re.findall(r'^Theorem (\w+)', current, re.M)
assert len(names) == 19
assert not re.search(r'\b(?:Abort|Admitted|admit|Axiom|Parameter)\b', current)
print('PASS: all original non-proof code preserved (all definitions and 19 statements)')
print('\n'.join(names))
