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

original = Path('notes/r04-list-remove/initial-attempt.v.txt').read_text()
current = Path('Examples/FreeRTOS/armv6m_uxListRemove_proof.v').read_text()
assert declarations(original) == declarations(current).replace('ImplicitTypes(equal:bool).', ''), 'Declarations changed'
assert current.count('Implicit Types (equal : bool).') == 1
names = re.findall(r'^(?:Theorem|Lemma) (\w+)', current, re.M)
assert len(names) == 16
assert not re.search(r'\b(?:Abort|Admitted|admit|Axiom|Parameter)\b', current)
print('PASS: all original non-proof code preserved (all definitions, Ltac declarations and 16 statements; added bool binder hint only)')
print('\n'.join(names))

assert original[:original.index('Theorem list_remove_correct:')] == current[:current.index('Theorem list_remove_correct:')]
print('PASS: all seven originally completed proof bodies retained verbatim')
