#!/usr/bin/env python3
"""Check retention against the exact archived Astra attempt, without Rocq."""
import hashlib
from pathlib import Path
import re
import subprocess

original = Path('notes/r11-missed-yield/initial-attempt.v.txt').read_text()
current = Path('Examples/FreeRTOS/armv6m_vTaskMissedYield_proof.v').read_text()
assert hashlib.sha256(original.encode()).hexdigest() == 'f4c7cb34fa53a4ecbd6e853d2852ee0e23bd188468531b82ac2a1dcac13cac9d'
current = re.sub(r'(?m)^Time ', '', current)
for label, pattern, count in [
    ('statements', r'(?ms)^(?:Theorem|Lemma|Corollary) (\w+)(.*?)(?=^Proof\.)', 18),
    ('definitions', r'(?ms)^Definition (\w+)(.*?)(?=\n(?:Definition|Theorem|Lemma|Corollary)|\n\n)', 13),
]:
    before, after = dict(re.findall(pattern, original)), dict(re.findall(pattern, current))
    assert len(before) == count, (label, len(before))
    for name, text in before.items():
        assert after.get(name) == text, (label, name)
    print(f'PASS: all {count} original {label} retained verbatim: {", ".join(before)}')
subprocess.run(['git', 'diff', '--exit-code', 'be3394d9240594694c90e28e5acf37887f9cf14e', '--',
                'notes/r11-missed-yield', 'Examples/FreeRTOS/vTaskMissedYield_armv6m.v'], check=True)
print('PASS: original evidence and generated map unchanged')
assert not re.search(r'\b(?:Abort|Admitted|admit|Axiom|Parameter)\b', current)
print('PASS: no aborted/admitted declarations or new axioms/parameters in active proof')
