#!/usr/bin/env python3
"""Compare every Astra declaration and definition; inspect raw assumptions."""
from pathlib import Path
import hashlib
import re
import subprocess

original = Path('notes/r07-current-task/initial-attempt.v.txt').read_text()
current = Path('Examples/FreeRTOS/armv6m_xTaskGetCurrentTaskHandle_proof.v').read_text()
patterns = [
    ('statements', r'(?ms)^(?:Theorem|Lemma|Corollary) (\w+)(.*?)(?=^Proof\.)', 13),
    ('definitions', r'(?ms)^Definition (\w+)(.*?)(?=\n\n)', 8),
]
for label, pattern, expected in patterns:
    before, after = dict(re.findall(pattern, original)), dict(re.findall(pattern, current))
    assert before == after and len(before) == expected, (label, len(before))
    print(f'PASS: all {expected} {label} retained verbatim: {", ".join(before)}')
assert len(re.findall(r'\bQed\.', current)) == 13
assert not re.search(r'\b(?:Abort|Admitted|admit|Axiom|Axioms|Parameter|Parameters)\b', current)
print('PASS: all 13 proofs end in Qed; no aborted or admitted declarations')
assert hashlib.sha256(original.encode()).hexdigest() == '8bc7f4bd966dee9fad5e9bb44c7264fbb50d23084bcb65dee45664acdac650d5'
subprocess.run(['git', 'diff', '--exit-code', '393e57f7973bbc0ea29e56902816e1ceb92cb20f', '--', 'notes/r07-current-task'], check=True)
print('PASS: exact Astra attempt and all original failure evidence unchanged')

raw = Path('notes/r07-current-task-fix/assumptions.log').read_text()
assert raw.rstrip().endswith('EXIT_CODE=0')
parts = re.split(r'(?m)^(current_task_\w+)\n', raw)[1:]
assert len(parts) == 26, len(parts)
closed = {'current_task_nwc', 'current_task_welltyped', 'current_task_preserves_memory',
          'current_task_zero_bound', 'current_task_witness_models',
          'current_task_entry_satisfiable', 'current_task_entry_nonempty',
          'current_task_original_bytes'}
for name, output in zip(parts[::2], parts[1::2]):
    if name in closed:
        assert 'Closed under the global context' in output and 'Axioms:' not in output, name
        print(f'{name}: closed')
    else:
        assert output.count('Axioms:') == 1, name
        axioms = re.findall(r'(?m)^([^ \n].*?)\s*:', output.split('Axioms:')[1])
        assert axioms == ['FunctionalExtensionality.functional_extensionality_dep'], (name, axioms)
        print(f'{name}: inherited FunctionalExtensionality.functional_extensionality_dep only')
print('PASS: inspected all 13 transitive assumptions reports; no imported admitted theorem')
