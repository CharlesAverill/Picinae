#!/usr/bin/env python3
"""Compare the original author's statements and definitions verbatim."""
from pathlib import Path
import hashlib
import re
import subprocess

unit = Path('notes/r06-task-count-fix')
original = Path('notes/r06-task-count/initial-attempt.v.txt').read_text()
current = Path('Examples/FreeRTOS/armv6m_uxTaskGetNumberOfTasks_proof.v').read_text()
statements = r'(?ms)^(?:Theorem|Lemma|Corollary) (\w+)(.*?)(?=^Proof\.)'
definitions = r'(?ms)^Definition (\w+)(.*?)(?=\n\n)'
for label, pattern, expected in [('statements', statements, 11), ('definitions', definitions, 7)]:
    before, after = dict(re.findall(pattern, original)), dict(re.findall(pattern, current))
    assert before == after and len(before) == expected, label
    print(f'PASS: {expected} {label} retained verbatim: {", ".join(before)}')
assert not re.search(r'\b(?:Abort|Admitted|admit|Axiom|Parameter)\b', current)
print('PASS: no Abort/admission/new axiom/parameter token in active proof')
assert hashlib.sha256(original.encode()).hexdigest() == '1e53620c5784c7a203b34298032bcb926246b27b07a97de513318d9c8b1bb197'
subprocess.run(['git', 'diff', '--exit-code', '7042ff1b6abdf79e2b07a348c7ef9ed014126ded', '--', 'notes/r06-task-count'], check=True)
print('PASS: original Astra attempt and evidence unchanged')
raw = (unit / 'assumptions.log').read_text()
parts = re.split(r'(?m)^(task_count_\w+)\n', raw)[1:]
closed = {'task_count_nwc', 'task_count_welltyped', 'task_count_preserves_memory',
          'task_count_zero_bound', 'task_count_witness_models', 'task_count_entry_satisfiable'}
assert len(parts) == 22
for name, output in zip(parts[::2], parts[1::2]):
    if name in closed:
        assert 'Closed under the global context' in output and 'Axioms:' not in output
        print(f'{name}: closed')
    else:
        assert output.count('Axioms:') == 1
        axioms = re.findall(r'(?m)^([^ \n].*?)\s*:', output.split('Axioms:')[1])
        assert axioms == ['FunctionalExtensionality.functional_extensionality_dep'], axioms
        print(f'{name}: inherited FunctionalExtensionality.functional_extensionality_dep only')
print('PASS: inspected all 11 transitive assumptions reports; no imported admitted theorem')
