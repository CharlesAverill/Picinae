#!/usr/bin/env python3
"""Validate exact assigned history and an archival-only partial handoff."""
import hashlib
from pathlib import Path
import subprocess

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()

base = '49956416928e5b6bb3928b54ae33e3b81091f006'
prereq = '5fec2fc24d0c739bafc08add426f02a3085e15cd'
assert git('rev-parse', 'origin/llm_generated_proofs') == base
assert git('merge-base', 'origin/llm_generated_proofs', 'HEAD') == base
assert git('merge-base', prereq, 'HEAD') == prereq
assert git('branch', '--show-current') == 'llm-proofs/r07-current-task'
assert git('rev-parse', '71470bffba65392adf1873a3df9f0cf0ca4f1ac9^') == base
allowed = set(git('rev-list', f'{base}..{prereq}').splitlines())
actual = set(git('rev-list', f'{base}..HEAD').splitlines())
assert allowed <= actual
for commit in actual - allowed:
    assert len(git('rev-list', '--parents', '-n', '1', commit).split()) == 2
    for path in git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines():
        assert path.startswith('notes/r07-current-task/'), path
assert hashlib.sha256(Path('Examples/FreeRTOS/xTaskGetCurrentTaskHandle_armv6m.v').read_bytes()).hexdigest() == 'ab04b58fe6006e5fd75b5cf3c44cf5aaf51fabef7f644b12cd55a785c110d6f4'
assert hashlib.sha256(Path('notes/r07-current-task/initial-attempt.v.txt').read_bytes()).hexdigest() == '8bc7f4bd966dee9fad5e9bb44c7264fbb50d23084bcb65dee45664acdac650d5'
assert Path('dune').read_bytes() == subprocess.check_output(['git', 'show', prereq + ':dune'])
assert not Path('Examples/FreeRTOS/armv6m_xTaskGetCurrentTaskHandle_proof.v').exists()
print('PASS: exact prerequisite union, only scoped archival unit commits, unchanged lift/Dune, exact preserved attempt')
for args in [('rev-parse', 'HEAD'), ('merge-base', 'origin/llm_generated_proofs', 'HEAD'),
             ('log', '--format=%H %s', 'origin/llm_generated_proofs..HEAD'),
             ('diff', '--stat', 'origin/llm_generated_proofs...HEAD'), ('status', '--short')]:
    print('git ' + ' '.join(args), flush=True)
    print(git(*args), flush=True)
