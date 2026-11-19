#!/usr/bin/env python3
"""Check the exact authorized checkpoint and scoped linear fixer history."""
from pathlib import Path
import hashlib
import subprocess

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()

base = '49956416928e5b6bb3928b54ae33e3b81091f006'
checkpoint = '393e57f7973bbc0ea29e56902816e1ceb92cb20f'
expected = {
    '71470bffba65392adf1873a3df9f0cf0ca4f1ac9',
    '59f696d32a5623cdfbceb9a1e0f91e2cc7c054c1',
    'dac36c0a03088a90bb6e6385f82cb355d27cc204',
    '5677a5d1d995745cc1cefbd33bcda1a3a4b49d8b',
    'abe7eda601a63d47eb70e765f4ae2c4ca235cca4',
    '8c01958e73ec7fe959c60b29444505afbb599d13',
    '075f59aca328e60e6376e2af01fa49925ab10e9d',
    '95da7ab7cee78f09a528aed86c1dfaf29520a9a8',
    '7042ff1b6abdf79e2b07a348c7ef9ed014126ded',
    '5fec2fc24d0c739bafc08add426f02a3085e15cd',
    checkpoint,
}
assert git('rev-parse', 'origin/llm_generated_proofs') == base
assert git('merge-base', 'origin/llm_generated_proofs', 'HEAD') == base
assert git('rev-parse', '71470bff^') == base
assert git('branch', '--show-current') == 'llm-proofs/r07-current-task-fix'
assert git('rev-parse', 'refs/heads/llm-proofs/r07-current-task') == checkpoint
assert git('merge-base', checkpoint, 'HEAD') == checkpoint
assert set(git('rev-list', f'{base}..{checkpoint}').splitlines()) == expected
for commit in git('rev-list', f'{checkpoint}..HEAD').splitlines():
    assert len(git('rev-list', '--parents', '-n', '1', commit).split()) == 2
    for path in git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines():
        assert path in {'dune', 'Examples/FreeRTOS/armv6m_xTaskGetCurrentTaskHandle_proof.v'} or path.startswith('notes/r07-current-task-fix/'), path
lift = Path('Examples/FreeRTOS/xTaskGetCurrentTaskHandle_armv6m.v')
assert hashlib.sha256(lift.read_bytes()).hexdigest() == 'ab04b58fe6006e5fd75b5cf3c44cf5aaf51fabef7f644b12cd55a785c110d6f4'
subprocess.run(['git', 'diff', '--exit-code', checkpoint, '--', 'notes/r07-current-task', 'Examples/FreeRTOS/xTaskGetCurrentTaskHandle_armv6m.v', 'Picinae_armv6m.v'], check=True)
print('PASS: exact 11-commit prerequisite history; only scoped linear fixer commits above it')
print('PASS: pinned origin, original Astra evidence, generated getter and ISA unchanged')
for args in [('rev-parse', 'HEAD'), ('merge-base', 'origin/llm_generated_proofs', 'HEAD'),
             ('log', '--format=%H %s', 'origin/llm_generated_proofs..HEAD'),
             ('diff', '--stat', 'origin/llm_generated_proofs...HEAD'), ('status', '--short')]:
    print('git ' + ' '.join(args), flush=True)
    print(git(*args), flush=True)
