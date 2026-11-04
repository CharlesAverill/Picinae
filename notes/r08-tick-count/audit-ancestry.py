"""Check the exact assigned ancestry and the unit's local change scope."""
from pathlib import Path
import hashlib
import subprocess

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()

base = '49956416928e5b6bb3928b54ae33e3b81091f006'
prereq = '5fec2fc24d0c739bafc08add426f02a3085e15cd'
assert git('rev-parse', 'origin/llm_generated_proofs') == base
assert git('merge-base', 'origin/llm_generated_proofs', 'HEAD') == base
assert git('merge-base', prereq, 'HEAD') == prereq
assert git('branch', '--show-current') == 'llm-proofs/r08-tick-count'
allowed = set(git('rev-list', f'{base}..{prereq}').splitlines())
own = set(git('rev-list', f'{prereq}..HEAD').splitlines())
assert set(git('rev-list', f'{base}..HEAD').splitlines()) == allowed | own
for commit in own:
    assert len(git('rev-list', '--parents', '-n', '1', commit).split()) == 2
    for path in git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines():
        assert path in ('dune', 'Examples/FreeRTOS/armv6m_xTaskGetTickCount_proof.v') or path.startswith('notes/r08-tick-count/'), path
lift = Path('Examples/FreeRTOS/xTaskGetTickCount_armv6m.v')
assert hashlib.sha256(lift.read_bytes()).hexdigest() == '68aff25ab81b55dd8c885e4ac56056074634de87dfaf8d64edb9477e8d6c40e9'
print('PASS: exact allowed prerequisite forest plus scoped linear unit commits; generated lift unchanged')
for args in [('rev-parse', 'HEAD'), ('merge-base', 'origin/llm_generated_proofs', 'HEAD'),
             ('log', '--format=%H %s', 'origin/llm_generated_proofs..HEAD'),
             ('diff', '--stat', 'origin/llm_generated_proofs...HEAD'), ('status', '--short')]:
    print('git ' + ' '.join(args), flush=True)
    print(git(*args), flush=True)
