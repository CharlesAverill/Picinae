"""Verify the exact allowed prerequisite ancestry plus scoped local unit commits."""
import subprocess

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()

base = '49956416928e5b6bb3928b54ae33e3b81091f006'
prerequisite = '5fec2fc24d0c739bafc08add426f02a3085e15cd'
assert git('rev-parse', 'origin/llm_generated_proofs') == base
assert git('merge-base', 'origin/llm_generated_proofs', 'HEAD') == base
assert git('merge-base', prerequisite, 'HEAD') == prerequisite
assert git('rev-parse', '71470bff^') == base
assert git('branch', '--show-current') == 'llm-proofs/r10-suspend-all'
allowed = set(git('rev-list', f'{base}..{prerequisite}').splitlines())
actual = set(git('rev-list', f'{base}..HEAD').splitlines())
assert allowed <= actual
for commit in actual - allowed:
    assert len(git('rev-list', '--parents', '-n', '1', commit).split()) == 2
    for path in git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines():
        assert path in ['dune', 'Examples/FreeRTOS/armv6m_vTaskSuspendAll_proof.v'] or path.startswith('notes/r10-suspend-all/'), path
assert git('diff', prerequisite, '--', 'Examples/FreeRTOS/vTaskSuspendAll_armv6m.v') == ''
print('PASS: exact assigned prerequisite union and only scoped linear unit commits; generated lift unchanged')
for args in [('rev-parse', 'HEAD'), ('merge-base', 'origin/llm_generated_proofs', 'HEAD'),
             ('log', '--format=%H %s', 'origin/llm_generated_proofs..HEAD'),
             ('diff', '--stat', 'origin/llm_generated_proofs...HEAD'), ('status', '--short')]:
    print('git ' + ' '.join(args), flush=True)
    print(git(*args), flush=True)
