from pathlib import Path
import subprocess
base = '49956416928e5b6bb3928b54ae33e3b81091f006'
checkpoint = '003d8a6d10510ce11b7c45beea2e62174b2ded2b'
def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()
assert git('branch', '--show-current') == 'llm-proofs/r13-reset-event-fix'
assert git('rev-parse', 'origin/llm_generated_proofs') == base
assert git('merge-base', base, 'HEAD') == base
assert git('merge-base', checkpoint, 'HEAD') == checkpoint
allowed = set(git('rev-list', base+'..'+checkpoint).splitlines())
actual = set(git('rev-list', base+'..HEAD').splitlines())
assert allowed <= actual
for commit in actual-allowed:
    assert len(git('show', '-s', '--format=%P', commit).split()) == 1
    paths = git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines()
    assert all(p == 'Examples/FreeRTOS/armv6m_uxTaskResetEventItemValue_proof.v'
               or p.startswith('notes/r13-reset-event-fix/') for p in paths), (commit, paths)
    print('Own scoped commit:', commit)
assert not git('diff', checkpoint, '--', 'notes/r13-reset-event',
               'Examples/FreeRTOS/uxTaskResetEventItemValue_armv6m.v', 'dune')
print('Base:', base, '\nExact source checkpoint:', checkpoint)
print('Allowed prerequisite commits:', len(allowed))
print(git('log', '--format=%H %s', base+'..HEAD'))
print(git('diff', '--stat', base+'...HEAD'))
print('STATUS:', git('status', '--short'))
print('ANCESTRY AND ARCHIVE PRESERVATION PASS')
