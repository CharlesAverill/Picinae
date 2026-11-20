"""Permit exactly the reviewed prerequisite closure and scoped local unit commits."""
import subprocess
BASE = '49956416928e5b6bb3928b54ae33e3b81091f006'
PREREQ = '5fec2fc24d0c739bafc08add426f02a3085e15cd'
def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()
assert git('branch', '--show-current') == 'llm-proofs/r09-tick-count-isr'
assert git('rev-parse', 'origin/llm_generated_proofs') == BASE
assert git('merge-base', 'origin/llm_generated_proofs', 'HEAD') == BASE
assert git('merge-base', PREREQ, 'HEAD') == PREREQ
allowed = set(git('rev-list', BASE+'..'+PREREQ).splitlines())
actual = set(git('rev-list', BASE+'..HEAD').splitlines())
assert allowed <= actual
own = actual - allowed
for commit in own:
    parents = git('show', '-s', '--format=%P', commit).split()
    assert len(parents) == 1 and parents[0] in allowed | own
    for path in git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines():
        assert path in ['dune', 'Examples/FreeRTOS/armv6m_xTaskGetTickCountFromISR_proof.v'] or path.startswith('notes/r09-tick-count-isr/'), path
assert git('diff', PREREQ, '--', 'Examples/FreeRTOS/xTaskGetTickCountFromISR_armv6m.v') == ''
print('PASS: exact prerequisite union plus scoped linear unit commits only.')
for args in [('rev-parse', 'HEAD'), ('merge-base', 'origin/llm_generated_proofs', 'HEAD'), ('log', '--format=%H %s', 'origin/llm_generated_proofs..HEAD'), ('diff', '--stat', 'origin/llm_generated_proofs...HEAD'), ('status', '--short')]:
    print('COMMAND: git '+' '.join(args))
    print(git(*args))
