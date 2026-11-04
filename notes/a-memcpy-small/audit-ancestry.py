import subprocess
import sys

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()

base = '49956416928e5b6bb3928b54ae33e3b81091f006'
e08 = '9ae8e6800fa044797efd98372857e6ac89b18e1b'
allowed = {
    '71470bffba65392adf1873a3df9f0cf0ca4f1ac9',
    '081d0233cd6667803b3907343b2fea6dc9eba714',
    '052521a753adbda077843ec7b259801282a7b1e9',
    '378fe1b57514b9af3f017a72b4ca665910156cc7', e08,
}
if len(sys.argv) == 2:
    own = sys.argv[1]
    assert git('rev-parse', 'HEAD') == own
    assert git('show', '-s', '--format=%P', own) == e08
    allowed.add(own)
assert git('branch', '--show-current') == 'llm-proofs/a-memcpy-small'
assert git('rev-parse', 'origin/llm_generated_proofs') == base
assert git('merge-base', 'origin/llm_generated_proofs', 'HEAD') == base
assert set(git('rev-list', base + '..HEAD').splitlines()) == allowed
assert git('diff', e08, '--', 'Examples/claude/lifter/scalar_ports') == ''
print('Exact prerequisite/own-commit ancestry and protected-map audit: PASS')
print('HEAD:', git('rev-parse', 'HEAD'))
print('MERGE_BASE:', git('merge-base', 'origin/llm_generated_proofs', 'HEAD'))
print(git('log', '--format=%H %s', 'origin/llm_generated_proofs..HEAD'))
print(git('diff', '--stat', 'origin/llm_generated_proofs...HEAD'))
print('STATUS:')
print(git('status', '--short', '--branch'))
