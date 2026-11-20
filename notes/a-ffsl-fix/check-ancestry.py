import subprocess

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()
base = '49956416928e5b6bb3928b54ae33e3b81091f006'
e00 = '71470bffba65392adf1873a3df9f0cf0ca4f1ac9'
author = '95fec3532babe28cc92926f2a23d6253ce55c69a'
assert git('rev-parse', 'origin/llm_generated_proofs') == base
assert git('merge-base', base, 'HEAD') == base
assert git('rev-parse', e00+'^') == base
assert git('rev-parse', author+'^') == e00
assert git('rev-parse', 'llm-proofs/a-ffsl') == author
assert git('branch', '--show-current') == 'llm-proofs/a-ffsl-fix'
commits = git('rev-list', '--reverse', base+'..HEAD').splitlines()
assert commits[:2] == [e00, author]
for parent, child in zip(commits, commits[1:]):
    assert git('show', '-s', '--format=%P', child) == parent
print('Verified a linear pinned origin -> reviewed e00 -> exact Astra checkpoint -> repair ancestry.')
print('Original author branch remains at the exact Astra checkpoint.')
for commit in commits:
    print(git('show', '-s', '--format=%H %s', commit))
