#!/usr/bin/env python3
"""Check the assigned prerequisite union and this unit's scoped commits."""
import subprocess
BASE = '49956416928e5b6bb3928b54ae33e3b81091f006'
PREREQ = '1eb19d19c77636496bb24c6c9c53c029ac76935b'
E00 = '71470bffba65392adf1873a3df9f0cf0ca4f1ac9'
def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()
def scoped(path):
    return path in ('dune', 'Examples/claude/arm8_memcpy_large_proof.v') or path.startswith('notes/a-memcpy-large/')
assert git('rev-parse', 'origin/llm_generated_proofs') == BASE
assert git('rev-parse', E00+'^') == BASE
assert git('rev-parse', '--abbrev-ref', 'HEAD') == 'llm-proofs/a-memcpy-large'
assert git('merge-base', 'origin/llm_generated_proofs', 'HEAD') == BASE
allowed = set(git('rev-list', BASE+'..'+PREREQ).splitlines())
actual = set(git('rev-list', BASE+'..HEAD').splitlines())
own = set(git('rev-list', PREREQ+'..HEAD').splitlines())
assert actual == allowed | own
assert allowed <= actual
for commit in own:
    paths = git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines()
    assert all(scoped(p) for p in paths), (commit, paths)
paths = git('diff', '--name-only', PREREQ).splitlines()
assert all(scoped(p) for p in paths), paths
print('HEAD', git('rev-parse', 'HEAD'))
print('MERGE_BASE', git('merge-base', 'origin/llm_generated_proofs', 'HEAD'))
print('ALLOWED_PREREQUISITE_COMMITS', len(allowed))
print('OWN_SCOPED_COMMITS', len(own))
print(git('log', '--format=%H %s', 'origin/llm_generated_proofs..HEAD'))
print(git('diff', '--stat', 'origin/llm_generated_proofs...HEAD'))
print(git('status', '--short', '--branch'))
print('ANCESTRY_AND_SCOPE_OK')
