#!/usr/bin/env python3
import subprocess
BASE = '49956416928e5b6bb3928b54ae33e3b81091f006'
PREREQ = '5fec2fc24d0c739bafc08add426f02a3085e15cd'
def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()
assert git('rev-parse', 'origin/llm_generated_proofs') == BASE
assert git('merge-base', BASE, 'HEAD') == BASE
assert git('merge-base', PREREQ, 'HEAD') == PREREQ
assert git('branch', '--show-current') == 'llm-proofs/r11-missed-yield'
allowed = set(git('rev-list', f'{BASE}..{PREREQ}').splitlines())
actual = set(git('rev-list', f'{BASE}..HEAD').splitlines())
unit = set(git('rev-list', f'{PREREQ}..HEAD').splitlines())
assert actual == allowed | unit
for commit in unit:
    parents = git('show', '-s', '--format=%P', commit).split()
    assert len(parents) == 1, (commit, parents)
    paths = git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines()
    assert all(p in ('dune', 'Examples/FreeRTOS/armv6m_vTaskMissedYield_proof.v')
               or p.startswith('notes/r11-missed-yield/') for p in paths), paths
print('BASE', BASE)
print('ASSIGNED_PREREQUISITE', PREREQ)
print('HEAD', git('rev-parse', 'HEAD'))
print('MERGE_BASE', git('merge-base', 'origin/llm_generated_proofs', 'HEAD'))
print('ALLOWED_PREREQUISITE_COMMITS', len(allowed))
print('OWN_SCOPED_COMMITS', len(unit))
print('ANCESTRY_CHECK=PASS')
print(git('log', '--format=%H %s', f'{BASE}..HEAD'))
print(git('diff', '--stat', f'{BASE}...HEAD'))
print('STATUS', repr(git('status', '--short')))
