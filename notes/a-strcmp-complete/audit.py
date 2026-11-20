#!/usr/bin/env python3
"""Audit the exact authorized ancestry, protected inputs and declaration retention."""
import hashlib
import importlib.util
import pathlib
import re
import subprocess

BASE = '49956416928e5b6bb3928b54ae33e3b81091f006'
PREREQ = '66bb12cfed34143d050f29289e4dc6aabba2cf87'
UNIT = pathlib.Path('notes/a-strcmp-complete')
PROOF = 'Examples/claude/arm8_strcmp_proof.v'

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()

spec = importlib.util.spec_from_file_location('audit_source', 'tools/audit-proof-source.py')
audit_source = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit_source)

def declarations(source):
    source = audit_source.mask(source)
    result = {}
    for match in re.finditer(r'\b(Definition|Lemma|Theorem)\s+(\w+)\b', source):
        if match[1] == 'Definition':
            end = re.search(r'\.(?=\s|$)', source[match.start():]).end() + match.start()
        else:
            end = source.index('Proof.', match.end())
        result[match[2]] = re.sub(r'\s+', ' ', source[match.start():end]).strip()
    return result

old = declarations(git('show', PREREQ + ':' + PROOF))
new = declarations(pathlib.Path(PROOF).read_text())
for name, statement in old.items():
    assert new.get(name) == statement, ('Changed retained declaration', name)
print('Retained declarations:', len(old), '(all original definitions/statements identical)')
print('New declarations:', ', '.join(sorted(new.keys() - old.keys())))
assert not audit_source.findings(pathlib.Path(PROOF).read_text())
assert git('branch', '--show-current') == 'llm-proofs/a-strcmp-complete'
assert git('merge-base', 'origin/llm_generated_proofs', 'HEAD') == BASE
assert git('merge-base', PREREQ, 'HEAD') == PREREQ
allowed = set((UNIT/'allowed-prerequisites.txt').read_text().split())
assert allowed == set(git('rev-list', BASE+'..'+PREREQ).split())
own = set(git('rev-list', PREREQ+'..HEAD').split())
assert set(git('rev-list', BASE+'..HEAD').split()) == allowed | own
for commit in own:
    assert len(git('show', '-s', '--format=%P', commit).split()) == 1
    paths = git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines()
    assert all(p == PROOF or p.startswith(str(UNIT)+'/') for p in paths), paths
changed = git('diff', '--name-only', PREREQ).splitlines()
assert all(p == PROOF or p.startswith(str(UNIT)+'/') for p in changed), changed
lift = pathlib.Path('Examples/claude/lifter/scalar_ccmp/e30_strcmp_arm8.v')
assert hashlib.sha256(lift.read_bytes()).hexdigest() == '2b7b58a310afd013b2dae9e2953786404640796734fc6ae39cf309f0a6568dc3'
print('Protected lift, Dune list, original author notes and all other prerequisite files: unchanged')
print('HEAD:', git('rev-parse', 'HEAD'))
print('Merge base:', BASE)
print('Prerequisite commits:', len(allowed), 'Own commits:', len(own))
print(git('log', '--format=%H %s', BASE+'..HEAD'))
print('Diff from assigned prerequisite:')
print(git('diff', '--stat', PREREQ))
print('Status:')
print(git('status', '--porcelain=v1') or 'CLEAN')
