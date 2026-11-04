#!/usr/bin/env python3
"""Require exact accepted prerequisite forest plus scoped local unit commits."""
import subprocess
BASE='49956416928e5b6bb3928b54ae33e3b81091f006'
PRE='4ff26413448da4d8f064b0273ac5472cc9de7e5a'
def git(*args):
    return subprocess.check_output(['git',*args],text=True).strip()
assert git('rev-parse','origin/llm_generated_proofs') == BASE
assert git('merge-base','origin/llm_generated_proofs','HEAD') == BASE
assert git('merge-base',PRE,'HEAD') == PRE
assert git('branch','--show-current') == 'llm-proofs/r05-list-insert'
allowed=set(git('rev-list',BASE+'..'+PRE).splitlines())
current=set(git('rev-list',BASE+'..HEAD').splitlines())
assert allowed <= current
for commit in current-allowed:
    parents=git('show','-s','--format=%P',commit).split()
    assert len(parents)==1, (commit,parents)
    for path in git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines():
        assert path in ['dune','Examples/FreeRTOS/armv6m_vListInsert_proof.v'] or path.startswith('notes/r05-list-insert/'), (commit,path)
print('Allowed prerequisite commits:',len(allowed))
print('Scoped unit commits:',len(current-allowed))
for args in [('rev-parse','HEAD'),('merge-base','origin/llm_generated_proofs','HEAD'),
             ('log','--format=%H %s','origin/llm_generated_proofs..HEAD'),
             ('diff','--stat','origin/llm_generated_proofs...HEAD'),
             ('diff','--stat',PRE),('status','--short')]:
    print('git '+' '.join(args)); print(git(*args))
assert git('diff',PRE,'--','Examples/FreeRTOS/vListInsert_armv6m.v') == ''
print('PASS: exact assigned forest, scoped own commits, unchanged generated map')
