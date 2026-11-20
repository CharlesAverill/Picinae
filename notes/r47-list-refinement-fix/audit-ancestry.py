#!/usr/bin/env python3
import subprocess
base='49956416928e5b6bb3928b54ae33e3b81091f006'
checkpoint='0093bb733adbdee3d63e3b2b5673c8b57f919f66'
def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()
assert git('rev-parse','origin/llm_generated_proofs')==base
assert git('merge-base','origin/llm_generated_proofs','HEAD')==base
assert git('branch','--show-current')=='llm-proofs/r47-list-refinement-fix'
allowed=set(git('rev-list',base+'..'+checkpoint).split())
actual=set(git('rev-list',base+'..HEAD').split())
assert allowed<=actual
for commit in actual-allowed:
    parents=git('show','-s','--format=%P',commit).split()
    assert len(parents)==1,(commit,parents)
    paths=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    assert all(p=='Examples/FreeRTOS/armv6m_list_refinement.v' or
               p.startswith('notes/r47-list-refinement-fix/') for p in paths),(commit,paths)
print('MERGE_BASE',git('merge-base','origin/llm_generated_proofs','HEAD'))
print('ALLOWED_PREREQUISITE_UNION',len(allowed),'commits ending at',checkpoint)
print('OWN_SCOPED_COMMITS',*sorted(actual-allowed))
print(git('log','--format=%H %s','origin/llm_generated_proofs..HEAD'))
print(git('diff','--stat','origin/llm_generated_proofs...HEAD'))
print('STATUS',git('status','--short'))
print('ANCESTRY PASS')
