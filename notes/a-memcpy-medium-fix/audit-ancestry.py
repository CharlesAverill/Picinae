#!/usr/bin/env python3
import subprocess

def git(*args):
    return subprocess.check_output(['git',*args],text=True).strip()
base='49956416928e5b6bb3928b54ae33e3b81091f006'
checkpoint='6e4a8a821127c302525a2476987fd17d6aa9f647'
assert git('rev-parse','origin/llm_generated_proofs')==base
assert git('merge-base','origin/llm_generated_proofs','HEAD')==base
assert git('branch','--show-current')=='llm-proofs/a-memcpy-medium-fix'
assert git('merge-base',checkpoint,'HEAD')==checkpoint
protected=['Examples/claude/arm8_memcpy_common.v','Examples/claude/arm8_memcpy_small_proof.v','Examples/claude/lifter','notes/a-memcpy-medium','dune']
assert not git('diff',checkpoint,'--',*protected)
for commit in git('rev-list',checkpoint+'..HEAD').splitlines():
    assert len(git('show','-s','--format=%P',commit).split())==1
    for path in git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines():
        assert path=='Examples/claude/arm8_memcpy_medium_proof.v' or path.startswith('notes/a-memcpy-medium-fix/'),path
print('Pinned base/merge-base:',base)
print('Exact allowed prerequisite checkpoint:',checkpoint)
print('Only scoped unit commits follow it; generated maps, common helpers, small proof, Dune, original evidence unchanged.')
print(git('log','--format=%H %P %s',base+'..HEAD'))
print(git('diff','--stat',base+'...HEAD'))
print('STATUS\n'+git('status','--short'))
