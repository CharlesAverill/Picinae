#!/usr/bin/env python3
import subprocess
BASE='49956416928e5b6bb3928b54ae33e3b81091f006'
E00='71470bffba65392adf1873a3df9f0cf0ca4f1ac9'
PRE='1eb19d19c77636496bb24c6c9c53c029ac76935b'
BRANCH='llm-proofs/a-memcpy-medium'
def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()
assert git('rev-parse','origin/llm_generated_proofs') == BASE
assert git('rev-parse',E00+'^') == BASE
assert git('show','-s','--format=%P',E00) == BASE
assert git('merge-base','origin/llm_generated_proofs','HEAD') == BASE
assert git('merge-base',PRE,'HEAD') == PRE
assert git('branch','--show-current') == BRANCH
allowed=set(git('rev-list',BASE+'..'+PRE).splitlines())
actual=set(git('rev-list',BASE+'..HEAD').splitlines())
own=actual-allowed
assert allowed <= actual
for commit in own:
    paths=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    assert paths and all(p=='dune' or p=='Examples/claude/arm8_memcpy_medium_proof.v' or p.startswith('notes/a-memcpy-medium/') for p in paths), (commit,paths)
assert not git('diff',PRE,'--','Examples/claude/arm8_memcpy_common.v','Examples/claude/arm8_memcpy_small_proof.v','Examples/claude/lifter')
print('HEAD',git('rev-parse','HEAD'))
print('BRANCH',BRANCH)
print('MERGE_BASE',BASE)
print('PREREQUISITE',PRE)
print('ALLOWED_PREREQUISITE_COMMITS',len(allowed))
print('OWN_SCOPED_COMMITS',len(own))
print(git('log','--format=%H %s','origin/llm_generated_proofs..HEAD'))
print(git('diff','--stat','origin/llm_generated_proofs...HEAD'))
print('STATUS_BEGIN')
print(git('status','--short'))
print('STATUS_END')
print('ANCESTRY_AND_PROTECTED_INPUTS_OK')
