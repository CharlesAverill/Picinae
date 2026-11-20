#!/usr/bin/env python3
import subprocess

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()
base='49956416928e5b6bb3928b54ae33e3b81091f006'
heads=['14ea393f2227bc8bde692b1e70badc61dce80304','cfb65c6f988088e4d1912544a03279d7cb29a681']
allowed=set()
for head in heads:
    allowed.update(git('rev-list',base+'..'+head).splitlines())
assert git('rev-parse','origin/llm_generated_proofs')==base
assert git('merge-base','origin/llm_generated_proofs','HEAD')==base
for head in heads:
    assert git('merge-base',head,'HEAD')==head
print('BRANCH',git('branch','--show-current'))
print('HEAD',git('rev-parse','HEAD'))
print('MERGE_BASE',git('merge-base','origin/llm_generated_proofs','HEAD'))
print('ALLOWED_PREREQUISITES',*sorted(allowed),sep='\n')
for commit in git('rev-list',base+'..HEAD').splitlines():
    if commit in allowed:
        continue
    print('UNIT_COMMIT',git('show','-s','--format=%H %P %s',commit))
    paths=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    assert all(p=='dune' or p=='Examples/claude/amd64_memmove_avx_forward_nt_policy_proof.v' or p.startswith('notes/x10-avx-forward-nt-policy/') for p in paths), paths
print(git('log','--format=%H %s','origin/llm_generated_proofs..HEAD'))
print(git('diff','--stat','origin/llm_generated_proofs...HEAD'))
print('STATUS',git('status','--short','--branch'),sep='\n')
print('PASS: only the assigned forests and scoped unit/import commits')
