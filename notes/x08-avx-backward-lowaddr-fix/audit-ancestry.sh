#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prerequisite=a0cf00cf530b9785dba569f9accf05421a36dbb3
[[ $(git rev-parse origin/llm_generated_proofs) == "$base" ]]
[[ $(git merge-base origin/llm_generated_proofs HEAD) == "$base" ]]
git merge-base --is-ancestor "$prerequisite" HEAD
[[ $(git branch --show-current) == llm-proofs/x08-avx-backward-lowaddr-fix ]]
python3 - <<'PY'
import subprocess
base='49956416928e5b6bb3928b54ae33e3b81091f006'
prereq='a0cf00cf530b9785dba569f9accf05421a36dbb3'
def git(*args): return subprocess.check_output(['git',*args], text=True).strip()
allowed=set(git('rev-list',base+'..'+prereq).splitlines())
actual=set(git('rev-list',base+'..HEAD').splitlines())
assert allowed<=actual
for commit in actual-allowed:
    parents=git('rev-list','--parents','-n','1',commit).split()[1:]
    assert len(parents)==1, (commit,parents)
    paths=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    assert all(p=='dune' or p=='Examples/claude/amd64_memmove_avx_backward_lowaddr_proof.v'
               or p.startswith('notes/x08-avx-backward-lowaddr-fix/') for p in paths), (commit,paths)
print('Allowed prerequisite commits:',len(allowed))
print('Scoped unit commits:',len(actual-allowed))
print('No unexpected ancestry or paths')
PY
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git status --short
