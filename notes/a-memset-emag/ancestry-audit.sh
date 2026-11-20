#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prerequisite=9ae8e6800fa044797efd98372857e6ac89b18e1b
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
git merge-base --is-ancestor "$prerequisite" HEAD
test "$(git branch --show-current)" = llm-proofs/a-memset-emag
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git status --short
python3 - <<'PY'
import subprocess

def git(*args):
    return subprocess.check_output(['git', *args], text=True).splitlines()
base='49956416928e5b6bb3928b54ae33e3b81091f006'
pre='9ae8e6800fa044797efd98372857e6ac89b18e1b'
allowed=set(git('rev-list',base+'..'+pre))
actual=set(git('rev-list',base+'..HEAD'))
assert allowed <= actual
for commit in actual-allowed:
    parents=git('show','-s','--format=%P',commit)[0].split()
    assert len(parents)==1, (commit,parents)
    paths=git('diff-tree','--no-commit-id','--name-only','-r',commit)
    assert all(p in ('dune','Examples/claude/arm8_memset_emag_proof.v') or p.startswith('notes/a-memset-emag/') for p in paths), (commit,paths)
print('Allowed prerequisite commits:',len(allowed))
print('Scoped unit commits:',len(actual-allowed))
print('Unexpected ancestry: none')
PY
