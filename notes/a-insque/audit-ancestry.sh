#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
assigned=9ae8e6800fa044797efd98372857e6ac89b18e1b
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
git merge-base --is-ancestor "$assigned" HEAD
git branch --show-current
git rev-parse HEAD
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git diff --stat "$assigned" HEAD
git status --porcelain=v1
python3 - <<'PY'
import subprocess
base='49956416928e5b6bb3928b54ae33e3b81091f006'
assigned='9ae8e6800fa044797efd98372857e6ac89b18e1b'
def git(*args): return subprocess.check_output(['git',*args],text=True).splitlines()
allowed=set(git('rev-list',base+'..'+assigned))
actual=set(git('rev-list',base+'..HEAD'))
assert allowed <= actual
for commit in actual-allowed:
    parents=git('show','-s','--format=%P',commit)[0].split()
    assert len(parents)==1, (commit,parents)
    changed=git('diff-tree','--no-commit-id','--name-only','-r',commit)
    assert all(p in {'dune','Examples/claude/arm8_insque_proof.v'} or p.startswith('notes/a-insque/') for p in changed), (commit,changed)
print('Exact prerequisite union plus own scoped single-parent commits: PASS')
assert not git('diff',assigned,'--','Examples/claude/lifter/scalar_ports/e08_insque_arm8.v')
print('Generated insque map unchanged: PASS')
PY
