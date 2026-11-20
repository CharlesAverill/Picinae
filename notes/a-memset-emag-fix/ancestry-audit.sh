#!/usr/bin/env bash
set -eu
base=49956416928e5b6bb3928b54ae33e3b81091f006
checkpoint=4b2f5bc78d3f544645dae5fb9f3714faf2db68dc
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
test "$(git branch --show-current)" = llm-proofs/a-memset-emag-fix
git merge-base --is-ancestor "$checkpoint" HEAD
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git status --short
python3 - <<'PY'
import subprocess
def git(*args):
 return subprocess.check_output(['git', *args], text=True).splitlines()
base='49956416928e5b6bb3928b54ae33e3b81091f006'
pre='4b2f5bc78d3f544645dae5fb9f3714faf2db68dc'
allowed=set(git('rev-list',base+'..'+pre))
actual=set(git('rev-list',base+'..HEAD'))
assert allowed <= actual
for commit in actual-allowed:
 parents=git('show','-s','--format=%P',commit)[0].split()
 assert len(parents)==1, (commit,parents)
 paths=git('diff-tree','--no-commit-id','--name-only','-r',commit)
 assert all(p=='Examples/claude/arm8_memset_emag_proof.v' or p.startswith('notes/a-memset-emag-fix/') for p in paths), (commit,paths)
print('Allowed pre-unit commits:',len(allowed))
print('Scoped fixer commits:',len(actual-allowed))
print('Unexpected ancestry: none')
PY
