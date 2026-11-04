#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
e00=71470bffba65392adf1873a3df9f0cf0ca4f1ac9
checkpoint=14bdeb6a8e93bddb2014b9b907e432dbf2b1516d
test "$(git branch --show-current)" = llm-proofs/x03-avx-overlap-forward-fix
test "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base"
test "$(git rev-parse "$e00^")" = "$base"
test "$(git rev-parse "$checkpoint^")" = "$e00"
git merge-base --is-ancestor "$checkpoint" HEAD
printf 'WORKTREE=%s\n' "$PWD"
git rev-parse HEAD
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git diff --exit-code "$base" -- Examples/claude/memmove_avx_amd64.v
git diff --exit-code "$checkpoint" -- dune notes/x03-avx-overlap-forward
printf 'FIX_COMMIT_FILES\n'
git log --format='%H %s' --name-only "$checkpoint"..HEAD
test -z "$(git rev-list --min-parents=2 "$checkpoint"..HEAD)"
python3 - "$checkpoint" <<'PY_SCOPE'
import subprocess,sys
checkpoint=sys.argv[1]
for commit in subprocess.check_output(['git','rev-list',checkpoint+'..HEAD'],text=True).splitlines():
    paths=subprocess.check_output(['git','diff-tree','--no-commit-id','--name-only','-r',commit],text=True).splitlines()
    for p in paths:
        assert p == 'Examples/claude/amd64_memmove_avx_overlap_forward_proof.v' or p.startswith('notes/x03-avx-overlap-forward-fix/'), (commit,p)
print('Every fix commit has linear history and only scoped paths.')
PY_SCOPE
printf 'STATUS\n'
git status --short
