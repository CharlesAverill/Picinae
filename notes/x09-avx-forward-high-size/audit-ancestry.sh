#!/usr/bin/env bash
set -euo pipefail
base=49956416928e5b6bb3928b54ae33e3b81091f006
prerequisite=14ea393f2227bc8bde692b1e70badc61dce80304
test "$(git rev-parse origin/llm_generated_proofs)" = "$base"
test "$(git branch --show-current)" = llm-proofs/x09-avx-forward-high-size
git merge-base --is-ancestor "$prerequisite" HEAD
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git diff --stat
git status --short
# The prepared prerequisite and its accepted proof are immutable in this unit.
git diff --exit-code "$prerequisite" -- Examples/claude/memmove_avx_amd64.v Examples/claude/amd64_memmove_avx_overlap_forward_proof.v
python3 - <<'PY'
import subprocess
base='49956416928e5b6bb3928b54ae33e3b81091f006'
pre='14ea393f2227bc8bde692b1e70badc61dce80304'
def revs(r):return set(subprocess.check_output(['git','rev-list',r],text=True).split())
assert revs(base+'..HEAD') == revs(base+'..'+pre) | revs(pre+'..HEAD')
print('Allowed prerequisite forest plus unit commits only: PASS')
for c in sorted(revs(pre+'..HEAD')):
    paths=subprocess.check_output(['git','diff-tree','--no-commit-id','--name-only','-r',c],text=True).splitlines()
    assert all(p=='dune' or p=='Examples/claude/amd64_memmove_avx_forward_high_size_proof.v' or p.startswith('notes/x09-avx-forward-high-size/') for p in paths), (c,paths)
    print('Scoped unit commit:',c)
PY
