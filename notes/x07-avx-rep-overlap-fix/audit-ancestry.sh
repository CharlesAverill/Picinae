#!/usr/bin/env bash
set -eu
base=49956416928e5b6bb3928b54ae33e3b81091f006
prereq=088a01f07128f763e9cefeb61de776795557b93e
[ "$(git merge-base origin/llm_generated_proofs HEAD)" = "$base" ]
git merge-base --is-ancestor "$prereq" HEAD
git merge-base origin/llm_generated_proofs HEAD
git log --format='%H %s' origin/llm_generated_proofs..HEAD
git diff --stat origin/llm_generated_proofs...HEAD
git status --short --branch
python3 - <<'PY'
import subprocess
base='49956416928e5b6bb3928b54ae33e3b81091f006'
prereq='088a01f07128f763e9cefeb61de776795557b93e'
def git(*args): return subprocess.check_output(['git',*args],text=True).splitlines()
allowed=set(git('rev-list',base+'..'+prereq))
actual=set(git('rev-list',base+'..HEAD'))
for commit in actual-allowed:
 parents=git('show','-s','--format=%P',commit)[0].split()
 assert len(parents)==1, ('unexpected merge',commit)
 paths=git('diff-tree','--no-commit-id','--name-only','-r',commit)
 assert all(p.startswith('notes/x07-avx-rep-overlap-fix/') or p=='Examples/claude/amd64_memmove_avx_rep_overlap_proof.v' for p in paths), (commit,paths)
 print('SCOPED UNIT COMMIT',commit)
assert allowed<=actual
print('PASS: exact assigned prerequisite ancestry plus scoped own commits only')
PY
