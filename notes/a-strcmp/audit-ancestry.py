#!/usr/bin/env python3
"""Read-only ancestry and protected-source audit for this unit."""
import hashlib
import pathlib
import subprocess

BASE = "49956416928e5b6bb3928b54ae33e3b81091f006"
PREREQ = "bbad5922112dedaa192bbe1fd0ab97f3bcbb2ba9"

def git(*args):
    return subprocess.check_output(["git", *args], text=True).strip()

allowed = set(pathlib.Path("notes/a-strcmp/allowed-prerequisites.txt").read_text().split())
assert set(git("rev-list", BASE + ".." + PREREQ).split()) == allowed
assert git("merge-base", "origin/llm_generated_proofs", "HEAD") == BASE
assert git("merge-base", PREREQ, "HEAD") == PREREQ
assert git("branch", "--show-current") == "llm-proofs/a-strcmp"
head_set = set(git("rev-list", BASE + "..HEAD").split())
own_set = set(git("rev-list", PREREQ + "..HEAD").split())
assert head_set == allowed | own_set
for sha in own_set:
    parents = git("show", "-s", "--format=%P", sha).split()
    assert len(parents) == 1, (sha, parents)
    assert git("show", "-s", "--format=%s", sha) == "Add partial AArch64 strcmp proof handoff"

paths = git("diff", "--name-only", PREREQ).splitlines()
assert all(p == "dune" or p == "Examples/claude/arm8_strcmp_proof.v"
           or p.startswith("notes/a-strcmp/") for p in paths), paths
lift = pathlib.Path("Examples/claude/lifter/scalar_ccmp/e30_strcmp_arm8.v")
assert hashlib.sha256(lift.read_bytes()).hexdigest() == \
    "2b7b58a310afd013b2dae9e2953786404640796734fc6ae39cf309f0a6568dc3"
print("HEAD:", git("rev-parse", "HEAD"))
print("Merge base:", BASE)
print("Allowed prerequisite commits:", len(allowed))
print("Own unit commits:", len(own_set))
print(git("log", "--format=%H %s", BASE + "..HEAD"))
print("Protected lift: unchanged, exact reviewed SHA256")
print("Changes since e30:")
print(git("diff", "--stat", PREREQ))
print("Status:")
print(git("status", "--porcelain=v1") or "CLEAN")
