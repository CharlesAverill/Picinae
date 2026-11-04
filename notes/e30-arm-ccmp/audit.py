#!/usr/bin/env python3
"""Verify exact prerequisite ancestry and unchanged protected evidence."""
import hashlib
import json
from pathlib import Path
import subprocess
repo=Path(__file__).resolve().parents[2]
base='49956416928e5b6bb3928b54ae33e3b81091f006'
accepted='9b9ea8fbb9c0921b07a906daae3cecc7048cbf6b'
def git(*args): return subprocess.check_output(['git',*args],cwd=repo,text=True).strip()
def scope(n): return n in ('dune','tools/ghidra-lifter/pcode2coq_scalar.py','tools/ghidra-lifter/test_ccmp.py') or n.startswith(('notes/e30-arm-ccmp/','Examples/claude/lifter/scalar_ccmp/'))
assert git('merge-base','origin/llm_generated_proofs','HEAD')==base
assert git('branch','--show-current')=='llm-proofs/e30-arm-ccmp'
subprocess.run(['git','merge-base','--is-ancestor',accepted,'HEAD'],check=True)
prereqs=set(git('rev-list',base+'..'+accepted).splitlines())
assert {git('rev-parse',p) for p in ('71470bf','081d023','052521a','378fe1b','9ae8e68','9b9ea8f')}==prereqs
for commit in git('rev-list',accepted+'..HEAD').splitlines():
    files=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    assert files and all(scope(n) for n in files)
hashes=json.loads((repo/'notes/e30-arm-ccmp/PROTECTED-HASHES.json').read_text())
for name,digest in hashes.items(): assert hashlib.sha256((repo/name).read_bytes()).hexdigest()==digest,name
assert all(scope(n) for n in git('diff','--name-only',accepted).splitlines())
print('PASS pinned origin merge-base; exact six allowed prerequisite commits; only own e30 scope follows e29')
print('PASS',len(hashes),'unchanged protected historical/core/proof/e02/e08/e11/e29 source and evidence hashes')
