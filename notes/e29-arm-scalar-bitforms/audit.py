#!/usr/bin/env python3
"""Verify the prerequisite preservation boundary and local ancestry."""
import hashlib
import json
from pathlib import Path
import subprocess

repo = Path(__file__).resolve().parents[2]
base = '49956416928e5b6bb3928b54ae33e3b81091f006'
accepted = '9ae8e6800fa044797efd98372857e6ac89b18e1b'
def git(*args): return subprocess.check_output(['git', *args], cwd=repo, text=True).strip()
assert git('merge-base', 'origin/llm_generated_proofs', 'HEAD') == base
assert git('branch', '--show-current') == 'llm-proofs/e29-arm-scalar-bitforms'
subprocess.run(['git', 'merge-base', '--is-ancestor', accepted, 'HEAD'], cwd=repo, check=True)
# Resolve the reviewed commit abbreviations locally; assert their exact history
# against the accepted prerequisite, allowing only this unit above it.
prereqs = set(git('rev-list', base + '..' + accepted).splitlines())
assert {git('rev-parse', p) for p in ('71470bf','081d023','052521a','378fe1b','9ae8e68')} == prereqs
for commit in git('rev-list', accepted + '..HEAD').splitlines():
    files = git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines()
    assert files and all(n in {'dune', 'tools/ghidra-lifter/pcode2coq_scalar.py', 'tools/ghidra-lifter/test_bitforms.py'} or n.startswith(('notes/e29-arm-scalar-bitforms/', 'Examples/claude/lifter/scalar_bitforms/')) for n in files)
hashes = json.loads((repo / 'notes/e29-arm-scalar-bitforms/PROTECTED-HASHES.json').read_text())
for name, digest in hashes.items():
    assert hashlib.sha256((repo / name).read_bytes()).hexdigest() == digest, name
changed = git('diff', '--name-only', accepted).splitlines()
assert set(changed) <= {'dune', 'tools/ghidra-lifter/pcode2coq_scalar.py', 'tools/ghidra-lifter/test_bitforms.py'} | {n for n in changed if n.startswith(('notes/e29-arm-scalar-bitforms/', 'Examples/claude/lifter/scalar_bitforms/'))}
print('PASS pinned merge-base; exact five prerequisite commits; only e29 scope above accepted e08')
print('PASS', len(hashes), 'protected historical/proof/e08/e11 source and evidence hashes')
