#!/usr/bin/env python3
"""Exact reviewed prerequisite ancestry and preservation audit for this unit."""
from pathlib import Path
import subprocess
import sys

def git(*a):return subprocess.check_output(['git',*a],text=True).strip()
base='49956416928e5b6bb3928b54ae33e3b81091f006'
e11='378fe1b57514b9af3f017a72b4ca665910156cc7'
e01='131ad4b86cf4abcbd392048297038f3f219423bb'
merge='1d4c46287725bd9c2dee3a7735b080ee9488e4ab'
head=git('rev-parse','HEAD')
assert git('rev-parse','origin/llm_generated_proofs')==base
assert git('branch','--show-current')=='llm-proofs/e25-x86-scalar-driver'
allowed=set(git('rev-list',base+'..'+e11).splitlines())|set(git('rev-list',base+'..'+e01).splitlines())|{merge}
if head!=merge:
    assert git('show','-s','--format=%P',head)==merge
    assert git('show','-s','--format=%s',head)=='Add strict AMD64 scalar lifting pipeline'
    allowed.add(head)
assert set(git('rev-list',base+'..HEAD').splitlines())==allowed
assert git('merge-base','origin/llm_generated_proofs','HEAD')==base
staged='--staged' in sys.argv
changes=git('diff',*(['--cached'] if staged else []),'--name-status',merge).splitlines()
assert changes
for line in changes:
    status,path=line.split('\t')
    if status=='M':assert path=='dune',(status,path)
    else:
        assert status=='A',(status,path)
        assert path.startswith(('notes/e25-x86-scalar-driver/','Examples/claude/lifter/x64_scalar_smoke/','Examples/claude/lifter/x64_scalar_fixture/')) or path in {
            'tools/ghidra-lifter/lift-x64.py','tools/ghidra-lifter/pcode2coq_x64.py','tools/ghidra-lifter/x64_headless.py','tools/ghidra-lifter/test_x64.py','tools/ghidra-lifter/test_x64_publication.py'},path
print('PASS exact allowed ancestry and additive e25-only changes; all existing artifacts/ARM drivers/proofs/core preserved')
for args in [('rev-parse','HEAD'),('merge-base','origin/llm_generated_proofs','HEAD'),('log','--oneline','origin/llm_generated_proofs..HEAD'),('diff',*(['--cached'] if staged else []),'--stat','origin/llm_generated_proofs')]:
    print('COMMAND=git '+' '.join(args))
    print(git(*args))
