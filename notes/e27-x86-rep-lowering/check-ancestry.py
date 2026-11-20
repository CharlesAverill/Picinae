#!/usr/bin/env python3
"""Require the exact assigned prerequisite set plus this unit's one local commit."""
from pathlib import Path
import subprocess,sys

def git(*a):return subprocess.check_output(['git',*a],text=True).strip()
base='49956416928e5b6bb3928b54ae33e3b81091f006'
checkpoint='328088263ebba11786a03448808e584231504fe1'
assert git('rev-parse','origin/llm_generated_proofs')==base
assert git('branch','--show-current')=='llm-proofs/e27-x86-rep-lowering'
allowed={line.split()[0] for line in Path('notes/e27-x86-rep-lowering/allowed-prerequisites.txt').read_text().splitlines()}
assert allowed==set(git('rev-list',base+'..'+checkpoint).splitlines())
head=git('rev-parse','HEAD');staged='--staged' in sys.argv
if head!=checkpoint:
    assert git('show','-s','--format=%P',head)==checkpoint
    assert git('show','-s','--format=%s',head)=='Add strict AMD64 REP MOVS and STOS lowering'
    allowed.add(head)
assert set(git('rev-list',base+'..HEAD').splitlines())==allowed
assert git('merge-base',base,'HEAD')==base
changes=git('diff',*(['--cached'] if staged else []),'--name-status',checkpoint).splitlines()
assert changes
for line in changes:
    status,path=line.split('\t')
    if status=='M':assert path=='dune',(status,path)
    else:
        assert status=='A',(status,path)
        assert path.startswith(('notes/e27-x86-rep-lowering/','Examples/claude/lifter/x64_rep_pinned/','Examples/claude/lifter/x64_rep_synthetic/')) or path in {
            'tools/ghidra-lifter/lift-x64-rep.py','tools/ghidra-lifter/pcode2coq_x64_rep.py','tools/ghidra-lifter/x64_rep_headless.py','tools/ghidra-lifter/test_x64_rep.py','tools/ghidra-lifter/test_x64_rep_publication.py'},path
print('PASS exact allowed ancestry, additive e27 scope; e25 driver/smokes/core/proofs unchanged')
for args in [('rev-parse','HEAD'),('merge-base','origin/llm_generated_proofs','HEAD'),('log','--oneline','origin/llm_generated_proofs..HEAD'),('diff',*(['--cached'] if staged else []),'--stat',checkpoint)]:
    print('COMMAND=git '+' '.join(args));print(git(*args))
