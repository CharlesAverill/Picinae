#!/usr/bin/env python3
from pathlib import Path
import subprocess
note=Path(__file__).resolve().parent
def git(*args):return subprocess.check_output(['git',*args],text=True).strip()
base='49956416928e5b6bb3928b54ae33e3b81091f006'
checkpoint='328088263ebba11786a03448808e584231504fe1'
assert git('rev-parse','origin/llm_generated_proofs')==base
assert git('merge-base','origin/llm_generated_proofs','HEAD')==base
assert git('branch','--show-current')=='llm-proofs/e28-x86-bitscan-lowering'
assert git('merge-base',checkpoint,'HEAD')==checkpoint
allowed=set((note/'allowed-prerequisites.txt').read_text().split())
assert set(git('rev-list',base+'..'+checkpoint).split())==allowed
own=git('rev-list','--reverse',checkpoint+'..HEAD').split()
previous=checkpoint
for commit in own:
    assert git('show','-s','--format=%P',commit)==previous, 'nonlinear/unassigned ancestry'
    assert git('show','-s','--format=%s',commit) in ('Add guarded AMD64 bit-scan lowering','Record bit-scan validation evidence'), 'unassigned commit'
    previous=commit
assert set(git('rev-list',base+'..HEAD').split())==allowed|set(own)
print('MERGE_BASE',git('merge-base','origin/llm_generated_proofs','HEAD'))
print('HEAD',git('rev-parse','HEAD'))
print('ALLOWED PREREQUISITES',len(allowed),'OWN',len(own))
print(git('log','--oneline','origin/llm_generated_proofs..HEAD'))
print(git('diff','--stat','origin/llm_generated_proofs...HEAD'))
print('PASS exact authorized prerequisite set plus only linear unit commits')
