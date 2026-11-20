#!/usr/bin/env python3
from pathlib import Path
import subprocess
base='49956416928e5b6bb3928b54ae33e3b81091f006'
checkpoint='bcdd924bec65111aeb9244de21e5dba6286da845'
run=lambda *args:subprocess.check_output(['git',*args],text=True).strip()
notes=Path(__file__).resolve().parent
allowed=set((notes/'allowed-prerequisites.txt').read_text().splitlines())
assert run('rev-parse','origin/llm_generated_proofs')==base
assert run('merge-base','origin/llm_generated_proofs','HEAD')==base
assert run('branch','--show-current')=='llm-proofs/e34-x86-copy-shuffles'
assert set(run('rev-list',base+'..'+checkpoint).splitlines())==allowed and len(allowed)==8
subprocess.run(['git','merge-base','--is-ancestor',checkpoint,'HEAD'],check=True)
protected=['tools/ghidra-lifter/pcode2coq_x64.py','tools/ghidra-lifter/pcode2coq_x64_copy.py','tools/ghidra-lifter/pcode2coq_scalar.py','tools/ghidra-lifter/lift-x64-copy.py','tools/ghidra-lifter/x64_copy_headless.py','tools/ghidra-lifter/test_x64_copy.py','Examples/claude/lifter/x64_copy_fixture','Examples/claude/lifter/x64_copy_pinned','Examples/claude/lifter/x64_scalar_smoke','Examples/claude/lifter/x64_scalar_fixture','notes/e26-x86-sse-avx-lowering']
subprocess.run(['git','diff','--exit-code',checkpoint,'--',*protected],check=True)
owned=lambda name:name=='dune' or name.startswith(('notes/e34-x86-copy-shuffles/','Examples/claude/lifter/x64_shuffle_')) or name in ['tools/ghidra-lifter/'+n for n in ('pcode2coq_x64_shuffle.py','x64_shuffle_headless.py','lift-x64-shuffle.py','test_x64_shuffle.py')]
for sha in run('rev-list',checkpoint+'..HEAD').splitlines():
    assert len(run('rev-list','--parents','-n','1',sha).split())==2,sha
    for name in run('diff-tree','--no-commit-id','--name-only','-r',sha).splitlines():assert owned(name),(sha,name)
for name in run('diff','--name-only',checkpoint).splitlines():assert owned(name),name
print('PASS exact eight assigned prerequisite commits; linear scoped e34 continuation only')
print('PASS protected e26/e25 sources, notes and generated artifacts byte-identical')
print('MERGE_BASE',run('merge-base','origin/llm_generated_proofs','HEAD'))
print(run('log','--oneline','origin/llm_generated_proofs..HEAD'))
print(run('diff','--stat','origin/llm_generated_proofs...HEAD'))
