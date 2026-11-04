#!/usr/bin/env python3
import subprocess
from pathlib import Path
base='49956416928e5b6bb3928b54ae33e3b81091f006'
checkpoint='328088263ebba11786a03448808e584231504fe1'
run=lambda *args:subprocess.check_output(['git',*args],text=True).strip()
notes=Path(__file__).resolve().parent
allowed=set((notes/'allowed-prerequisites.txt').read_text().splitlines())
assert run('rev-parse','origin/llm_generated_proofs')==base
assert run('merge-base','origin/llm_generated_proofs','HEAD')==base
assert run('branch','--show-current')=='llm-proofs/e26-x86-sse-avx-lowering'
assert set(run('rev-list',base+'..'+checkpoint).splitlines())==allowed
subprocess.run(['git','merge-base','--is-ancestor',checkpoint,'HEAD'],check=True)
protected=['tools/ghidra-lifter/pcode2coq_x64.py','tools/ghidra-lifter/lift-x64.py','tools/ghidra-lifter/x64_headless.py','Examples/claude/lifter/x64_scalar_smoke','Examples/claude/lifter/x64_scalar_fixture']
subprocess.run(['git','diff','--exit-code',checkpoint,'--',*protected],check=True)
# A unit-owned continuation must be linear and may touch only assigned files.
for sha in run('rev-list',checkpoint+'..HEAD').splitlines():
    assert len(run('rev-list','--parents','-n','1',sha).split())==2,sha
    for name in run('diff-tree','--no-commit-id','--name-only','-r',sha).splitlines():
        assert name=='dune' or name.startswith(('notes/e26-x86-sse-avx-lowering/','Examples/claude/lifter/x64_copy_')) or name in ['tools/ghidra-lifter/'+n for n in ('pcode2coq_x64_copy.py','x64_copy_headless.py','lift-x64-copy.py','test_x64_copy.py')],(sha,name)
print('PASS exact seven authorized prerequisites + linear unit-owned continuation; e25 code and all scalar artifacts byte-identical')
print('MERGE_BASE',run('merge-base','origin/llm_generated_proofs','HEAD'))
print(run('log','--oneline','origin/llm_generated_proofs..HEAD'))
