#!/usr/bin/env python3
"""Real launcher failures (including swallowed exceptions) accept no artifact."""
from pathlib import Path
import subprocess
import sys
import tempfile

repo=Path(__file__).resolve().parents[2]
state=Path('/home/charles/code/friends/.toolchains/e25-x86-scalar-driver')
run=Path(tempfile.mkdtemp(prefix='negative.',dir=state))
cases=[('missing',['--cet-disabled'],['e25_missing_symbol']),
       ('mixed-missing',['--cet-disabled'],['toascii','e25_missing_symbol']),
       ('cet-default',[],['toascii']),
       ('mixed-vector',['--fixture'],['scalar_caller','scalar_callee','unsupported_vector']),
       ('indirect-call',['--fixture'],['unsupported_indirect']),
       ('rep',['--fixture'],['unsupported_rep']),
       ('unclosed-call',['--fixture'],['scalar_caller'])]
for name,flags,names in cases:
    out=run/name
    cmd=[sys.executable,str(repo/'tools/ghidra-lifter/lift-x64.py'),*flags,'--out',str(out),*names]
    print('COMMAND='+repr(cmd),flush=True)
    r=subprocess.run(cmd)
    print('EXPECTED_EXIT=1 ACTUAL_EXIT='+str(r.returncode),flush=True)
    assert r.returncode==1 and not out.exists()
    assert not list(run.glob('.e25-stage-*'))
# Existing output rejection runs before launching Java and preserves sentinel.
out=run/'existing';out.mkdir();(out/'sentinel').write_text('unchanged')
cmd=[sys.executable,str(repo/'tools/ghidra-lifter/lift-x64.py'),'--out',str(out),'abs']
print('COMMAND='+repr(cmd),flush=True)
r=subprocess.run(cmd)
assert r.returncode==2 and (out/'sentinel').read_text()=='unchanged'
print('EXPECTED_EXIT=2 ACTUAL_EXIT='+str(r.returncode),flush=True)
# A broken symlink is still an existing destination and must be rejected.
link=run/'existing-link';link.symlink_to(run/'absent')
cmd=[sys.executable,str(repo/'tools/ghidra-lifter/lift-x64.py'),'--out',str(link),'abs']
print('COMMAND='+repr(cmd),flush=True)
r=subprocess.run(cmd)
assert r.returncode==2 and link.is_symlink() and not (run/'absent').exists()
print('EXPECTED_EXIT=2 ACTUAL_EXIT='+str(r.returncode),flush=True)
# Real subprocess boundary: unknown userop/register and malformed branch raise
# nonzero, never a successful Nop. Actual Ghidra failures above log launcher 0.
for expr in ["Insn('MOV',Op('CALLOTHER',None,VN('constant',0,4)))",
             "Insn('MOV',Op('COPY',VN('register',999,8),VN('constant',0,8)))",
             "Insn('JZ',Op('CBRANCH',None,VN('constant',0,8)))"]:
    code="import sys; sys.path.insert(0,"+repr(str(repo/'tools/ghidra-lifter'))+"); from test_x64 import *; X64Lifter(Language()).instruction("+expr+")"
    cmd=[sys.executable,'-c',code]
    print('COMMAND='+repr(cmd),flush=True)
    r=subprocess.run(cmd)
    assert r.returncode==1
    print('EXPECTED_EXIT=1 ACTUAL_EXIT='+str(r.returncode),flush=True)
print('PASS real strict negative batches, stale-output refusal and opcode/register/branch subprocesses; no partial publication')
