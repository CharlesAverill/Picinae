#!/usr/bin/env python3
"""Every mixed successful/failed batch must reject all output, including staging."""
import pathlib
import subprocess
import sys

state = pathlib.Path('/home/charles/code/friends/.toolchains/e11-canonical-lifter')
repo = pathlib.Path(__file__).resolve().parents[2]
for label, symbols in [('symbol', ['toascii', 'e11_symbol_does_not_exist']),
                       ('relative-call', ['mempcpy']),
                       ('instruction-asimd', ['toascii', '__memcpy_simd']),
                       ('instruction-tls', ['toascii', 'sigaddset']),
                       ('instruction-zva', ['toascii', '__memset_generic']),
                       ('instruction-sve', ['toascii', '__memcpy_a64fx']),
                       ('instruction-mte', ['toascii', '__strlen_mte'])]:
    out = state/('reject-'+label)
    command = [sys.executable, str(repo/'tools/ghidra-lifter/lift-scalar.py'), '--out',str(out),*symbols]
    print('COMMAND='+repr(command),flush=True)
    result = subprocess.run(command)
    print(f'EXPECTED_EXIT=1 ACTUAL_EXIT={result.returncode}',flush=True)
    assert result.returncode == 1
    assert not out.exists()
    assert not list(state.glob('.e11-stage-*'))
# Unsupported opcode must raise through a process boundary, never emit Nop.
op_command = [sys.executable, '-c',
              'import sys; sys.path.insert(0, '+repr(str(repo/'tools/ghidra-lifter'))+'); '
              'from test_scalar import *; '
              'ScalarLifter(Language()).instruction(Insn("mov",Op("CALLOTHER",None,VN("constant",0,4))))']
print('COMMAND='+repr(op_command),flush=True)
result = subprocess.run(op_command, env={**__import__('os').environ, 'PYTHONDONTWRITEBYTECODE':'1'})
assert result.returncode == 1
print('EXPECTED_OPCODE_EXIT=1 ACTUAL_EXIT='+str(result.returncode))
print('PASS seven failing batches and unsupported-op subprocess: nonzero, no accepted or partial output')
