#!/usr/bin/env python3
"""Exact new acceptance boundary plus actual ELF strict rejection probes."""
import importlib.util
import os
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
os.chdir(root)
spec = importlib.util.spec_from_file_location('front', root/'lifter/armv6m.py')
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)
new = 'primask-v1-base'
# Exhaust all halfwords: the only 16-bit acceptance delta is CPSIE/CPSID i.
assert [x for x in range(65536) if f.accepted16(x) != f.accepted16(x, new)] == [0xb662, 0xb672]
# All possible operand/SYSm bytes in the two recognized system templates.
for r in range(16):
    for sysm in range(256):
        expected = sysm == 16 and r not in (13, 15)
        assert f.accepted32(0xf3ef, 0x8000 + 256*r + sysm, new) == expected
        assert f.accepted32(0xf380+r, 0x8800+sysm, new) == expected
# Every single fixed-bit perturbation is excluded (unless it forms a legacy BL).
for a, b, variable1, variable2 in ((0xf3ef,0x8010,0,0x0f00), (0xf380,0x8810,0x000f,0)):
    for half in (0,1):
        for bit in range(16):
            if (variable1 if half == 0 else variable2) & (1 << bit):
                continue
            x, y = (a ^ (1 << bit), b) if half == 0 else (a, b ^ (1 << bit))
            assert f.accepted32(x,y,new) == f.accepted32(x,y), (hex(x),hex(y))
print('PASS exact 16-bit delta, all register/SYSm templates and fixed-bit mutations')

tool = Path('/home/charles/code/friends/.toolchains/e04-freertos-build')
elf = tool/'verified02-a/out/FreeRTOS-Cortex-M0.elf'
objdump = str(tool/'arm-gnu-toolchain-13.2.Rel1-x86_64-arm-none-eabi/bin/arm-none-eabi-objdump')
env = {**os.environ, 'OBJDUMP':objdump, 'PYTHON':sys.executable, 'PYTHONDONTWRITEBYTECODE':'1'}
for profile in ('legacy-e03','primask-v1-base','primask-v1-up'):
    for name in ('ulSetInterruptMask','vClearInterruptMask','vPortEnterCritical','vPortYield','fixture_assert_fail','PendSV_Handler','SVC_Handler'):
        symbol = name
        cmd = ['bash','armv6m_lifter.sh','--profile',profile,str(elf),'probe',symbol]
        proc = subprocess.run(cmd, capture_output=True, text=True, env=env)
        ok = profile != 'legacy-e03' and name in ('ulSetInterruptMask','vClearInterruptMask')
        print('COMMAND:',repr(cmd))
        print('EXIT_CODE:',proc.returncode)
        if ok:
            assert proc.returncode == 0 and proc.stdout and 'Unknown' not in proc.stdout
        else:
            assert proc.returncode == 1 and not proc.stdout
            # Must fail at the remaining instruction, not a missing symbol.
            assert 'unsupported instruction' in proc.stderr, proc.stderr
        print(proc.stderr,end='')
print('PASS real mask acceptance and retained barrier/WFI/PSP rejection boundaries')
