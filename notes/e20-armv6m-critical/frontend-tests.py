#!/usr/bin/env python3
"""Finite acceptance deltas, reserved encodings, and atomic ELF publication tests."""
import importlib.util
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[2]
os.chdir(root)
spec = importlib.util.spec_from_file_location('front', root/'lifter/armv6m.py')
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)
new = 'critical-seq-v1-base'
assert all(f.accepted16(x,new) == f.accepted16(x,'primask-v1-base') for x in range(65536))
assert [x for x in range(65536) if f.accepted32(0xf3bf,x,new) and not f.accepted32(0xf3bf,x,'primask-v1-base')] == [0x8f4f,0x8f5f,0x8f6f]
for a,b in ((0xf3bf,0x8f4f),(0xf3bf,0x8f5f),(0xf3bf,0x8f6f)):
    for half in (0,1):
        for bit in range(16):
            x,y = (a^(1<<bit),b) if half==0 else (a,b^(1<<bit))
            assert f.accepted32(x,y,new) == (f.accepted32(x,y,'primask-v1-base') or (x==0xf3bf and y in (0x8f4f,0x8f5f,0x8f6f))), (x,y)
for r in range(16):
    for n in range(256):
        for a,b in ((0xf3ef,0x8000+256*r+n),(0xf380+r,0x8800+n)):
            assert f.accepted32(a,b,new) == f.accepted32(a,b,'primask-v1-base')
print('PASS all 16-bit words, all barrier second halfwords/options, fixed-bit mutations, PRIMASK operands')

tool = Path('/home/charles/code/friends/.toolchains/e04-freertos-build')
elfpath = tool/'verified02-a/out/FreeRTOS-Cortex-M0.elf'
objdump = str(tool/'arm-gnu-toolchain-13.2.Rel1-x86_64-arm-none-eabi/bin/arm-none-eabi-objdump')
env = {**os.environ,'OBJDUMP':objdump,'PYTHON':sys.executable,'PYTHONDONTWRITEBYTECODE':'1'}
def probe(path,profile,name,ok,reason=None):
    cmd = ['bash','armv6m_lifter.sh','--profile',profile,str(path),'probe',name]
    p = subprocess.run(cmd,capture_output=True,text=True,env=env)
    print('COMMAND:',repr(cmd),'EXIT_CODE:',p.returncode)
    if ok:
        assert p.returncode==0 and p.stdout and not p.stderr
    else:
        assert p.returncode==1 and not p.stdout, p.stderr
        assert reason in p.stderr, p.stderr
        print(p.stderr,end='')
for profile in f.PROFILES:
    for name in ('vPortEnterCritical','vPortExitCritical','ulSetInterruptMask','vClearInterruptMask',
                 'vPortYield','fixture_assert_fail','PendSV_Handler','SVC_Handler'):
        if name=='vPortEnterCritical': ok=profile==new
        elif name in ('vPortExitCritical','ulSetInterruptMask','vClearInterruptMask'): ok=profile!='legacy-e03'
        else: ok=False
        reason = 'high/MMIO literal' if name=='vPortYield' and profile==new else 'unsupported instruction'
        probe(elfpath,profile,name,ok,reason)
# Patch only a private temporary ELF copy. Test all reserved options, bad fixed
# bits, and a supported prefix followed by unsupported WFI. No partial stdout.
elf = f.ELF(elfpath)
sec = next(s for s in elf.sections if s[3] <= 0x3e72 < s[3]+s[5] and s[1]==1)
offset = sec[4]+0x3e72-sec[3]
mutations = [(0xf3bf,0x8f40+x) for x in range(15)]
mutations += [(0xf3bf,0x8f50+x) for x in range(15)]
mutations += [(0xf3bf,0x8f60+x) for x in range(15)]
mutations += [(0xf3bf^(1<<b),0x8f4f) for b in range(16)
              if (0xf3bf^(1<<b)) >> 11 >= 29 and not f.accepted32(0xf3bf^(1<<b),0x8f4f,new)]
mutations += [(0xf3bf,0x8f4f^(1<<b)) for b in range(16)
              if not f.accepted32(0xf3bf,0x8f4f^(1<<b),new)]
with tempfile.TemporaryDirectory(prefix='e20-elf-') as tmp:
    path=Path(tmp)/'mutation.elf'
    for a,b in mutations:
        data=bytearray(elf.data)
        struct.pack_into('<HH',data,offset,a,b)
        path.write_bytes(data)
        probe(path,new,'vPortEnterCritical',False,'instruction')
    data=bytearray(elf.data)
    struct.pack_into('<H',data,offset,0xbf30) # WFI at first barrier
    path.write_bytes(data)
    probe(path,new,'vPortEnterCritical',False,'unsupported instruction')
print('PASS strict failed-output behavior, actual MMIO/WFI/PSP boundaries, old profile compatibility')
