#!/usr/bin/env python3
"""Reproduce old generated lifts and exhaust old profile acceptance predicates."""
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
root=Path(__file__).resolve().parents[2]
os.chdir(root)
spec=importlib.util.spec_from_file_location('front',root/'lifter/armv6m.py')
f=importlib.util.module_from_spec(spec); spec.loader.exec_module(f)
old={}
source=subprocess.check_output(['git','show','0bc7fec4dbbfddbe8c5c130b9bd15d1b7af10ba6:lifter/armv6m.py'],text=True)
exec(compile(source,'accepted-e19-frontend','exec'),old)
for profile in ('legacy-e03','primask-v1-base','primask-v1-up'):
    assert all(f.accepted16(x,profile)==old['accepted16'](x,profile) for x in range(65536))
    for a in (0xf3bf,0xf3ef,*range(0xf380,0xf390)):
        assert all(f.accepted32(a,b,profile)==old['accepted32'](a,b,profile) for b in range(65536))
print('PASS exhaustive old 16-bit and system/BL template 32-bit acceptance compatibility')
tool=Path('/home/charles/code/friends/.toolchains/e04-freertos-build')
bin=tool/'arm-gnu-toolchain-13.2.Rel1-x86_64-arm-none-eabi/bin'
objdump=str(bin/'arm-none-eabi-objdump')
elf=tool/'verified02-a/out/FreeRTOS-Cortex-M0.elf'
for name in ('ulSetInterruptMask','vClearInterruptMask'):
    assert (root/'Examples/FreeRTOSMask'/f'{name}_armv6m.v').read_text()==f.extract(str(elf),name,name,objdump,'primask-v1-base')
with tempfile.TemporaryDirectory(prefix='e20-e19-') as tmp:
    obj=Path(tmp)/'snippets.o'; elf=Path(tmp)/'snippets.elf'
    subprocess.run([str(bin/'arm-none-eabi-as'),'-mcpu=cortex-m0','-mthumb','-o',str(obj),'tests/armv6m_primask/snippets.s'],check=True)
    subprocess.run([str(bin/'arm-none-eabi-ld'),'-Ttext=0x1000','--entry=mask_fixture','-o',str(elf),str(obj)],check=True)
    assert (root/'tests/armv6m_primask/fixture.v').read_text()==f.extract(str(elf),'mask_fixture','mask_fixture',objdump,'primask-v1-up')
subprocess.run(['git','diff','--exit-code','0bc7fec4dbbfddbe8c5c130b9bd15d1b7af10ba6','--',
  'Picinae_armv6m.v','Examples/FreeRTOS','Examples/FreeRTOSMask','Examples/freertos',
  'tests/armv6m','tests/armv6m_primask','notes/e19-armv6m-primask','notes/e05-freertos-lifts','units/e03-armv6m-core'],check=True)
print('PASS old mask artifacts reproduce; original ISA/e03/e04/e05/e19 artifacts unchanged')
