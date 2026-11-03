#!/usr/bin/env python3
"""Reproduce e19 artifacts from read-only tools/input; standard library only."""
import hashlib
import importlib.util
import os
import resource
from pathlib import Path
import subprocess
import sys

resource.setrlimit(resource.RLIMIT_AS, (2000000*1024, 2000000*1024))
resource.setrlimit(resource.RLIMIT_STACK, (65536*1024, 65536*1024))
ROOT = Path(__file__).resolve().parents[2]
os.chdir(ROOT)
spec = importlib.util.spec_from_file_location('frontend', ROOT / 'lifter/armv6m.py')
front = importlib.util.module_from_spec(spec)
spec.loader.exec_module(front)
tool = Path('/home/charles/code/friends/.toolchains/e04-freertos-build')
bin = tool / 'arm-gnu-toolchain-13.2.Rel1-x86_64-arm-none-eabi/bin'
elf = tool / 'verified02-a/out/FreeRTOS-Cortex-M0.elf'
assert hashlib.sha256(elf.read_bytes()).hexdigest() == '5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca'
check = '--check' in sys.argv

def run(args):
    print('COMMAND:', repr(list(map(str, args))), flush=True)
    proc = subprocess.run(list(map(str, args)), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    print(proc.stdout, end='', flush=True)
    print('EXIT_CODE:', proc.returncode, flush=True)
    assert proc.returncode == 0
    return proc.stdout

def save(path, text):
    if check:
        assert path.read_text() == text, f'artifact differs: {path}'
    else:
        path.write_text(text)

out = ROOT / 'tests/armv6m_primask'
run([bin/'arm-none-eabi-as', '-mcpu=cortex-m0', '-mthumb', '-o', out/'snippets.o', out/'snippets.s'])
run([bin/'arm-none-eabi-ld', '-Ttext=0x1000', '--entry=mask_fixture', '-o', out/'snippets.elf', out/'snippets.o'])
dump = run([bin/'arm-none-eabi-objdump', '-d', '-s', out/'snippets.elf'])
save(ROOT/'notes/e19-armv6m-primask/logs/snippets.objdump', dump)
save(out/'fixture.v', front.extract(str(out/'snippets.elf'), 'mask_fixture', 'mask_fixture', str(bin/'arm-none-eabi-objdump'), 'primask-v1-up'))
for name in ('ulSetInterruptMask', 'vClearInterruptMask'):
    save(ROOT/'Examples/FreeRTOSMask'/f'{name}_armv6m.v',
         front.extract(str(elf), name, name, str(bin/'arm-none-eabi-objdump'), 'primask-v1-base'))
print('PASS: real mask lifts and independently assembled fixture reproduce')
