#!/usr/bin/env python3
"""Independent ELF fixtures testing strict failure with zero Coq stdout."""
import os
from pathlib import Path
import subprocess
import sys

out = Path(sys.argv[1])


def reject(label, args, env=None):
    result = subprocess.run(['./armv6m_lifter.sh', *map(str, args)],
                            capture_output=True, env=env)
    assert result.returncode != 0, f'{label}: unexpectedly accepted'
    assert result.stdout == b'', f'{label}: emitted partial output'
    print(f'PASS reject {label}: exit={result.returncode}; {result.stderr.decode().strip()}')


reject('relocatable', [out / 'snippets.o', 'bad'])
reject('missing function', [out / 'snippets.elf', 'bad', 'absent'])
reject('invalid definition name', [out / 'snippets.elf', 'bad*)Axiom'])
reject('missing objdump', [out / 'snippets.elf', 'bad'], {**os.environ, 'OBJDUMP': '/nonexistent/objdump'})
reject('failing objdump', [out / 'snippets.elf', 'bad'], {**os.environ, 'OBJDUMP': '/bin/false'})
reject('unset objdump', [out / 'snippets.elf', 'bad'], {k: v for k, v in os.environ.items() if k != 'OBJDUMP'})
reject('missing file', [out / 'absent.elf', 'bad'])

cases = {
    'undefined': 'udf #0',
    'cpsid': 'cpsid i',
    'cpsie': 'cpsie i',
    'mrs': 'mrs r0, primask',
    'msr': 'msr primask, r0',
    'dmb': 'dmb',
    'dsb': 'dsb',
    'isb': 'isb',
    'svc': 'svc #0',
    'bkpt': 'bkpt #0',
    'wfi': 'wfi',
    'wfe': 'wfe',
    'sev': 'sev',
    'yield': 'yield',
    'unknown_hint': '.inst.n 0xbf50',
    'thumb2_movw': '.inst.w 0xf2400000',
    'truncated_bl': '.inst.n 0xf000',
    'unpredictable_stm': '.inst.n 0xc103',
    'empty_push': '.inst.n 0xb400',
    'empty_pop': '.inst.n 0xbc00',
    'unpredictable_cmp': '.inst.n 0x4500',
    'missing_literal': 'ldr r0, [pc, #1020]',
}
for label, code in cases.items():
    src, obj, elf = (out / f'{label}{suffix}' for suffix in ('.s', '.o', '.elf'))
    src.write_text('.syntax unified\n.cpu cortex-m0\n.thumb\n.text\n.global bad\n'
                   '.type bad, %function\n.thumb_func\nbad:\n' + code + '\n.size bad, .-bad\n')
    subprocess.run(['arm-linux-gnueabi-as', '-mcpu=cortex-m0', '-mthumb', '-o', str(obj), str(src)], check=True)
    subprocess.run(['arm-linux-gnueabi-ld', '-Ttext=0x1000', '--entry=bad', '-o', str(elf), str(obj)], check=True)
    reject(label, [elf, 'bad_bytes', 'bad'])

# Stripping removes the ELF mapping symbols required to distinguish code/data.
stripped = out / 'stripped.elf'
subprocess.run(['arm-linux-gnueabi-strip', '-o', str(stripped), str(out / 'snippets.elf')], check=True)
reject('stripped', [stripped, 'bad'])
# Retained relocations are refused even for an ET_EXEC input.
relocs = out / 'relocs.elf'
subprocess.run(['arm-linux-gnueabi-ld', '--emit-relocs', '-Ttext=0x1000', '--entry=fixture',
                '-o', str(relocs), str(out / 'snippets.o')], check=True)
reject('retained relocations', [relocs, 'bad'])

# Corrupt just the section's declared size so only the low half of the literal
# word exists. The original input is otherwise a valid linked executable.
import struct
data = bytearray((out / 'snippets.elf').read_bytes())
shoff = struct.unpack_from('<I', data, 32)[0]
shnum = struct.unpack_from('<H', data, 48)[0]
for i in range(shnum):
    sh = shoff + i * 40
    flags, address = struct.unpack_from('<II', data, sh + 8)
    if flags & 6 == 6 and address == 0x1000:
        struct.pack_into('<I', data, sh + 20, 0x12)
partial = out / 'partial-pool.elf'
partial.write_bytes(data)
reject('partial literal word', [partial, 'bad', 'fixture'])

data = bytearray((out / 'snippets.elf').read_bytes())
for i in range(shnum):
    sh = shoff + i * 40
    flags, address = struct.unpack_from('<II', data, sh + 8)
    if flags & 6 == 6 and address == 0x1000:
        struct.pack_into('<I', data, sh + 8, flags | 1)
writable = out / 'writable-pool.elf'
writable.write_bytes(data)
reject('writable literal word', [writable, 'bad', 'fixture'])
