"""Read-only checks against the accepted pinned source/config/ELF evidence."""
from pathlib import Path
import hashlib
import json

fixture = Path('Examples/freertos/cortex-m0')
manifest = json.loads((fixture / 'evidence/manifest.json').read_text())
source = Path('/home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/source/FreeRTOS-Kernel-dbf70559b27d39c1fdb68dfb9a32140b6a6777a0')
for name, lo, hi in [('tasks.c', 4106, 4122), ('portable/GCC/ARM_CM0/portmacro.h', 65, 81), ('include/FreeRTOS.h', 2888, 2905)]:
    data = (source / name).read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    assert digest == manifest['source_files'][name]
    print(name, 'SHA256', digest)
    for number, line in enumerate(data.decode().splitlines(), 1):
        if lo <= number <= hi:
            print(f'{number}: {line}')
assert hashlib.sha256((fixture / 'FreeRTOSConfig.h').read_bytes()).hexdigest() == manifest['fixture_files']['FreeRTOSConfig.h']
layout = json.loads((fixture / 'evidence/layout.json').read_text())
assert layout['TickType_t.sizeof'] == layout['void *.sizeof'] == 4
print('TickType_t and void * sizes:', layout['TickType_t.sizeof'], layout['void *.sizeof'])
for line in (fixture / 'FreeRTOSConfig.h').read_text().splitlines():
    if any(key in line for key in ['configTICK_TYPE_WIDTH_IN_BITS', 'configNUMBER_OF_CORES', 'configUSE_TRACE_FACILITY']):
        print(line)
for line in (fixture / 'evidence/nm.txt').read_text().splitlines():
    if 'xTickCount' in line or 'xTaskGetTickCount' in line:
        print(line)
lift = json.loads(Path('Examples/FreeRTOS/xTaskGetTickCount.json').read_text())
assert lift['closure_prerequisites'] == lift['blocked_helpers'] == lift['unsupported_instructions'] == []
assert lift['literals'][0]['globals'] == [{'address': '0x2000002c', 'name': 'xTickCount', 'offset': 0, 'size': 4}]
assert lift['elf_sha256'] == manifest['artifacts']['FreeRTOS-Cortex-M0.elf']
print('ELF SHA256:', lift['elf_sha256'])
print('Literal/object evidence:', lift['literals'])
print('Instructions:', lift['instructions'])
print('PASS: pinned source hashes, configuration, sizes, global address and call-free manifest')
