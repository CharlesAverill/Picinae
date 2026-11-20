"""Check this leaf against the inherited pinned fixture, read-only."""
from pathlib import Path
import gzip
import hashlib
import json
root = Path('Examples/freertos/cortex-m0')
manifest = json.loads((root/'evidence/manifest.json').read_text())
leaf = json.loads(Path('Examples/FreeRTOS/xTaskGetTickCountFromISR.json').read_text())
layout = json.loads((root/'evidence/layout.json').read_text())
source = Path('/home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/source/FreeRTOS-Kernel-dbf70559b27d39c1fdb68dfb9a32140b6a6777a0')
elf = source.parent.parent/'out/FreeRTOS-Cortex-M0.elf'
def check_hash(path, expected):
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    print(path, actual)
    assert actual == expected, (path, actual, expected)
assert manifest['inputs']['kernel']['commit'] == 'dbf70559b27d39c1fdb68dfb9a32140b6a6777a0'
check_hash(elf, leaf['elf_sha256'])
check_hash(source/'tasks.c', leaf['source'][0]['sha256'])
for name in ['portable/GCC/ARM_CM0/portmacro.h', 'include/FreeRTOS.h']:
    check_hash(source/name, manifest['source_files'][name])
check_hash(root/'FreeRTOSConfig.h', manifest['fixture_files']['FreeRTOSConfig.h'])
check_hash(root/'evidence/layout.json', manifest['artifacts']['layout.json'])
check_hash(Path('Examples/FreeRTOS/xTaskGetTickCountFromISR_armv6m.v'), leaf['generated_sha256'])
assert layout['TickType_t.sizeof'] == layout['void *.sizeof'] == 4
assert leaf['closure_prerequisites'] == leaf['blocked_helpers'] == leaf['unsupported_instructions'] == []
assert leaf['literals'][0]['globals'] == [{'address': '0x2000002c', 'name': 'xTickCount', 'offset': 0, 'size': 4}]
print('Global:', leaf['literals'][0]['globals'])
print('Instructions:', leaf['instructions'])
print('Entry/return:', leaf['entry'], leaf['return_candidates'])
text = (source/'tasks.c').read_text()
a = text.index('TickType_t xTaskGetTickCountFromISR( void )')
b = text.index('/*-----------------------------------------------------------*/', a)
print('Pinned tasks.c function:\n'+text[a:b])
for name, needles in [('portable/GCC/ARM_CM0/portmacro.h', ['typedef uint32_t', 'portTICK_TYPE_IS_ATOMIC']), ('include/FreeRTOS.h', ['portTICK_TYPE_SET_INTERRUPT_MASK_FROM_ISR', 'portTICK_TYPE_CLEAR_INTERRUPT_MASK_FROM_ISR', 'portASSERT_IF_INTERRUPT_PRIORITY_INVALID'])]:
    lines = (source/name).read_text().splitlines()
    for i, line in enumerate(lines, 1):
        if any(needle in line for needle in needles):
            print(f'{name}:{i}: {line}')
macros = gzip.decompress((root/'evidence/config-macros.txt.gz').read_bytes()).decode()
for line in macros.splitlines():
    if any(key in line for key in ['configTICK_TYPE_WIDTH_IN_BITS ', 'portTICK_TYPE_IS_ATOMIC ', 'portTICK_TYPE_SET_INTERRUPT_MASK_FROM_ISR(', 'portTICK_TYPE_CLEAR_INTERRUPT_MASK_FROM_ISR(', 'portASSERT_IF_INTERRUPT_PRIORITY_INVALID(']):
        print('Compiled macro:', line)
print('PASS: pinned source/config/layout and unchanged accepted call-free artifact.')
print('This evidence is not a binary/lifter refinement or asynchronous atomicity proof.')
