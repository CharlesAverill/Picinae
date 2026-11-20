"""Read-only check of the assigned pinned source/config/layout/lift evidence."""
import gzip
import hashlib
import json
from pathlib import Path

fixture = Path('Examples/freertos/cortex-m0')
evidence = fixture / 'evidence'
manifest = json.loads((evidence / 'manifest.json').read_text())
lift = Path('Examples/FreeRTOS/vTaskSuspendAll_armv6m.v')
record = json.loads(Path('Examples/FreeRTOS/vTaskSuspendAll.json').read_text())
source = Path('/home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/source/FreeRTOS-Kernel-dbf70559b27d39c1fdb68dfb9a32140b6a6777a0/tasks.c')
elf = source.parent.parent.parent / 'out/FreeRTOS-Cortex-M0.elf'

def check(path, digest):
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    assert actual == digest, (str(path), actual, digest)
    print(actual, path)

assert manifest['inputs']['kernel']['commit'] == 'dbf70559b27d39c1fdb68dfb9a32140b6a6777a0'
assert manifest['inputs']['kernel']['release'] == 'V11.1.0'
check(source, record['source'][0]['sha256'])
check(fixture/'FreeRTOSConfig.h', manifest['fixture_files']['FreeRTOSConfig.h'])
check(evidence/'layout.json', manifest['artifacts']['layout.json'])
check(evidence/'symbols.json', manifest['artifacts']['symbols.json'])
check(lift, record['generated_sha256'])
assert record['elf_sha256'] == manifest['artifacts']['FreeRTOS-Cortex-M0.elf']
# The installed fixture is read only; its ELF is checked if still present.
elf = Path('/home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/out/FreeRTOS-Cortex-M0.elf')
check(elf, record['elf_sha256'])
layout = json.loads((evidence/'layout.json').read_text())
assert layout['UBaseType_t.sizeof'] == 4
assert layout['UBaseType_t.alignof'] == 4
symbols = json.loads((evidence/'symbols.json').read_text())
for name in ['uxSchedulerSuspended', 'vTaskSuspendAll']:
    rows = [s for s in symbols if s['name'] == name]
    assert len(rows) == 1
    print(json.dumps(rows[0], sort_keys=True))
    if name == 'uxSchedulerSuspended':
        assert rows[0]['address'] == '0x20000008' and rows[0]['size'] == 4
assert record['entry'] == '0x00000574'
assert record['closure_prerequisites'] == []
assert record['blocked_helpers'] == []
assert record['unsupported_instructions'] == []
assert record['literals'][0]['globals'] == [dict(address='0x20000008', name='uxSchedulerSuspended', offset=0, size=4)]
for i in record['instructions']:
    print(i['address'], i['opcode'], i['assembly'])
config = gzip.decompress((evidence/'config-macros.txt.gz').read_bytes())
assert hashlib.sha256(config).hexdigest() == manifest['artifacts']['config-macros.txt']
for line in config.decode().splitlines():
    if any(x in line for x in ['configNUMBER_OF_CORES ', 'configUSE_TRACE_FACILITY ', 'traceENTER_vTaskSuspendAll', 'traceRETURN_vTaskSuspendAll', 'portMEMORY_BARRIER', 'portSOFTWARE_BARRIER']):
        print(line)
print('Pinned tasks.c lines 3811-3833:')
print('\n'.join(source.read_text().splitlines()[3810:3833]))
print('PASS: pinned global address/size/offset and call-free instruction path; no hardware refinement claimed')
