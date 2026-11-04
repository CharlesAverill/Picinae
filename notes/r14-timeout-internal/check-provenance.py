import hashlib,json,pathlib
root=pathlib.Path('Examples/freertos/cortex-m0')
manifest=json.loads((root/'evidence/manifest.json').read_text())
src=pathlib.Path('/home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/source/FreeRTOS-Kernel-dbf70559b27d39c1fdb68dfb9a32140b6a6777a0')
for name in ['tasks.c','include/task.h']:
    f=src/name; sha=hashlib.sha256(f.read_bytes()).hexdigest()
    assert sha==manifest['source_files'][name]
    print(f'{f}: SHA256 {sha} MATCH')
    lines=f.read_text().splitlines()
    a,b=(5522,5531) if name=='tasks.c' else (125,129)
    for n in range(a,b+1):print(f'{n}: {lines[n-1]}')
for name in ['FreeRTOSConfig.h','layout-probe.c']:
    sha=hashlib.sha256((root/name).read_bytes()).hexdigest()
    assert sha==manifest['fixture_files'][name]
    print(f'{name}: SHA256 {sha} MATCH')
layout=root/'evidence/layout.json'
assert hashlib.sha256(layout.read_bytes()).hexdigest()==manifest['artifacts']['layout.json']
for k,v in json.loads(layout.read_text()).items():
    if k.startswith(('TimeOut_t.','TickType_t.','BaseType_t.','void *.')):print(k,v)
lift=pathlib.Path('Examples/FreeRTOS/vTaskInternalSetTimeOutState_armv6m.v')
meta=json.loads(lift.with_name('vTaskInternalSetTimeOutState.json').read_text())
assert hashlib.sha256(lift.read_bytes()).hexdigest()==meta['generated_sha256']
assert not meta['closure_prerequisites'] and not meta['unsupported_instructions']
print('Generated lift hash MATCH; no call closure or unsupported instruction.')
print('ELF SHA256',meta['elf_sha256'])
for l in meta['literals']:print('Literal globals:',l['globals'])
for ins in meta['instructions']:print(ins['address'],ins['opcode'],ins['assembly'])
