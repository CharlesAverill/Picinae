import hashlib,json,pathlib
r=pathlib.Path('.')
m=json.loads((r/'Examples/freertos/cortex-m0/evidence/manifest.json').read_text())
a=json.loads((r/'Examples/FreeRTOS/pvTaskIncrementMutexHeldCount.json').read_text())
s=pathlib.Path('/home/charles/code/friends/.toolchains/e04-freertos-build/FreeRTOS-Kernel-dbf70559b27d39c1fdb68dfb9a32140b6a6777a0/tasks.c')
assert hashlib.sha256(s.read_bytes()).hexdigest()==m['source_files']['tasks.c']==a['source'][0]['sha256']
for p,k in [('Examples/freertos/cortex-m0/FreeRTOSConfig.h','FreeRTOSConfig.h')]:
 assert hashlib.sha256((r/p).read_bytes()).hexdigest()==m['fixture_files'][k]
assert hashlib.sha256((r/'Examples/freertos/cortex-m0/evidence/layout.json').read_bytes()).hexdigest()==m['artifacts']['layout.json']
assert hashlib.sha256((r/'Examples/FreeRTOS/pvTaskIncrementMutexHeldCount_armv6m.v').read_bytes()).hexdigest()==a['generated_sha256']
assert not a['closure_prerequisites'] and not a['unsupported_instructions'] and not a['blocked_helpers']
print('Source',s,'sha256',a['source'][0]['sha256'])
print('ELF SHA256',a['elf_sha256']); print('Kernel',m['inputs']['kernel']['commit'])
print('Config SHA256',m['fixture_files']['FreeRTOSConfig.h'])
print('Layout SHA256',m['artifacts']['layout.json'])
layout=json.loads((r/'Examples/freertos/cortex-m0/evidence/layout.json').read_text())
print({k:v for k,v in layout.items() if k.startswith(('TCB_t.','UBaseType_t.','void *.'))})
print(json.dumps(a['literals'],indent=2)); print(json.dumps(a['instructions'],indent=2))
print('\n'.join(s.read_text().splitlines()[7586:7609]))
print('All selected pinned source/config/layout/generated hashes match. No call/unsupported-operation dependencies.')
