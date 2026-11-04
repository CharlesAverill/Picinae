#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
fixture=Path('Examples/freertos/cortex-m0')
manifest=json.loads(Path('Examples/FreeRTOS/prvSearchForNameWithinSingleList.json').read_text())
source=Path('/home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/source/FreeRTOS-Kernel-dbf70559b27d39c1fdb68dfb9a32140b6a6777a0/tasks.c')
assert hashlib.sha256(source.read_bytes()).hexdigest()==manifest['source'][0]['sha256']
lift=Path('Examples/FreeRTOS/prvSearchForNameWithinSingleList_armv6m.v')
assert hashlib.sha256(lift.read_bytes()).hexdigest()==manifest['generated_sha256']
assert manifest['closure_prerequisites']==[]
assert manifest['unsupported_instructions']==[]
assert manifest['literals']==[] and manifest['mapped_data']==[]
layout=json.loads((fixture/'evidence/layout.json').read_text())
expected={'List_t.sizeof':20,'List_t.uxNumberOfItems':0,'List_t.xListEnd':8,'MiniListItem_t.pxNext':4,'ListItem_t.sizeof':20,'ListItem_t.pxNext':4,'ListItem_t.pvOwner':12,'TCB_t.sizeof':84,'TCB_t.pcTaskName':52}
for name,value in expected.items(): assert layout[name]==value
assert '#define configMAX_TASK_NAME_LEN                  16U' in (fixture/'FreeRTOSConfig.h').read_text()
print('PASS: pinned tasks.c hash and unchanged generated lift hash')
print('PASS: 34 instructions, no callee prerequisites, unsupported instructions, literals or globals')
print('Actual return:',manifest['return_candidates'])
print('Compiler layout:',json.dumps(expected,sort_keys=True))
print('Source hash:',manifest['source'][0]['sha256'])
print('Generated hash:',manifest['generated_sha256'])
print('ELF hash (inherited manifest, not independently relifted):',manifest['elf_sha256'])
