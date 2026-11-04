import hashlib,json,pathlib
r=pathlib.Path('.')
layout=json.loads((r/'Examples/freertos/cortex-m0/evidence/layout.json').read_text())
for key,value in {'TCB_t.sizeof':84,'TCB_t.xEventListItem':24,'ListItem_t.xItemValue':0,'TCB_t.uxPriority':44,'TickType_t.sizeof':4,'void *.sizeof':4}.items():
    assert layout[key]==value
    print(key, value)
p=r/'Examples/freertos/cortex-m0/FreeRTOSConfig.h'
assert '#define configMAX_PRIORITIES                      5U' in p.read_text()
print('configMAX_PRIORITIES=5U')
p=pathlib.Path('/home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/source/FreeRTOS-Kernel-dbf70559b27d39c1fdb68dfb9a32140b6a6777a0/tasks.c')
assert hashlib.sha256(p.read_bytes()).hexdigest()=='6a54883765441f12b45b7f2e36838727e8e0aa872054df30c814c473ee3e4149'
print('tasks.c SHA256 verified; lines 7569-7584:')
print('\n'.join(p.read_text().splitlines()[7568:7584]))
m=json.loads((r/'Examples/FreeRTOS/uxTaskResetEventItemValue.json').read_text())
assert not m['closure_prerequisites'] and not m['unsupported_instructions']
assert m['literals'][0]['value']=='0x20000108'
assert m['literals'][0]['globals'][0]['name']=='pxCurrentTCB'
p=r/'Examples/FreeRTOS/uxTaskResetEventItemValue_armv6m.v'
assert hashlib.sha256(p.read_bytes()).hexdigest()==m['generated_sha256']
print('Unchanged generated lift SHA256:',m['generated_sha256'])
print('Inherited ELF SHA256:',m['elf_sha256'])
print('Entry, exit, call-free artifact:',m['entry'],m['return_candidates'],m['closure_prerequisites'])
for i in m['instructions']: print(i['address'],i['opcode'],i['assembly'])
