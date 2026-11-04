import hashlib,json,pathlib
root=pathlib.Path('Examples/freertos/cortex-m0')
src=pathlib.Path('/home/charles/code/friends/.toolchains/e04-freertos-build/FreeRTOS-Kernel-dbf70559b27d39c1fdb68dfb9a32140b6a6777a0')
manifest=json.loads(pathlib.Path('Examples/FreeRTOS/prvResetNextTaskUnblockTime.json').read_text())
for name in ['tasks.c','include/list.h']:
 p=src/name
 digest=hashlib.sha256(p.read_bytes()).hexdigest()
 print(p,digest)
 if name=='tasks.c': assert digest==manifest['source'][0]['sha256']
for name in ['FreeRTOSConfig.h','inputs.json','evidence/layout.json','evidence/nm.txt']:
 p=root/name
 print(p,hashlib.sha256(p.read_bytes()).hexdigest())
layout=json.loads((root/'evidence/layout.json').read_text())
for field in ['List_t.sizeof','List_t.uxNumberOfItems','List_t.xListEnd','MiniListItem_t.sizeof','MiniListItem_t.pxNext','ListItem_t.xItemValue','TickType_t.sizeof','void *.sizeof']:
 print(field,layout[field])
for line in (root/'evidence/nm.txt').read_text().splitlines():
 if 'pxDelayedTaskList' in line or 'xNextTaskUnblockTime' in line: print(line)
print('\n'.join((src/'tasks.c').read_text().splitlines()[6455:6474]))
for line in (src/'include/list.h').read_text().splitlines():
 if line.startswith('#define listGET_ITEM_VALUE_OF_HEAD_ENTRY') or line.startswith('#define listLIST_IS_EMPTY'): print(line)
print('ELF:',manifest['elf_sha256'])
print('Call prerequisites:',manifest['closure_prerequisites'])
print('Unsupported:',manifest['unsupported_instructions'])
p=pathlib.Path('Examples/FreeRTOS/prvResetNextTaskUnblockTime_armv6m.v')
assert hashlib.sha256(p.read_bytes()).hexdigest()==manifest['generated_sha256']
print('Unchanged generated lift SHA256:',manifest['generated_sha256'])
