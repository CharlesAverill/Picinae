import gzip, hashlib, json
from pathlib import Path
fixture=Path('Examples/freertos/cortex-m0')
source=Path('/home/charles/code/friends/.toolchains/e04-freertos-build/verified02-a/source/FreeRTOS-Kernel-dbf70559b27d39c1fdb68dfb9a32140b6a6777a0')
manifest=json.loads((fixture/'evidence/manifest.json').read_text())
print('Pinned input:',json.dumps(json.loads((fixture/'inputs.json').read_text())['kernel'],sort_keys=True))
for name,lo,hi in [('tasks.c',6537,6575),('include/task.h',273,278),('include/projdefs.h',50,60)]:
 p=source/name
 digest=hashlib.sha256(p.read_bytes()).hexdigest()
 print(name,'sha256',digest)
 assert digest==manifest['source_files'][name] if 'source_files' in manifest else digest in str(manifest)
 for i,line in enumerate(p.read_text().splitlines(),1):
  if lo<=i<=hi: print(f'{i}: {line}')
for name in ['FreeRTOSConfig.h','evidence/layout.json','evidence/nm.txt']:
 p=fixture/name
 print(name,'sha256',hashlib.sha256(p.read_bytes()).hexdigest())
 for line in p.read_text().splitlines():
  if any(x in line for x in ['BaseType_t','void *','configNUMBER_OF_CORES','INCLUDE_xTaskGetSchedulerState','configUSE_TIMERS','xSchedulerRunning','uxSchedulerSuspended','xTaskGetSchedulerState']):print(line)
lift=Path('Examples/FreeRTOS/xTaskGetSchedulerState_armv6m.v')
m=json.loads(lift.with_name('xTaskGetSchedulerState.json').read_text())
assert hashlib.sha256(lift.read_bytes()).hexdigest()==m['generated_sha256']
assert not m['closure_prerequisites'] and not m['unsupported_instructions'] and not m['blocked_helpers']
print('Manifest:',json.dumps(m,indent=2))
