#!/usr/bin/env python3
"""Snapshot exact source, generated mask bytes, tools, and primary-source hashes."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[2]
tools = Path('/home/charles/code/friends/.toolchains')
spec = importlib.util.spec_from_file_location('front',root/'lifter/armv6m.py')
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)
elfpath = tools/'e04-freertos-build/verified02-a/out/FreeRTOS-Cortex-M0.elf'
elf = f.ELF(elfpath)
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
files = ['Picinae_armv6m.v','lifter/armv6m.py','dune',
         'tests/armv6m_primask/Checks.v','tests/armv6m_primask/fixture.v',
         'tests/armv6m_primask/snippets.s',
         'Examples/FreeRTOSMask/ulSetInterruptMask_armv6m.v',
         'Examples/FreeRTOSMask/vClearInterruptMask_armv6m.v']
result = dict(unit='e19-armv6m-primask',profile='primask-v1-base',
  prerequisite='95da7ab7cee78f09a528aed86c1dfaf29520a9a8',
  base='49956416928e5b6bb3928b54ae33e3b81091f006',
  timing_source='4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6',
  kernel='dbf70559b27d39c1fdb68dfb9a32140b6a6777a0',
  elf_path=str(elfpath),elf_sha256=sha(elfpath),
  sources_sha256={p:sha(root/p) for p in files},
  manuals=[dict(document='ARM DDI 0419E ID070218',
     url='https://documentation-service.arm.com/static/5f8ff05ef86e16515cdbf826',
     sha256=sha(tools/'e19-armv6m-primask/DDI0419E.pdf'),
     sections=['B1.3.1','B1.4.3-6','B1.5.8','B4.1.1','B4.2.1-3']),
    dict(document='ARM DDI 0432C ID113009',
     url='https://documentation-service.arm.com/static/5e8e294afd977155116a6a5b',
     sha256=sha(tools/'e19-armv6m-primask/DDI0432C.pdf'),sections=['3.2'])],
  functions=[])
for name in ('ulSetInterruptMask','vClearInterruptMask'):
    sym = [s for s in elf.symbols if s[0]==name and s[3]==2]
    assert len(sym)==1
    _,value,size,_,index = sym[0]
    entry = value&~1
    result['functions'].append(dict(symbol=name,thumb_symbol=hex(value),entry=hex(entry),
      size=size,bytes=elf.read(entry,size).hex(),
      finite_entries=([hex(entry),hex(entry+4),hex(entry+6)] if name=='ulSetInterruptMask'
                     else [hex(entry),hex(entry+4)]),
      source_sha256=sha(root/'Examples/FreeRTOSMask'/f'{name}_armv6m.v'),
      correctness_proof='not part of engineering e19; r42 pending'))
text=json.dumps(result,sort_keys=True,indent=2)+'\n'
path=root/'notes/e19-armv6m-primask/provenance.json'
if '--check' in sys.argv: assert path.read_text()==text
else: path.write_text(text)
print('PASS exact source and input provenance snapshot')
