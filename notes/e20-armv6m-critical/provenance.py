#!/usr/bin/env python3
"""Pin actual ELF bytes, code/data mapping, branch/call edges, manuals and tools."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
root=Path(__file__).resolve().parents[2]
tool=Path('/home/charles/code/friends/.toolchains/e04-freertos-build')
bin=tool/'arm-gnu-toolchain-13.2.Rel1-x86_64-arm-none-eabi/bin'
spec=importlib.util.spec_from_file_location('front',root/'lifter/armv6m.py')
f=importlib.util.module_from_spec(spec); spec.loader.exec_module(f)
elfpath=tool/'verified02-a/out/FreeRTOS-Cortex-M0.elf'
elf=f.ELF(elfpath)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(elfpath)=='5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca'
assert [(s[1],s[2]) for s in elf.symbols if s[0]=='ulCriticalNesting']==[(0x20000000,4)]
dump=subprocess.check_output([str(bin/'arm-none-eabi-objdump'),'-d','--start-address=0x3e68','--stop-address=0x3eb0',str(elfpath)],text=True)
result=dict(unit='e20-armv6m-critical',status='PARTIAL: sequential projection only; hardware barriers and exit assertion closure unavailable',
    profile='critical-seq-v1-base',base='49956416928e5b6bb3928b54ae33e3b81091f006',
    prerequisite='0bc7fec4dbbfddbe8c5c130b9bd15d1b7af10ba6',
    timing_source='4f1772040b6fc9d12af3f84f2ca089bb65cd4bd6',
    freertos_source='dbf70559b27d39c1fdb68dfb9a32140b6a6777a0',
    elf_path=str(elfpath),elf_sha256=sha(elfpath),ulCriticalNesting='0x20000000',
    compiler=subprocess.check_output([str(bin/'arm-none-eabi-gcc'),'--version'],text=True).splitlines()[0],
    tools_sha256={name:sha(bin/name) for name in ('arm-none-eabi-as','arm-none-eabi-ld','arm-none-eabi-objdump')},
    sources_sha256={str(p.relative_to(root)):sha(p) for p in [root/'Picinae_armv6m.v',root/'Picinae_armv6m_sync.v',root/'lifter/armv6m.py',root/'dune',
      *sorted((root/'Examples/FreeRTOSCritical').glob('*.v')),*sorted((root/'tests/armv6m_critical').glob('*.v')),root/'tests/armv6m_critical/snippets.s',
      *sorted((root/'notes/e20-armv6m-critical').glob('*.py')),root/'notes/e20-armv6m-critical/validate.sh']},
    manuals=[dict(document='Arm DDI 0419E ID070218',url='https://documentation-service.arm.com/static/5f8ff05ef86e16515cdbf826',
      sha256=sha(Path('/home/charles/code/friends/.toolchains/e19-armv6m-primask/DDI0419E.pdf')),
      sections=['A3.7.3','A6.7.21','A6.7.22','A6.7.24','B1.4.6','B2.5','B4.2.1']),
      dict(document='Arm DDI 0432C ID113009',url='https://documentation-service.arm.com/static/5e8e294afd977155116a6a5b',
      sha256=sha(Path('/home/charles/code/friends/.toolchains/e19-armv6m-primask/DDI0432C.pdf')),sections=['3.2'])],functions=[])
for name in ('vPortEnterCritical','vPortExitCritical'):
    sym=[s for s in elf.symbols if s[0]==name and s[3]==2]; assert len(sym)==1
    _,value,size,_,idx=sym[0]; entry=value&~1
    rows=[]; calls=[]; barriers=[]; literals=[]
    for line in dump.splitlines():
        m=re.match(r'^\s*([0-9a-f]+):\s+([0-9a-f]{4}(?:\s+[0-9a-f]{4})?)\s+([^\s].*)$',line)
        if not m: continue
        a=int(m[1],16)
        if not entry<=a<entry+size or elf.mode(idx,a)!='t': continue
        halves=[int(h,16) for h in m[2].split()]; width=2*len(halves)
        assert elf.read(a,width)==b''.join(h.to_bytes(2,'little') for h in halves)
        text=m[3]; rows.append(dict(address=hex(a),halfwords=[hex(x) for x in halves],disassembly=text))
        if text.startswith('bl\t'):
            target=int(text.split()[1],16)
            calls.append(dict(site=hex(a),target=hex(target),symbol=[s[0] for s in elf.symbols if s[3]==2 and s[1]&~1==target]))
        if halves[0]==0xf3bf: barriers.append(dict(site=hex(a),kind=text))
        if halves[0]&0xf800==0x4800:
            loc=((a+4)&~3)+(halves[0]&255)*4
            literals.append(dict(site=hex(a),pool=hex(loc),value=hex(int.from_bytes(elf.read(loc,4,True),'little'))))
    assert len(rows)==(8 if name=='vPortEnterCritical' else 17)
    assert [int(x['target'],16) for x in calls]==([] if name=='vPortEnterCritical' else [0x419c])
    result['functions'].append(dict(symbol=name,entry=hex(entry),thumb_symbol=hex(value),size=size,
      bytes=elf.read(entry,size).hex(),instructions=rows,literals=literals,barriers=barriers,calls=calls,
      call_closure='closed body, sequential projection only' if not calls else 'BLOCKED: fixture_assert_fail at 0x419c rejects WFI (e23); no nonreturn contract'))
path=root/'notes/e20-armv6m-critical/provenance.json'
text=json.dumps(result,sort_keys=True,indent=2)+'\n'
if '--check' in sys.argv: assert path.read_text()==text
else:
    path.write_text(text)
    (root/'notes/e20-armv6m-critical/logs/critical.objdump').write_text(dump)
print('PASS exact ELF, global, code/data, call closure, barrier, tool and manual provenance')
