import hashlib, json
from pathlib import Path
p=Path('Examples/claude/lifter/scalar_ccmp')
name='e30___memchr_nosimd_arm8'
m=json.loads((p/(name+'.manifest.json')).read_text())
r=json.loads((p/(name+'.pcode.json')).read_text())
b=b''.join(bytes.fromhex(x['bytes']) for x in r)
assert len(r)==56 and len(b)==224
assert [int(x['address'],16) for x in r]==list(range(0x19c7c0,0x19c8a0,4))
assert hashlib.sha256(b).hexdigest()==m['record']['bytes_sha256']
for suffix,key in [('.v','generated_program_sha256'),('.pcode.json','pcode_sha256')]:
    h=hashlib.sha256((p/(name+suffix)).read_bytes()).hexdigest()
    assert h==m[key]
    print(name+suffix,h)
print('56 instructions / 224 bytes:',hashlib.sha256(b).hexdigest())
for x in r:
    print(x['address'],x['bytes'],x['assembly'])
print('Memory sites:', m['data']['memory_accesses'])
print('Closed map:',m['closure']['closed'])
print('Limitations:',m['limits'])
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,'Examples/claude/inventory/e02-arm-inventory')
from inventory import ELF
elf_path=Path('/home/charles/code/friends/.toolchains/e02-arm-inventory/root/lib/aarch64-linux-gnu/libc.so.6')
elf=ELF(elf_path)
assert hashlib.sha256(elf.data).hexdigest()==m['elf_sha256']
for x in r:
    assert elf.at(int(x['address'],16)-0x100000,4).hex()==x['bytes']
print('Read-only ELF byte comparison: 56/56 match',elf_path)
print('ELF SHA256:',hashlib.sha256(elf.data).hexdigest())
