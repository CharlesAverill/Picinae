"""Read-only check of the pinned ELF/data and the unchanged witness literal."""
import hashlib, json, re, struct
from pathlib import Path
elf_path = Path('/home/charles/code/friends/.toolchains/e02-arm-inventory/root/lib/aarch64-linux-gnu/libc.so.6')
elf = elf_path.read_bytes()
sha = hashlib.sha256(elf).hexdigest()
assert sha == '79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06'
assert elf[:6] == b'\x7fELF\x02\x01'
phoff = struct.unpack_from('<Q', elf, 32)[0]
phsize, phnum = struct.unpack_from('<HH', elf, 54)
addr, size = 0x14e738, 256
for index in range(phnum):
    typ, flags, off, va, _, filesz, memsz, align = struct.unpack_from('<IIQQQQQQ', elf, phoff + index*phsize)
    if typ == 1 and va <= addr and addr+size <= va+filesz:
        data = elf[off+addr-va:off+addr-va+size]
        print(f'PT_LOAD flags={flags:#x}, ELF={addr:#x}, file offset={off+addr-va:#x}, size={size}')
        assert flags & 4
        break
else:
    raise AssertionError('table is not file-backed PT_LOAD data')
obj = json.loads(Path('notes/e08-arm-lifts/ffs-reference-data.json').read_text())['materialized_objects'][0]
assert data.hex() == obj['elf_bytes_hex']
assert hashlib.sha256(data).hexdigest() == obj['elf_bytes_sha256']
assert int(obj['model_address'], 0) == addr + 0x100000 == 0x24e738
source = Path('Examples/claude/arm8_ffs_proof.v').read_text()
literal = re.search(r'Definition ffs_table_bytes : N := (0x[0-9a-f]+)\.', source).group(1)
assert int(literal, 16).to_bytes(256, 'little') == data
assert all(byte == i.bit_length() for i, byte in enumerate(data))
pcode = json.loads(Path('Examples/claude/lifter/scalar_smoke/e11_ffs_arm8.pcode.json').read_text())
print('ELF SHA256:', sha)
print('Table SHA256:', hashlib.sha256(data).hexdigest())
print('All 256 bytes match ELF, reference-data JSON, proof literal and index bit length.')
print('Model address = ELF address + 0x100000. Table is independent of input X0.')
print('Runtime memory must supply these bytes; staticMemory=False does not initialize them.')
print('This executable provenance check does not certify the lifter or prove total correctness.')
