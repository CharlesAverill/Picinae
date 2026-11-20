#@runtime PyGhidra
"""Gather every instruction, including later unsupported frontiers, without IL."""
import json
from pathlib import Path
import sys

repo, unit_dir = map(Path, getScriptArgs())
sys.path.insert(0, str(repo / 'Examples/claude/inventory/e02-arm-inventory'))
from inventory import ELF, EXPECTED, BUILD_ID, sha
from ghidra.framework import Application
assert str(Application.getApplicationVersion()) == '11.4.2'
assert str(currentProgram.getExecutableSHA256()).lower() == EXPECTED
currentProgram.setImageBase(toAddr(0x100000), True)
deps = Path('/home/charles/code/friends/.toolchains/e02-arm-inventory')
elf = ELF(deps / 'root/lib/aarch64-linux-gnu/libc.so.6')
dbg = ELF(deps / f'root/usr/lib/debug/.build-id/{BUILD_ID[:2]}/{BUILD_ID[2:]}.debug')
assert sha(elf.data) == EXPECTED

def vn(v):
    if v is None:
        return None
    kind = 'unique' if v.isUnique() else 'register' if v.isRegister() else 'constant' if v.isConstant() else str(v.getAddress().getAddressSpace().getName())
    r = dict(kind=kind, offset=int(v.getOffset()), size=int(v.getSize()))
    if v.isRegister():
        reg = currentProgram.getLanguage().getRegister(v.getAddress(), v.getSize())
        if reg is None:
            return r
        b = reg.getBaseRegister()
        r['base'] = dict(name=str(b.getName()), offset=int(b.getAddress().getOffset()), width=int(b.getBitLength()))
    return r

def row(i):
    return dict(address=hex(int(i.getAddress().getOffset())), bytes=bytes(int(b) & 255 for b in i.getBytes()).hex(),
                assembly=str(i), mnemonic=str(i.getMnemonicString()).lower(),
                pcode=[str(op) for op in i.getPcode()],
                ops=[dict(code=str(op.getMnemonic()), out=vn(op.getOutput()), args=[vn(v) for v in op.getInputs()]) for op in i.getPcode()])

targets = {}
for name in ('inet_makeaddr', 'rand_r', '__memchr_nosimd', 'strcmp', '__strlen_asimd'):
    matches = {(s['address'], s['size']) for s in dbg.symbols() if s['name'] == name and s['type'] == 'FUNC'}
    assert len(matches) == 1
    address, size = matches.pop()
    rows = []
    for a in range(address + 0x100000, address + 0x100000 + size, 4):
        disassemble(toAddr(a))
        i = getInstructionAt(toAddr(a))
        assert i is not None
        r = row(i)
        assert r['bytes'] == elf.at(a - 0x100000, 4).hex()
        rows.append(r)
    targets[name] = rows

# Explicit architectural encodings, independent of any assembler installation.
# Paired width/register/immediate cases supplement actual binary instructions.
words = []
for sf in (0, 1):
    w = 32 << sf
    words.extend([((0xdac00c00 if sf else 0x5ac00800) | (1 << 5), 'rev'),
                  ((sf << 31) | 0x2a200000 | (2 << 16) | (1 << 5), 'orn'),
                  ((sf << 31) | 0x6a200000 | (2 << 16) | (1 << 5), 'bics')])
    for lsb, width in ((1, 1), (10, 11), (w - 2, 1), (1, w - 2)):
        words.append(((sf << 31) | 0x53000000 | (sf << 22) | ((w - lsb) << 16) | ((width - 1) << 10) | (1 << 5), 'ubfiz'))
base = toAddr(0x400000)
block = currentProgram.getMemory().createInitializedBlock('e29-fixtures', base, len(words) * 4, 0, monitor, False)
block.setExecute(True)
fixtures = []
from jpype import JArray, JByte
currentProgram.getMemory().setBytes(base, JArray(JByte)(b''.join(w.to_bytes(4, 'little') for w, _ in words)))
for index, (word, name) in enumerate(words):
    a = base.add(index * 4)
    raw = word.to_bytes(4, 'little')
    disassemble(a)
    i = getInstructionAt(a)
    assert str(i.getMnemonicString()).lower() == name, str(i)
    fixtures.append(row(i))
(unit_dir / 'raw.json').write_text(json.dumps(dict(elf_sha256=EXPECTED, ghidra='11.4.2', targets=targets, fixtures=fixtures), indent=2) + '\n')
