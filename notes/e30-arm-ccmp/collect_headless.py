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
for name in ('__memchr_nosimd', 'strcmp', '__strlen_asimd', 'wcschrnul', 'memcmp', 'sigandset', 'sigorset', 'sigaddset', 'sigdelset', 'sigismember'):
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
    for immediate in (0, 1):
        for cond in range(16):
            # All conditions and fallback bits; both widths and forms.
            for operand in ((0, 1, 31) if immediate else (2, 30, 31)):
                rn = 31 if operand == 31 else 1
                nzcv = cond
                words.append(((sf << 31) | 0x7a400000 | (immediate << 11) |
                              (operand << 16) | (cond << 12) | (rn << 5) | nzcv, 'ccmp'))
# Exercise every fallback under EQ, independently of the condition encoding,
# every imm5 value, and separate zero-register positions / source aliasing.
for sf in (0, 1):
    for immediate in (0, 1):
        for nzcv in range(16):
            words.append(((sf << 31) | 0x7a400000 | (immediate << 11) | (2 << 16) | (1 << 5) | nzcv, 'ccmp'))
    for imm in range(32):
        words.append(((sf << 31) | 0x7a400800 | (imm << 16) | (1 << 12) | (1 << 5) | 15, 'ccmp'))
    for rn, rm in ((31, 2), (1, 31), (1, 1)):
        words.append(((sf << 31) | 0x7a400000 | (rm << 16) | (rn << 5), 'ccmp'))
base = toAddr(0x400000)
block = currentProgram.getMemory().createInitializedBlock('e30-fixtures', base, len(words) * 4, 0, monitor, False)
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
