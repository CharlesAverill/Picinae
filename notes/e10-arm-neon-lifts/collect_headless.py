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

# GNU assembler output, generated in this unit's isolated state. Ghidra
# independently decodes both widths, all fourteen legal alias conditions,
# source/destination aliasing and register endpoints. AL/NV/ZR are excluded.
words = (unit_dir / 'assembled.bin').read_bytes()
base = toAddr(0x400000)
block = currentProgram.getMemory().createInitializedBlock('e10-fixtures', base, len(words), 0, monitor, False)
block.setExecute(True)
from jpype import JArray, JByte
currentProgram.getMemory().setBytes(base, JArray(JByte)(words))
fixtures = []
for index in range(len(words)//4):
    a = base.add(index * 4)
    disassemble(a)
    i = getInstructionAt(a)
    fixtures.append(row(i))
vector_bases = []
for k in range(32):
    r = currentProgram.getLanguage().getRegister('z'+str(k))
    vector_bases.append(dict(name=str(r.getName()), offset=int(r.getAddress().getOffset()), width=int(r.getBitLength())))
(unit_dir / 'raw.json').write_text(json.dumps(dict(elf_sha256=EXPECTED, ghidra='11.4.2', targets=targets, fixtures=fixtures, vector_bases=vector_bases), indent=2) + '\n')
# Diagnostic open fragments, never a function program or partial extraction.
sys.path.insert(0, str(repo/'tools/ghidra-lifter'))
from pcode2coq_neon_loads import NeonLoadLifter
from pcode2coq_scalar import Unsupported
fragments={}
audits={}
for name,rows in {**targets, 'assembled':fixtures}.items():
    accepted=[]; rejected=[]
    for r in rows:
        try:
            il=NeonLoadLifter(currentProgram.getLanguage()).instruction(getInstructionAt(toAddr(int(r['address'],16))))
        except Unsupported as e:
            rejected.append(dict(address=r['address'],bytes=r['bytes'],assembly=r['assembly'],reason=str(e)))
        else:
            accepted.append(r['address'])
            if r['mnemonic'] in ('ldr','ldp') and 'q' in r['assembly']:
                fragments[r['bytes']]=il
    audits[name]=dict(accepted_addresses=accepted,rejected=rejected)
(unit_dir/'OPEN-FRAGMENTS.json').write_text(json.dumps(fragments,indent=2)+'\n')
(unit_dir/'FRONTIERS.json').write_text(json.dumps(audits,indent=2)+'\n')
