#@runtime PyGhidra
#@category Picinae
"""Exact pinned AMD64 ELF/debug extraction, called only by lift-x64.py."""
import hashlib
import json
import pathlib
import sys

repo, stage, inventory, token, kind, profile, *names = list(getScriptArgs())
repo, stage, inventory = map(pathlib.Path, (repo,stage,inventory))
sys.path.insert(0,str(repo/'tools/ghidra-lifter'))
sys.path.insert(0,str(repo/'Examples/claude/inventory/e01-x86-inventory'))
from pcode2coq_x64 import X64Lifter, Unsupported
from inventory import ELF, symbols
from ghidra.framework import Application
sha = lambda data: hashlib.sha256(data).hexdigest()
BASE = 0x100000
if str(Application.getApplicationVersion()) != '11.4.2':
    raise ValueError('requires Ghidra 11.4.2')
if str(currentProgram.getLanguageID()) != 'x86:LE:64:default':
    raise ValueError('requires x86:LE:64:default')
if kind == 'glibc':
    binary = inventory/'runtime/lib/x86_64-linux-gnu/libc.so.6'
    debug = inventory/'debug/usr/lib/debug/.build-id/08/5164b7e9093b36e3be17226f0d94a35b818c55.debug'
    pins = json.loads((repo/'Examples/claude/inventory/e01-x86-inventory/generated/target-manifest.json').read_text())
    expected = pins[str(binary.relative_to(inventory))]
    if sha(debug.read_bytes()) != pins[str(debug.relative_to(inventory))]:
        raise ValueError('wrong debug SHA256')
else:
    binary = repo/'notes/e25-x86-scalar-driver/fixture/scalar.so'
    debug = binary
    expected = json.loads((binary.parent/'pins.json').read_text())['sha256']
if sha(binary.read_bytes()) != expected or str(currentProgram.getExecutableSHA256()).lower() != expected:
    raise ValueError('wrong ELF SHA256')
currentProgram.setImageBase(toAddr(BASE),True)
elf = ELF(binary)
syms = symbols(debug,'exact-debug')
def vn_json(v):
    if v is None:
        return None
    result = dict(space=str(v.getAddress().getAddressSpace().getName()),offset=int(v.getOffset()),size=int(v.getSize()))
    if v.isRegister():
        reg = currentProgram.getLanguage().getRegister(v.getAddress(),v.getSize())
        if reg is not None:
            base = reg.getBaseRegister()
            result.update(register=str(reg.getName()),base=str(base.getName()),
                          base_offset=int(base.getAddress().getOffset()),base_width=int(base.getBitLength()))
    return result


def op_json(op):
    return dict(code=str(op.getMnemonic()),output=vn_json(op.getOutput()),inputs=[vn_json(v) for v in op.getInputs()])

records, traces, fragments = [],{},{}
for name in names:
    matches = {(s['address'],s['size']) for s in syms if s['name']==name and s['type']=='FUNC' and s['size']}
    if len(matches)!=1:
        raise ValueError(f'{name}: expected one nonempty FUNC extent, got {matches}')
    addr,size = matches.pop()
    entry = addr+BASE
    records.append(dict(symbol=name,elf_entry=hex(addr),entry=hex(entry),size=size,
                        bytes_sha256=sha(elf.read(addr,size))))
    rows,parts = [],[]
    address = entry
    lifter = X64Lifter(currentProgram.getLanguage(),cet_disabled=profile=='cet-disabled')
    while address < entry+size:
        disassemble(toAddr(address))
        insn = getInstructionAt(toAddr(address))
        if insn is None or int(insn.getLength()) <= 0 or address+int(insn.getLength()) > entry+size:
            raise ValueError(f'{name}: invalid instruction extent at {address:#x}')
        raw = bytes(int(b)&255 for b in insn.getBytes())
        if raw != elf.read(address-BASE,len(raw)):
            raise ValueError('Ghidra bytes differ from ELF')
        try:
            stmt = lifter.instruction(insn)
        except Exception as e:
            raise Unsupported(f'{name} {address:#x} {insn}: {e}; raw pcode: '+ '; '.join(str(o) for o in insn.getPcode())) from e
        rows.append(dict(address=hex(address),bytes=raw.hex(),assembly=str(insn),
                         pcode=[str(o) for o in insn.getPcode()],ops=[op_json(o) for o in insn.getPcode()]))
        part = f'(* {address:#x}: {insn} *)\n| {address:#x} => Some ({len(raw)},\n\t{stmt}\n)\n'
        if address in fragments and fragments[address]!=part:
            raise ValueError('inconsistent overlapping instruction')
        fragments[address] = part
        parts.append(insn)
        address += len(raw)
    traces[name] = rows
    record = records[-1]
    record['instructions'] = len(rows)
    record['selected_symbols'] = names
    record['_insns'] = parts
# Reject overlapping extents even if different decodings happen to agree at entries.
intervals = sorted({(int(r['entry'],16),int(r['entry'],16)+r['size']) for r in records})
if any(b>c for (a,b),(c,d) in zip(intervals,intervals[1:])):
    raise Unsupported('overlapping nonidentical symbol extents')
addresses = set(fragments)
edges = []
for r in records:
    for insn in r.pop('_insns'):
        address = int(insn.getAddress().getOffset())
        for op in insn.getPcode():
            code = str(op.getMnemonic())
            if code in ('BRANCH','CBRANCH','CALL'):
                dest = op.getInput(0)
                if dest.isAddress():
                    target = int(dest.getOffset())
                    if target not in addresses:
                        raise Unsupported(f'direct {code} outside selected instruction boundaries: {target:#x}')
                    edges.append(dict(site=hex(address),target=hex(target),kind=code))
        # Ghidra's machine fallthrough, including the actual call return site.
        fall = insn.getFallThrough()
        if fall is not None and int(fall.getOffset()) not in addresses:
            raise Unsupported(f'fallthrough outside selected instruction boundaries: {fall}')
body = ''.join(fragments[a] for a in sorted(fragments))
for r in records:
    name = r['symbol']
    coqname = f'e25_{name}_amd64'
    text = f'''(* Strict AMD64 scalar profile, Ghidra 11.4.2 raw SLEIGH pcode.
Source kind: {kind}; ELF SHA256: {expected}
Symbol: {name}; global entry: {r['entry']}; selected: {', '.join(names)}
Profile: {profile} (CET-enabled execution is outside this model).
Global memory/return addresses; instruction-local temporaries; staticMemory=False.
Engineering typing only; no functional correctness or lifter soundness claim. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition {coqname} : program := fun _ a => match a with
{body}| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx {coqname}.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
'''
    output = stage/f'{coqname}.v'
    output.write_text(text)
    tracefile = stage/f'{coqname}.pcode.json'
    tracefile.write_text(json.dumps(traces[name],indent=2)+'\n')
    r.update(output=output.name,output_sha256=sha(output.read_bytes()),pcode_sha256=sha(tracefile.read_bytes()))
receipt = dict(token=token,source_kind=kind,elf_sha256=expected,debug_sha256=sha(debug.read_bytes()),
               image_base=hex(BASE),language=str(currentProgram.getLanguageID()),addressing='global',profile=profile,
               direct_edges=edges,records=records)
(stage/'SUCCESS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(f'E25 SUCCESS {len(records)} complete strict scalar artifacts')
