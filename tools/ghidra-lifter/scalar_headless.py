#@runtime PyGhidra
#@category Picinae
"""Fresh-import, exact ELF symbol-extent scalar lifting; called by lift-scalar.py."""
import hashlib
import json
import pathlib
import sys

repo, stage, deps, token, mode, *names = list(getScriptArgs())
repo, stage, deps = map(pathlib.Path, (repo, stage, deps))
sys.path.insert(0, str(repo/'tools/ghidra-lifter'))
sys.path.insert(0, str(repo/'Examples/claude/inventory/e02-arm-inventory'))
from pcode2coq_scalar import ScalarLifter, Unsupported
from inventory import ELF, EXPECTED, BUILD_ID, sha
from ghidra.framework import Application
if str(Application.getApplicationVersion()) != '11.4.2':
    raise ValueError('requires Ghidra 11.4.2')

if str(currentProgram.getExecutableSHA256()).lower() != EXPECTED:
    raise ValueError('wrong runtime SHA256')
currentProgram.setImageBase(toAddr(0x100000), True)
binary = deps/'root/lib/aarch64-linux-gnu/libc.so.6'
debug = deps/f'root/usr/lib/debug/.build-id/{BUILD_ID[:2]}/{BUILD_ID[2:]}.debug'
elf, dbg = ELF(binary), ELF(debug)
manifest = json.loads((repo/'Examples/claude/inventory/e02-arm-inventory/evidence/inventory.json').read_text())
if sha(dbg.data) != manifest['debug_sha256']:
    raise ValueError('wrong debug SHA256')
symbols = dbg.symbols()
records = []
all_addresses = set()
for name in names:
    matches = {(s['address'], s['size']) for s in symbols if s['name'] == name and s['type'] == 'FUNC' and s['size']}
    if len(matches) != 1:
        raise ValueError(f'{name}: expected one nonempty FUNC extent, found {matches}')
    address, size = matches.pop()
    if size % 4:
        raise ValueError(f'{name}: non-A64 extent')
    entry = address + 0x100000
    all_addresses.update(range(entry, entry + size, 4))
    records.append(dict(symbol=name, elf_entry=hex(address), entry=hex(entry), size=size,
                        bytes_sha256=sha(elf.at(address, size))))
bodies = {}
traces = {}
for record in records:
    name = record['symbol']
    entry = int(record['entry'], 16)
    base = 0 if mode == 'global' else entry
    lifter = ScalarLifter(currentProgram.getLanguage(), base)
    rows, body = [], []
    for address in range(entry, entry + record['size'], 4):
        disassemble(toAddr(address))
        insn = getInstructionAt(toAddr(address))
        if insn is None:
            raise ValueError(f'{name}: missing instruction {address:#x}')
        # Reject dangling direct machine edges, including cross-symbol branches.
        # Global mode accepts only explicitly selected closed symbol extents.
        for op in insn.getPcode():
            if str(op.getMnemonic()) in ('BRANCH', 'CBRANCH', 'CALL'):
                dest = op.getInput(0)
                if dest.isAddress():
                    target = int(dest.getOffset())
                    allowed = all_addresses if not base else set(range(entry, entry + record['size'], 4))
                    if target not in allowed:
                        raise Unsupported(f'{name}: direct edge outside selected extent(s): {target:#x}')
        try:
            stmt = lifter.instruction(insn)
        except Exception as e:
            raise Unsupported(f'{name} {address:#x} {insn}: {e}; raw pcode: ' + '; '.join(str(op) for op in insn.getPcode())) from e
        raw = bytes((int(b) & 255) for b in insn.getBytes())
        if raw != elf.at(address - 0x100000, 4):
            raise ValueError('Ghidra bytes differ from ELF')
        rows.append(dict(address=hex(address), bytes=raw.hex(), assembly=str(insn),
                         pcode=[str(op) for op in insn.getPcode()]))
        body.append(f'(* {address:#x}: {insn} *)\n| {address - base:#x} => Some (4,\n\t{stmt}\n)\n')
    bodies[name] = body
    traces[name] = rows
for record in records:
    name, entry = record['symbol'], int(record['entry'], 16)
    # Every global program contains the union of the selected extents. Remove
    # aliases by address, retaining a deterministic ascending code order.
    if mode == 'global':
        byaddr = {}
        for selected in records:
            for row, fragment in zip(traces[selected['symbol']], bodies[selected['symbol']]):
                byaddr[int(row['address'], 16)] = (row, fragment)
        rows, body = zip(*(byaddr[a] for a in sorted(byaddr)))
    else:
        rows, body = traces[name], bodies[name]
    coqname = f'e11_{name}_arm8'
    text = f'''(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: {EXPECTED}
function: {name}; entry: {entry:#x}; addressing: {mode}
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition {coqname} : program := fun _ a => match a with
{''.join(body)}| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx {coqname}.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
'''
    output = stage/f'{coqname}.v'
    output.write_text(text)
    (stage/f'{coqname}.pcode.json').write_text(json.dumps(rows, indent=2)+'\n')
    record.update(output=output.name, output_sha256=sha(output.read_bytes()), instructions=len(rows),
                  selected_symbols=names if mode == 'global' else [name])
# This receipt is only written after every requested function succeeded.
receipt = dict(token=token, libc_sha256=EXPECTED, debug_sha256=sha(dbg.data),
               language=str(currentProgram.getLanguageID()), addressing=mode, records=records)
(stage/'SUCCESS.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(f'E11 SUCCESS {len(records)} complete scalar artifacts')
