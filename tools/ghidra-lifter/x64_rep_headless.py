#@runtime PyGhidra
#@category Picinae
"""Exact REP instruction fragments; deliberately no closed glibc function claim."""
import hashlib
import json
import pathlib
import re
import sys
repo,stage,inventory,token,kind,profile,*selection = list(getScriptArgs())
repo,stage,inventory = map(pathlib.Path,(repo,stage,inventory))
sys.path.insert(0,str(repo/'tools/ghidra-lifter'))
sys.path.insert(0,str(repo/'Examples/claude/inventory/e01-x86-inventory'))
from pcode2coq_x64_rep import X64RepLifter, Unsupported
from inventory import ELF, symbols
from ghidra.framework import Application
sha = lambda data: hashlib.sha256(data).hexdigest()
BASE=0x100000
if str(Application.getApplicationVersion())!='11.4.2' or str(currentProgram.getLanguageID())!='x86:LE:64:default':
    raise ValueError('requires pinned Ghidra 11.4.2 x86:LE:64:default')
if kind=='glibc':
    binary=inventory/'runtime/lib/x86_64-linux-gnu/libc.so.6'
    pins=json.loads((repo/'Examples/claude/inventory/e01-x86-inventory/generated/target-manifest.json').read_text())
    expected=pins[str(binary.relative_to(inventory))]
    # Select only actual REP MOVS/STOS sites from the reviewed e01 disassembly.
    # The bytes are independently checked against ELF and Ghidra below.
    lines=(repo/'Examples/claude/inventory/e01-x86-inventory/generated/disassembly.txt').read_text().splitlines()
    requests=[]
    for line in lines:
        match=re.fullmatch(r'([0-9a-f]+)\s+([0-9a-f]+)\s+rep (?:movs|stos) .*',line)
        if match: requests.append((int(match[1],16)+BASE,bytes.fromhex(match[2]),'pinned_rep_site'))
    if selection!=['pinned_rep_sites'] or len(requests)!=26:
        raise ValueError('unexpected pinned REP inventory selection')
else:
    binary=repo/'notes/e27-x86-rep-lowering/fixture/rep.so'
    expected=json.loads((binary.parent/'pins.json').read_text())['sha256']
    syms=symbols(binary,'synthetic')
    names=['rep_movs'+w for w in 'bwdq']+['rep_stos'+w for w in 'bwdq'] if selection==['rep_fixture'] else selection
    requests=[]
    for name in names:
        matches={(s['address'],s['size']) for s in syms if s['name']==name and s['type']=='FUNC' and s['size']}
        if len(matches)!=1: raise ValueError('expected unique synthetic FUNC '+name)
        address,size=matches.pop()
        requests.append((address+BASE,None,name))
if sha(binary.read_bytes())!=expected or str(currentProgram.getExecutableSHA256()).lower()!=expected:
    raise ValueError('wrong ELF SHA256')
currentProgram.setImageBase(toAddr(BASE),True)
elf=ELF(binary)
lifter=X64RepLifter(currentProgram.getLanguage(),cet_disabled=profile=='cet-disabled')
def vn_json(v):
    if v is None:return None
    d=dict(space=str(v.getAddress().getAddressSpace().getName()),offset=int(v.getOffset()),size=int(v.getSize()))
    if v.isRegister():
        r=currentProgram.getLanguage().getRegister(v.getAddress(),v.getSize());b=r.getBaseRegister()
        d.update(register=str(r.getName()),base=str(b.getName()),base_offset=int(b.getAddress().getOffset()),base_width=int(b.getBitLength()))
    return d
rows,parts=[],[]
for address,wanted,label in sorted(requests):
    disassemble(toAddr(address));insn=getInstructionAt(toAddr(address))
    if insn is None:raise ValueError('invalid instruction')
    raw=bytes(int(b)&255 for b in insn.getBytes())
    if raw!=elf.read(address-BASE,len(raw)) or (wanted is not None and raw!=wanted):
        raise ValueError('instruction byte mismatch')
    stmt=lifter.instruction(insn)  # no partial output before every row succeeds
    rows.append(dict(address=hex(address),bytes=raw.hex(),assembly=str(insn),label=label,
        pcode=[str(o) for o in insn.getPcode()],
        ops=[dict(code=str(o.getMnemonic()),output=vn_json(o.getOutput()),inputs=[vn_json(v) for v in o.getInputs()]) for o in insn.getPcode()]))
    parts.append(f'(* {address:#x}: {insn} *)\n| {address:#x} => Some ({len(raw)},\n\t{stmt}\n)\n')
coqname='e27_rep_amd64'
text=f'''(* Exact REP MOVS/STOS instruction fragments, Ghidra 11.4.2 raw SLEIGH pcode.
Source: {kind}; ELF SHA256: {expected}; image base: 0x100000.
Selection: {', '.join(selection)}; profile: {profile}.
All addresses global. Deliberately open program: fallthroughs are NOT selected.
Successful sequential completion only; no fault/restart/interrupt/atomicity model.
Rep snapshots entry RCX; original ordered iteration body repeats RCX times,
including zero. 64-bit modular addresses, DF +/- element width, sequential
load-before-store alias behavior; flags untouched. No comparison REP forms.
Typing only: no functional correctness or lifter soundness theorem. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition {coqname} : program := fun _ a => match a with
{''.join(parts)}| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx {coqname}.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.
'''
output=stage/(coqname+'.v');output.write_text(text)
trace=stage/(coqname+'.pcode.json');trace.write_text(json.dumps(rows,indent=2)+'\n')
receipt=dict(token=token,selection=selection,source_kind=kind,elf_sha256=expected,
    semantics='rep-successful-sequential-fragments-v1',language=str(currentProgram.getLanguageID()),
    addressing='global',image_base=hex(BASE),profile=profile,
    frontier=[hex(int(r['address'],16)+len(bytes.fromhex(r['bytes']))) for r in rows],
    records=[dict(symbol='rep',instructions=len(rows),output=output.name,output_sha256=sha(output.read_bytes()),pcode_sha256=sha(trace.read_bytes()))])
(stage/'SUCCESS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(f'E27 SUCCESS {len(rows)} exact REP fragments, open fallthrough frontier')
