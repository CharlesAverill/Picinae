#@runtime PyGhidra
import json,pathlib,sys,hashlib
repo,out,kind=getScriptArgs();repo=pathlib.Path(repo)
sys.path.insert(0,str(repo/'Examples/claude/inventory/e01-x86-inventory'))
from inventory import ELF,symbols
binary=pathlib.Path(str(currentProgram.getExecutablePath()))
assert str(currentProgram.getExecutableSHA256()).lower()==hashlib.sha256(binary.read_bytes()).hexdigest()
currentProgram.setImageBase(toAddr(0x100000),True)
if kind=='actual':
    sites=[int(r['address'],16) for r in json.loads((repo/'notes/e34-x86-copy-shuffles/actual-selection.json').read_text())]
else:
    sites=[]
    for s in symbols(binary,'fixture'):
        if s['type']=='FUNC' and s['size']:
            a=s['address']+0x100000
            while a<s['address']+0x100000+s['size']:
                disassemble(toAddr(a));ins=getInstructionAt(toAddr(a));sites.append(a);a+=int(ins.getLength())
def vn(v):
    if v is None:return None
    r=dict(space=str(v.getAddress().getAddressSpace().getName()),offset=int(v.getOffset()),size=int(v.getSize()))
    if v.isRegister():
        reg=currentProgram.getLanguage().getRegister(v.getAddress(),v.getSize())
        if reg is not None:
            base=reg.getBaseRegister();r.update(register=str(reg.getName()),base=str(base.getName()),base_offset=int(base.getAddress().getOffset()),base_width=int(base.getBitLength()))
    return r
rows=[]
for a in sorted(set(sites)):
    disassemble(toAddr(a));i=getInstructionAt(toAddr(a))
    rows.append(dict(address=hex(a),bytes=bytes(int(b)&255 for b in i.getBytes()).hex(),assembly=str(i),pcode=[str(o) for o in i.getPcode()],ops=[dict(code=str(o.getMnemonic()),output=vn(o.getOutput()),inputs=[vn(v) for v in o.getInputs()]) for o in i.getPcode()]))
pathlib.Path(out).write_text(json.dumps(rows,indent=2)+'\n')
