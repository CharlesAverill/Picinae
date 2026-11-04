#@runtime PyGhidra
import json,pathlib,sys
repo,out,kind=list(getScriptArgs())
repo,out=map(pathlib.Path,(repo,out))
sys.path.insert(0,str(repo/'Examples/claude/inventory/e01-x86-inventory'))
from inventory import symbols
currentProgram.setImageBase(toAddr(0x100000),True)
def vn(v):
    if v is None:return None
    d=dict(space=str(v.getAddress().getAddressSpace().getName()),offset=int(v.getOffset()),size=int(v.getSize()))
    if v.isRegister():
        r=currentProgram.getLanguage().getRegister(v.getAddress(),v.getSize());b=r.getBaseRegister()
        d.update(register=str(r.getName()),base=str(b.getName()),base_offset=int(b.getAddress().getOffset()),base_width=int(b.getBitLength()))
    return d
binary=repo/'notes/e27-x86-rep-lowering/fixture/rep.so'
rows=[]
for s in symbols(binary,'fixture'):
    if s['type']!='FUNC' or not s['name'].startswith('rep_'):continue
    addr=s['address']+0x100000
    disassemble(toAddr(addr));i=getInstructionAt(toAddr(addr))
    rows.append(dict(address=hex(addr),symbol=s['name'],bytes=bytes(int(b)&255 for b in i.getBytes()).hex(),assembly=str(i),
        ops=[dict(code=str(o.getMnemonic()),output=vn(o.getOutput()),inputs=[vn(v) for v in o.getInputs()]) for o in i.getPcode()]))
out.write_text(json.dumps(rows,indent=2)+'\n')
