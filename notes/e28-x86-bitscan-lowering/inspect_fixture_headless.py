#@runtime PyGhidra
import pathlib,json,hashlib,re,sys
repo,out=map(pathlib.Path,getScriptArgs())
sys.path.insert(0,str(repo/'Examples/claude/inventory/e01-x86-inventory'))
from inventory import ELF,symbols
inv=pathlib.Path('/home/charles/code/friends/.toolchains/e01-x86-inventory')
binary=repo/'notes/e28-x86-bitscan-lowering/fixture/bitscan.so'

elf=ELF(binary)
currentProgram.setImageBase(toAddr(0x100000),True)
def vn(v):
    if v is None:return None
    d=dict(space=str(v.getAddress().getAddressSpace().getName()),offset=int(v.getOffset()),size=int(v.getSize()))
    if v.isRegister():
        r=currentProgram.getLanguage().getRegister(v.getAddress(),v.getSize()); b=r.getBaseRegister()
        d.update(register=str(r.getName()),base=str(b.getName()),base_offset=int(b.getAddress().getOffset()),base_width=int(b.getBitLength()))
    return d
def row(a):
    disassemble(toAddr(a+0x100000));i=getInstructionAt(toAddr(a+0x100000))
    raw=bytes(int(b)&255 for b in i.getBytes());assert raw==elf.read(a,len(raw))
    return dict(address=hex(a+0x100000),bytes=raw.hex(),assembly=str(i),pcode=[str(o) for o in i.getPcode()],ops=[dict(code=str(o.getMnemonic()),output=vn(o.getOutput()),inputs=[vn(v) for v in o.getInputs()]) for o in i.getPcode()])
rows=[]
for sym in symbols(binary,'synthetic'):
    if sym['type']=='FUNC' and sym['size']:
        a=sym['address'];end=a+sym['size']
        while a<end:
            r=row(a);r['function']=sym['name'];rows.append(r);a+=len(bytes.fromhex(r['bytes']))
out.write_text(json.dumps(rows,indent=2)+'\n')
