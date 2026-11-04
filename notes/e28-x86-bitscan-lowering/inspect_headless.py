#@runtime PyGhidra
import pathlib,json,hashlib,re,sys
repo,out=map(pathlib.Path,getScriptArgs())
sys.path.insert(0,str(repo/'Examples/claude/inventory/e01-x86-inventory'))
from inventory import ELF,symbols
inv=pathlib.Path('/home/charles/code/friends/.toolchains/e01-x86-inventory')
binary=inv/'runtime/lib/x86_64-linux-gnu/libc.so.6'
assert hashlib.sha256(binary.read_bytes()).hexdigest()=='9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9'
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
rows=[];seen=set();occurrences=[]
for line in (repo/'Examples/claude/inventory/e01-x86-inventory/generated/disassembly.txt').read_text().splitlines():
    if line.startswith('# '): context=line
    m=re.match(r'([0-9a-f]+)\s+([0-9a-f]+)\s+(bsf|bsr|tzcnt|lzcnt)\s',line)
    if m:
        a=int(m[1],16);r=row(a);assert r['bytes']==m[2]
        occurrences.append(dict(address=r['address'],bytes=m[2],symbol_context=context))
        if m[2] not in seen: rows.append(r);seen.add(m[2])
debug=inv/'debug/usr/lib/debug/.build-id/08/5164b7e9093b36e3be17226f0d94a35b818c55.debug'
for name in ['ffs','ffsl','ffsll']:
    syms={(s['address'],s['size']) for s in symbols(debug,'exact-debug') if s['name']==name and s['type']=='FUNC'}
    for a,size in syms:
        end=a+size
        while a<end:
            r=row(a);r['function']=name;rows.append(r);a+=len(bytes.fromhex(r['bytes']))
out.write_text(json.dumps(dict(rows=rows,occurrences=occurrences),indent=2)+'\n')
print('RAW EXTRACTION',len(rows),len(occurrences))
