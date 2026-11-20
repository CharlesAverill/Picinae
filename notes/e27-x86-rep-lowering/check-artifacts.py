#!/usr/bin/env python3
"""Validate byte provenance, complete selection, receipts and exact emitted text."""
import hashlib,json,sys
from pathlib import Path
repo=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(repo/'Examples/claude/inventory/e01-x86-inventory'))
sys.path.insert(0,str(repo/'tools/ghidra-lifter'))
from inventory import ELF
from test_x64 import Language,instruction
from pcode2coq_x64_rep import X64RepLifter
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=Path('/home/charles/code/friends/.toolchains/e01-x86-inventory')
manifest=json.loads((repo/'Examples/claude/inventory/e01-x86-inventory/generated/target-manifest.json').read_text())
for f,want in manifest.items():assert sha(inv/f)==want,f
fixture=repo/'notes/e27-x86-rep-lowering/fixture/rep.so'
assert sha(fixture)==json.loads((fixture.parent/'pins.json').read_text())['sha256']
for kind,binary,count in [('pinned',inv/'runtime/lib/x86_64-linux-gnu/libc.so.6',26),('synthetic',fixture,8)]:
    d=repo/'Examples/claude/lifter'/('x64_rep_'+kind)
    receipt=json.loads((d/'SUCCESS.json').read_text())
    assert receipt['elf_sha256']==sha(binary)
    assert receipt['semantics']=='rep-successful-sequential-fragments-v1'
    for name,want in receipt['implementation_sha256'].items():assert sha(repo/'tools/ghidra-lifter'/name)==want,name
    for name,want in receipt['isa_sha256'].items():assert sha(Path('/home/charles/code/friends/.toolchains/e02-arm-inventory')/name)==want,name
    r,=receipt['records'];assert r['instructions']==count
    assert sha(d/r['output'])==r['output_sha256']
    assert sha(d/'e27_rep_amd64.pcode.json')==r['pcode_sha256']
    rows=json.loads((d/'e27_rep_amd64.pcode.json').read_text());assert len(rows)==count
    elf=ELF(binary);lifter=X64RepLifter(Language(rows))
    for row in rows:
        address=int(row['address'],16);raw=bytes.fromhex(row['bytes'])
        assert raw==elf.read(address-0x100000,len(raw))
        assert '\t'+lifter.instruction(instruction(row))+'\n)' in (d/r['output']).read_text()
        print(kind,hex(address),row['bytes'],row['assembly'])
    assert receipt['frontier']==[hex(int(row['address'],16)+len(bytes.fromhex(row['bytes']))) for row in rows]
print('PASS runtime/inventory/decoder/implementation pins, ELF instruction bytes, 34 exact fragments, explicit fallthrough frontiers')
