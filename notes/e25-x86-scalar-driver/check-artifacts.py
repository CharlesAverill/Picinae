#!/usr/bin/env python3
"""Verify exact e01 sources, ELF/debug, instruction bytes, ISA and artifact pins."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tarfile

repo=Path(__file__).resolve().parents[2]
inv=Path('/home/charles/code/friends/.toolchains/e01-x86-inventory')
deps=Path('/home/charles/code/friends/.toolchains/e02-arm-inventory')
sys.path.insert(0,str(repo/'Examples/claude/inventory/e01-x86-inventory'))
from inventory import ELF, symbols
sha=lambda data:hashlib.sha256(data).hexdigest()
source_files=['stdlib/abs.c','stdlib/labs.c','sysdeps/wordsize-64/labs.c','nptl/pthread_equal.c','ctype/ctype-extn.c','ctype/ctype.h']
with tarfile.open(inv/'downloads/glibc_2.35.orig.tar.xz') as archive:
    for name in source_files:
        text=(inv/'source'/name).read_bytes()
        original=archive.extractfile('glibc-2.35/'+name).read()
        assert text==original,name
        print('SOURCE '+sha(text)+' '+name)
for f,digest in json.loads((repo/'Examples/claude/inventory/e01-x86-inventory/generated/target-manifest.json').read_text()).items():
    assert sha((inv/f).read_bytes())==digest,f
print('PASS full exact e01 manifest (runtime/debug/source archives/packages)')
for group,kind,root in [('x64_scalar_smoke','glibc',inv/'runtime/lib/x86_64-linux-gnu/libc.so.6'),('x64_scalar_fixture','synthetic',repo/'notes/e25-x86-scalar-driver/fixture/scalar.so')]:
    folder=repo/'Examples/claude/lifter'/group
    receipt=json.loads((folder/'SUCCESS.json').read_text())
    assert receipt['elf_sha256']==sha(root.read_bytes()) and receipt['source_kind']==kind
    elf=ELF(root)
    dbg=inv/'debug/usr/lib/debug/.build-id/08/5164b7e9093b36e3be17226f0d94a35b818c55.debug' if kind=='glibc' else root
    assert receipt['debug_sha256']==sha(dbg.read_bytes())
    syms=symbols(dbg,'exact')
    expected={'SUCCESS.json'}
    for r in receipt['records']:
        name='e25_'+r['symbol']+'_amd64'
        expected.update({name+'.v',name+'.pcode.json'})
        assert sha((folder/r['output']).read_bytes())==r['output_sha256']
        assert sha((folder/(name+'.pcode.json')).read_bytes())==r['pcode_sha256']
        rows=json.loads((folder/(name+'.pcode.json')).read_text())
        address=int(r['elf_entry'],16)
        assert (address,r['size']) in {(s['address'],s['size']) for s in syms if s['name']==r['symbol'] and s['type']=='FUNC'}
        data=b''
        for row in rows:
            assert int(row['address'],16)==address+0x100000+len(data)
            raw=bytes.fromhex(row['bytes'])
            assert elf.read(address+len(data),len(raw))==raw
            data+=raw
        assert len(rows)==r['instructions'] and len(data)==r['size']
        assert sha(data)==r['bytes_sha256']
        print(f'PASS {kind} {r["symbol"]} entry={r["entry"]} size={r["size"]} insns={len(rows)} bytes_sha256={sha(data)}')
    assert {f.name for f in folder.iterdir() if f.suffix in ('.json','.v')}==expected
    for f,digest in receipt['implementation_sha256'].items():assert sha((repo/'tools/ghidra-lifter'/f).read_bytes())==digest,f
    for f,digest in receipt['isa_sha256'].items():assert sha((deps/f).read_bytes())==digest,f
    print('PASS complete hashes, implementation pins, SLEIGH pins and exact instruction boundaries: '+group)
print(subprocess.check_output(['readelf','-n',str(inv/'runtime/lib/x86_64-linux-gnu/libc.so.6')],text=True))
