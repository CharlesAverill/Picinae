#!/usr/bin/env python3
"""Verify receipts, ELF/debug extents, raw instruction bytes and protected files."""
import hashlib,json,sys,subprocess
from pathlib import Path
repo=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(repo/'Examples/claude/inventory/e01-x86-inventory'))
from inventory import ELF,symbols
inv=Path('/home/charles/code/friends/.toolchains/e01-x86-inventory')
deps=Path('/home/charles/code/friends/.toolchains/e02-arm-inventory')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for f,h in json.loads((repo/'Examples/claude/inventory/e01-x86-inventory/generated/target-manifest.json').read_text()).items():assert sha(inv/f)==h,f
for f,h in json.loads((repo/'notes/e25-x86-scalar-driver/isa-pins.json').read_text()).items():assert sha(deps/f)==h,f
count=rows_count=0
for directory in sorted((repo/'Examples/claude/lifter').glob('x64_bitscan_*')):
    receipt=json.loads((directory/'SUCCESS.json').read_text())
    synthetic=receipt['source_kind']=='synthetic'
    binary=repo/'notes/e28-x86-bitscan-lowering/fixture/bitscan.so' if synthetic else inv/'runtime/lib/x86_64-linux-gnu/libc.so.6'
    elf=ELF(binary)
    debug=binary if synthetic else inv/'debug/usr/lib/debug/.build-id/08/5164b7e9093b36e3be17226f0d94a35b818c55.debug'
    assert sha(binary)==receipt['elf_sha256'] and sha(debug)==receipt['debug_sha256']
    for f,h in receipt['implementation_sha256'].items():assert sha(repo/'tools/ghidra-lifter'/f)==h,f
    for record in receipt['records']:
        p=directory/record['output'];trace=p.with_suffix('.pcode.json')
        assert sha(p)==record['output_sha256'] and sha(trace)==record['pcode_sha256']
        rows=json.loads(trace.read_text());assert len(rows)==record['instructions']
        for r in rows:assert bytes.fromhex(r['bytes'])==elf.read(int(r['address'],16)-0x100000,len(bytes.fromhex(r['bytes'])))
        extents=[(int(x['elf_entry'],16),x['size']) for x in record['extents']]
        assert hashlib.sha256(b''.join(elf.read(a,n) for a,n in extents)).hexdigest()==record['bytes_sha256']
        if receipt['source_kind']!='samples':
            actual={(s['address'],s['size']) for s in symbols(debug,'exact-debug') if s['name']==record['symbol'] and s['type']=='FUNC'}
            assert set(extents)==actual
            assert sum(len(bytes.fromhex(r['bytes'])) for r in rows)==sum(n for a,n in extents)
        count+=1;rows_count+=len(rows)
print('PASS',count,'receipts/artifact pairs;',rows_count,'raw instruction bytes/rows; exact debug extents; ISA/implementation pins')
# Only the reviewed checkpoint and this unit's changes may be present.
changed=subprocess.check_output(['git','diff','--name-only','328088263ebba11786a03448808e584231504fe1'],text=True).splitlines()
allowed={'dune','tools/ghidra-lifter/lift-x64.py','tools/ghidra-lifter/pcode2coq_x64.py','tools/ghidra-lifter/test_scalar.py'}
for f in changed:
    assert f in allowed or f.startswith(('notes/e28-x86-bitscan-lowering/','Examples/claude/lifter/x64_bitscan_')) or Path(f).name in ('pcode2coq_bitscan.py','bitscan_headless.py','lift-bitscan.py','test_bitscan.py','test_bitscan_publication.py'),f
print('PASS historical programs/proofs, core ISA, ARM driver and e25 artifacts unchanged')
