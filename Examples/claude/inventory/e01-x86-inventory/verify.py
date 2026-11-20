#!/usr/bin/env python3
"""Cross-check the inventory with nm, independently extracted .text, and dispatch."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
from retrieve import DEFAULT_ROOT, LIBC_SHA, BUILD_ID, sha

HERE=Path(__file__).resolve().parent
OUT=HERE/'generated'
libc=DEFAULT_ROOT/'runtime/lib/x86_64-linux-gnu/libc.so.6'
debug=DEFAULT_ROOT/f'debug/usr/lib/debug/.build-id/{BUILD_ID[:2]}/{BUILD_ID[2:]}.debug'
assert sha(libc)==LIBC_SHA
for line in (OUT/'SHA256SUMS').read_text().splitlines():
    digest,name=line.split('  ',1)
    assert sha(OUT/name)==digest,name
print('PASS: output checksum manifest')
inventory=json.loads((OUT/'inventory.json').read_text())
# nm is a second symbol-table reader, separate from inventory.py's readelf parser.
nm=subprocess.check_output(['nm','-a','-S','--defined-only',str(debug)],text=True)
observed={}
for line in nm.splitlines():
    m=re.match(r'([0-9a-f]+) ([0-9a-f]+) \S (\S+)$',line)
    if m:
        observed[m[3]]=(int(m[1],16),int(m[2],16))
for s in inventory['symbols']:
    if s['table']=='debug-symtab':
        assert observed[s['name']]==(int(s['elf_address'],16),s['size']),s['name']
print('PASS: all selected debug-symbol addresses/sizes independently agree with nm')
# Section extraction independently checks hashes computed through PT_LOAD mapping.
sections=subprocess.check_output(['readelf','-SW',str(libc)],text=True)
text_address=int(re.search(r'\[\s*\d+\]\s+\.text\s+PROGBITS\s+([0-9a-f]+)',sections)[1],16)
with tempfile.TemporaryDirectory(prefix='e01-section-') as tmp:
    textfile=Path(tmp)/'text.bin'
    subprocess.run(['objcopy','--dump-section',f'.text={textfile}',str(libc),str(Path(tmp)/'copy.elf')],check=True)
    text=textfile.read_bytes()
    for extent in inventory['extents']:
        offset=int(extent['elf_address'],16)-text_address
        assert offset>=0
        assert len(text[offset:offset+extent['size']])==extent['size']
        assert hashlib.sha256(text[offset:offset+extent['size']]).hexdigest()==extent['sha256']
print(f'PASS: {len(inventory["extents"])} extent hashes agree with independent objcopy .text extraction')
source=json.loads((OUT/'ifunc-implementations.json').read_text())
resolvers=json.loads((OUT/'resolvers.json').read_text())
prefixes=('memcpy','memmove','mempcpy','memcpy_chk','memmove_chk','mempcpy_chk')
byname={s['name']:s for s in inventory['symbols']}
suffixes=None
for prefix in prefixes:
    public='__'+prefix if prefix.endswith('_chk') else prefix
    candidates=[r for r in source if r['public']==public]
    suffix_set={r['implementation'].removeprefix('__'+prefix+'_') for r in candidates}
    assert len(suffix_set)==14
    assert suffixes is None or suffixes==suffix_set
    suffixes=suffix_set
    # Runtime resolver references must corroborate each source candidate's actual address.
    resolver,=[r for r in resolvers if public in r['names'] or '__'+public in r['names']]
    targets={int(r['target'],16) for r in resolver['rip_references']}
    for candidate in candidates:
        assert int(byname[candidate['implementation']]['elf_address'],16) in targets,candidate
print('PASS: all 84 copy candidates exist and occur in their six actual IFUNC resolvers')
for suffix in suffixes:
    a,b=(byname['__'+p+'_'+suffix] for p in ('memcpy','memmove'))
    assert (a['elf_address']==b['elf_address'])==(suffix not in ('ssse3','ssse3_back'))
    a,b=(byname['__'+p+'_'+suffix] for p in ('memcpy_chk','memmove_chk'))
    assert (a['elf_address']==b['elf_address'])==(suffix not in ('ssse3','ssse3_back'))
print('PASS: SSSE3 copy/check entries remain distinct; other copy/check address aliases agree')
comparisons=json.loads((OUT/'existing-lifts.json').read_text())
for c in comparisons:
    assert c['instructions']==c['matched_boundaries']
    assert not c['direct_targets_outside_lift']
    assert all(r['annotation'].startswith('NOP ') and r['disassembly'].startswith('prefetcht0 ') for r in c['issues'])
    print(f'PASS: {c["file"]}: {c["instructions"]} instruction boundaries/lengths; {len(c["issues"])} explicit NOP/prefetch annotation discrepancies')
print('N/A: theorem checking and Print Assumptions (binary inventory; no theorem added/adapted)')
