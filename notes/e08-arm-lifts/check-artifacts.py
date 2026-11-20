#!/usr/bin/env python3
"""Recompute hashes, exact naming-only transformation, bytes and map closure."""
import importlib.util
import json
from pathlib import Path
import re
import sys
spec = importlib.util.spec_from_file_location('extract', Path(__file__).with_name('extract.py'))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
root = Path(sys.argv[1]) if len(sys.argv)>1 else m.REPO/'Examples/claude/lifter/scalar_ports'
hashes = json.loads((root/'HASHES.json').read_text())
assert set(p.name for p in root.iterdir()) == set(hashes) | {'HASHES.json'}
for name,digest in hashes.items():
    assert m.sha((root/name).read_bytes()) == digest, name
coverage = json.loads((root/'COVERAGE.json').read_text())
assert not any(r['status']=='not-attempted' for r in coverage['ports'])
elf=m.ELF(m.DEPS/'root/lib/aarch64-linux-gnu/libc.so.6')
assert m.sha(elf.data)==m.EXPECTED
for r in coverage['accepted']:
    n=r['artifact']; manifest=json.loads((root/f'{n}.manifest.json').read_text())
    v=(root/f'{n}.v').read_text()
    assert m.sha(v.encode())==manifest['generated_program_sha256']
    old=manifest['naming_adapter']['old']
    original=v.replace(n,old)
    assert m.sha(original.encode())==manifest['original_program_sha256']
    rows=json.loads((root/f'{n}.pcode.json').read_text())
    assert len(rows)==r['instructions']==manifest['instruction_count']
    addresses={int(x['address'],16) for x in rows}
    assert m.control_flow(rows,addresses)==manifest['closure']
    clauses={int(a,16) for a in re.findall(r'^\| (0x[0-9a-f]+) => Some \(4,',v,re.M)}
    assert addresses==clauses
    for row in rows:
        assert elf.at(int(row['address'],16)-0x100000,4).hex()==row['bytes']
    for ref in manifest['data']['materialized_objects']:
        if ref['file_backed']:
            assert elf.at(int(ref['elf_address'],16),ref['size']).hex()==ref['elf_bytes_hex']
    assert not re.search(r'\b(?:Admitted|admit|Axiom|Parameter)\b',v)
    print('PASS',n,len(rows),'instructions;',len(manifest['closure']['returns']),'RETURN sites; naming-only hash/ELF bytes/closed edges/data')
print('PASS all published file hashes and full e02 port accounting')
