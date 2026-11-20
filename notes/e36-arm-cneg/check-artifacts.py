#!/usr/bin/env python3
"""Recheck pinned bytes, complete maps, naming adapters, and fixture IL."""
import json
import re
import sys
from validate import ART, REPO, e08, sha

sys.path.insert(0, str(REPO / 'tools/ghidra-lifter'))
from test_cneg import RAW, cases, lower

hashes = json.loads((ART / 'HASHES.json').read_text())
assert {p.name for p in ART.iterdir()} == set(hashes) | {'HASHES.json'}
for name, digest in hashes.items(): assert sha(ART / name) == digest, name
elf = e08.ELF(e08.DEPS / 'root/lib/aarch64-linux-gnu/libc.so.6')
assert e08.sha(elf.data) == e08.EXPECTED == RAW['elf_sha256']
assert json.loads((ART / 'IL.json').read_text()) == [dict(bytes=r['bytes'], assembly=r['assembly'], il=lower(r)) for r in cases()]
fixture = (ART / 'e36_cneg.v').read_text()
for i, row in enumerate(cases()): assert f'Definition fixture_{i} : stmt :=\n{lower(row)}.\n' in fixture
for name, rows in RAW['targets'].items():
    for r in rows: assert elf.at(int(r['address'], 16) - 0x100000, 4).hex() == r['bytes']
audit = json.loads((REPO / 'notes/e36-arm-cneg/memcmp-instruction-audit.json').read_text())
assert audit['total'] == len(RAW['targets']['memcmp']) == 114
accepted = set(audit['accepted_addresses'])
rejected = {r['address'] for r in audit['rejected']}
assert len(accepted) == 97 and len(rejected) == 17 and not accepted & rejected
assert accepted | rejected == {r['address'] for r in RAW['targets']['memcmp']}
assert {'0x1946e4','0x194800'} <= accepted
assert sorted(rejected)[0] == '0x194780'
assert not list(ART.glob('*memcmp*'))
assert len(list(ART.glob('*.v'))) == 1
print('PASS exact memcmp diagnostics: 97 instruction acceptances, 17 vector rejections; no function map')
print('PASS all hashes, exact ELF raw bytes and 168 raw-pcode/IL fixtures; no new function map published')
