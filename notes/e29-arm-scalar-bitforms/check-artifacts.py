#!/usr/bin/env python3
"""Recheck pinned bytes, complete maps, naming adapters, and fixture IL."""
import json
import re
import sys
from validate import ART, REPO, e08, sha

sys.path.insert(0, str(REPO / 'tools/ghidra-lifter'))
from test_bitforms import RAW, cases, lower

hashes = json.loads((ART / 'HASHES.json').read_text())
assert {p.name for p in ART.iterdir()} == set(hashes) | {'HASHES.json'}
for name, digest in hashes.items(): assert sha(ART / name) == digest, name
elf = e08.ELF(e08.DEPS / 'root/lib/aarch64-linux-gnu/libc.so.6')
assert e08.sha(elf.data) == e08.EXPECTED == RAW['elf_sha256']
assert json.loads((ART / 'IL.json').read_text()) == [dict(bytes=r['bytes'], assembly=r['assembly'], il=lower(r)) for r in cases()]
fixture = (ART / 'e29_bitforms.v').read_text()
for i, row in enumerate(cases()): assert f'Definition fixture_{i} : stmt :=\n{lower(row)}.\n' in fixture
for name, rows in RAW['targets'].items():
    for r in rows: assert elf.at(int(r['address'], 16) - 0x100000, 4).hex() == r['bytes']
for symbol in ('inet_makeaddr', 'rand_r'):
    n = f'e29_{symbol}_arm8'
    m = json.loads((ART / (n + '.manifest.json')).read_text())
    for f, h in m['implementation_sha256'].items(): assert sha(REPO / 'tools/ghidra-lifter' / f) == h
    assert sha(REPO / 'notes/e29-arm-scalar-bitforms/validate.py') == m['harness_sha256']
    text = (ART / (n + '.v')).read_text()
    assert sha(ART / (n + '.v')) == m['generated_program_sha256']
    assert sha(ART / (n + '.pcode.json')) == m['pcode_sha256']
    assert text.count(n) == 2
    original = text.replace(n, m['naming_adapter']['old'])
    assert e08.sha(original.encode()) == m['record']['output_sha256']
    rows = json.loads((ART / (n + '.pcode.json')).read_text())
    keys = {int(r['address'], 16) for r in rows}
    assert len(keys) == len(rows) == m['record']['instructions']
    assert keys == {int(a, 16) for a in re.findall(r'^\| (0x[0-9a-f]+) => Some \(4,', text, re.M)}
    assert e08.control_flow(rows, keys) == m['closure']
    raw = RAW['targets'][symbol]
    assert rows == [{k: r[k] for k in ('address', 'assembly', 'bytes', 'pcode')} for r in raw]
    print('PASS', symbol, len(rows), 'exact ELF instructions; naming-only adaptation; closed map; implementation hashes')
print('PASS all file hashes and 25 raw-pcode/IL fixtures')
