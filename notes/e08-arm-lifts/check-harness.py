#!/usr/bin/env python3
"""Exercise edge-closure failures against actual e11 raw-pcode format."""
import importlib.util
from pathlib import Path
import json
spec = importlib.util.spec_from_file_location('extract', Path(__file__).with_name('extract.py'))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
rows = json.loads((m.REPO/'Examples/claude/lifter/scalar_global/e11_mempcpy_arm8.pcode.json').read_text())
addresses = {int(r['address'],16) for r in rows}
f = m.control_flow(rows, addresses)
assert f['closed'] and len(f['returns']) == 8, len(f['returns'])
assert any(e['kind']=='CALL' and e['target']=='0x19ab40' for e in f['direct_and_fallthrough_edges'])
for bad in [rows[:9], [dict(address='0x1000', pcode=[' ---  BRANCHIND (register, 0x4000, 8)'])],
            [dict(address='0x1000', pcode=[])],
            [dict(address='0x1000', pcode=[' ---  CALL (ram, 0x1000, 8)'])]]:
    try:
        m.control_flow(bad, {int(r['address'],16) for r in bad})
    except ValueError as e:
        print('EXPECTED_REJECTION',e)
    else:
        raise AssertionError('accepted an unclosed map')
print('PASS actual memcpy+mempcpy closure and four unclosed maps rejected')
