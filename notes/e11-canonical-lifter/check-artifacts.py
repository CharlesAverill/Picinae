#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path
repo = Path(__file__).resolve().parents[2]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for folder in ('scalar_smoke', 'scalar_global'):
    root=repo/'Examples/claude/lifter'/folder
    manifest=json.loads((root/'SUCCESS.json').read_text())
    for name, expected in manifest['implementation_sha256'].items():
        assert sha(repo/'tools/ghidra-lifter'/name)==expected, name
    for r in manifest['records']:
        assert sha(root/r['output'])==r['output_sha256']
        trace=json.loads((root/r['output'].replace('.v','.pcode.json')).read_text())
        assert len(trace)==r['instructions']
        assert len({x['address'] for x in trace})==len(trace)
        assert all(len(bytes.fromhex(x['bytes']))==4 for x in trace)
        print(folder,r['symbol'],r['instructions'],'instruction byte/pcode records; hashes PASS')
selected=list((repo/'_build/default/Examples/claude').rglob('*.vo'))
assert len(selected)==8,[str(p) for p in selected]
assert all('/lifter/scalar_' in str(p) for p in selected)
assert not list((repo/'_build/default/Examples/claude/inventory').rglob('*.vo'))
print('PASS exactly eight selected new fixture .vo files; no e02 inventory .vo duplicates')
