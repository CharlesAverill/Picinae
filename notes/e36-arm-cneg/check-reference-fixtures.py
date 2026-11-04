#!/usr/bin/env python3
"""Prior finite fixture statements remain byte-identical with the new backend."""
import importlib
import json
from pathlib import Path
import sys
repo=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(repo/'tools/ghidra-lifter'))
for module,folder,name in [('test_bitforms','scalar_bitforms','e29_bitforms'),('test_ccmp','scalar_ccmp','e30_ccmp')]:
    m=importlib.import_module(module)
    root=repo/'Examples/claude/lifter'/folder
    rows=m.cases()
    actual=[dict(bytes=r['bytes'],assembly=r['assembly'],il=m.lower(r)) for r in rows]
    assert actual==json.loads((root/'IL.json').read_text())
    fixture=(root/(name+'.v')).read_text()
    for i,row in enumerate(rows): assert f'Definition fixture_{i} : stmt :=\n{m.lower(row)}.\n' in fixture
    print('PASS',name,len(rows),'unchanged raw-pcode/IL/Rocq fixture statements')
