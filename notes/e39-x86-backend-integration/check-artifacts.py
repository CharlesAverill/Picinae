import hashlib,json,re
from pathlib import Path
P=Path(__file__).resolve().parent
repo=P.parents[1]
root=repo/'Examples/claude/lifter';build=Path('/home/charles/code/friends/.toolchains/e39-x86-backend-integration/dune/default')
files=sorted(p.relative_to(repo) for p in root.rglob('*.v') if p.parent.name.startswith(('x64_scalar_','x64_copy_','x64_rep_','x64_bitscan_','x64_integrated_')))
assert len(files)==39
for f in files:assert (build/f.with_suffix('.vo')).is_file(),f
assert [str(f) for f in files]==json.loads((P/'typing-targets.json').read_text())
source=root/'x64_integrated_fixture';receipt=json.loads((source/'SUCCESS.json').read_text())
for f,h in receipt['dependencies'].items():assert hashlib.sha256((repo/f).read_bytes()).hexdigest()==h,f
for r in receipt['records']:
    assert hashlib.sha256((source/r['output']).read_bytes()).hexdigest()==r['output_sha256']
    assert hashlib.sha256((source/r['output'].replace('.v','.pcode.json')).read_bytes()).hexdigest()==r['pcode_sha256']
rows=json.loads((source/'e39_mixed_amd64.pcode.json').read_text())
addresses={int(r['address'],16) for r in rows}
assert len(addresses)==17
for r in rows:
    if not r['assembly'].startswith(('RET','JMP')):assert int(r['address'],16)+len(bytes.fromhex(r['bytes'])) in addresses
for edge in receipt['direct_edges']:assert int(edge['target'],16) in addresses
text=(P/'logs/22-assumptions-exact.log').read_text()
assert text.count('Axioms:')==39
assert text.count('FunctionalExtensionality.functional_extensionality_dep :')==39
assert 'EXIT_CODE=0' in text
# Every assumptions block contains only the existing FE dependency.
for block in text.split('Axioms:\n')[1:]:
    assert block.startswith('FunctionalExtensionality.functional_extensionality_dep :\n')
print('PASS 39 compiled typing modules and 39 FE-only assumptions queries')
print('PASS all current dependency/output/raw hashes and 17 mixed selected instruction boundaries')
