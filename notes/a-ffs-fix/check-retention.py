import json, re, subprocess
from pathlib import Path
source = Path('Examples/claude/arm8_ffs_proof.v').read_text()
archive = Path('notes/a-ffs/initial-attempt.v.txt').read_text()
original = json.loads(Path('notes/a-ffs/statements.json').read_text())
statements = re.findall(r'(?:Theorem|Lemma)\s+(\w+)[\s\S]*?(?=\nProof\.)', source)
assert len(statements) >= 16
for item in original:
    assert item['statement'] in source, item['name']
    print('Unchanged statement:', item['name'])
for name in re.findall(r'^Definition (\w+)', archive, re.M):
    pattern = r'^Definition '+name+r'\b[\s\S]*?\.(?=\n)'
    before = re.search(pattern, archive, re.M).group(0)
    after = re.search(pattern, source, re.M).group(0)
    assert before == after, name
    print('Unchanged definition:', name)
for path in ['Examples/claude/ffs_arm8.v', 'Examples/claude/lifter/scalar_smoke/e11_ffs_arm8.v']:
    before = subprocess.check_output(['git','show',f'6acd817:{path}'])
    assert before == Path(path).read_bytes(), path
    print('Unchanged generated map:', path)
for path in subprocess.check_output(['git','ls-tree','-r','--name-only','6acd817','notes/a-ffs']).decode().splitlines():
    assert subprocess.check_output(['git','show',f'6acd817:{path}']) == Path(path).read_bytes(), path
print('Original author evidence preserved byte-for-byte.')
