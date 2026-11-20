import hashlib, re, subprocess
from pathlib import Path

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()
base = '49956416928e5b6bb3928b54ae33e3b81091f006'
checkpoint = 'efb04e07c821be4b78f20714edb727c4f4ee36e7'
proof = 'Examples/FreeRTOS/armv6m_pvTaskIncrementMutexHeldCount_proof.v'
assert git('rev-parse', 'origin/llm_generated_proofs') == base
assert git('merge-base', 'origin/llm_generated_proofs', 'HEAD') == base
assert git('merge-base', checkpoint, 'HEAD') == checkpoint
assert git('branch', '--show-current') == 'llm-proofs/r18-mutex-held-fix'
assert git('rev-list', '--parents', '-n1', '71470bffba65392adf1873a3df9f0cf0ca4f1ac9').split() == ['71470bffba65392adf1873a3df9f0cf0ca4f1ac9', base]
def scoped(p):
    return p == proof or p.startswith('notes/r18-mutex-held-fix/')
for c in git('rev-list', checkpoint+'..HEAD').splitlines():
    assert len(git('rev-list', '--parents', '-n1', c).split()) == 2
    assert all(scoped(p) for p in git('diff-tree', '--no-commit-id', '--name-only', '-r', c).splitlines())
assert all(scoped(p) for p in git('diff', '--name-only', checkpoint).splitlines())
assert hashlib.sha256(Path('Examples/FreeRTOS/pvTaskIncrementMutexHeldCount_armv6m.v').read_bytes()).hexdigest() == '447b2821c35d983c36509cdbbe0bdd6e53c35a9594bcdd3af872c45ebb6dbf53'
assert hashlib.sha256(Path('notes/r18-mutex-held/initial-attempt.v.txt').read_bytes()).hexdigest() == '645995bad29c07910a2eac3c71c7b3e811ecf820f25763f2569cad85fb3ab45f'
assert git('diff', checkpoint, '--', 'notes/r18-mutex-held', 'dune') == ''
def declarations(s):
    s = re.sub(r'\(\*.*?\*\)', '', s, flags=re.S)
    return [' '.join(m.group(0).split()) for m in re.finditer(r'^(?:Theorem|Lemma|Corollary|Definition)\s+.*?(?=\nProof\.|\.\n)', s, re.M|re.S)]
assert declarations(Path('notes/r18-mutex-held/initial-attempt.v.txt').read_text()) == declarations(Path(proof).read_text())
print('PASS: all original theorem/helper statements and definitions preserved; map, original evidence, and explicit Dune list unchanged.')
print('PASS: exact assigned checkpoint ancestry, only scoped linear fixer commits above it.')
for args in [('rev-parse','HEAD'), ('merge-base','origin/llm_generated_proofs','HEAD'), ('log','--format=%H %s','origin/llm_generated_proofs..HEAD'), ('diff','--stat','origin/llm_generated_proofs...HEAD'), ('status','--short','--branch')]:
    print('git '+' '.join(args)); print(git(*args))
