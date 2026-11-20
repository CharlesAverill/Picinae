"""Check exact author declarations, lift, evidence, and authorized ancestry."""
from pathlib import Path
import hashlib
import re
import subprocess

BASE = '49956416928e5b6bb3928b54ae33e3b81091f006'
CHECKPOINT = 'e3ddea3cffe75231193e5b51e04a30ee7012e17a'
ALLOWED = set('''71470bffba65392adf1873a3df9f0cf0ca4f1ac9
081d0233cd6667803b3907343b2fea6dc9eba714
052521a753adbda077843ec7b259801282a7b1e9
378fe1b57514b9af3f017a72b4ca665910156cc7
9ae8e6800fa044797efd98372857e6ac89b18e1b
9b9ea8fbb9c0921b07a906daae3cecc7048cbf6b
e3ddea3cffe75231193e5b51e04a30ee7012e17a'''.split())

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()

assert git('rev-parse', 'origin/llm_generated_proofs') == BASE
assert git('merge-base', 'origin/llm_generated_proofs', 'HEAD') == BASE
assert set(git('rev-list', BASE + '..' + CHECKPOINT).split()) == ALLOWED
assert git('branch', '--show-current') == 'llm-proofs/a-inet-makeaddr-fix'
assert git('rev-parse', 'llm-proofs/a-inet-makeaddr') == CHECKPOINT
assert subprocess.run(['git', 'merge-base', '--is-ancestor', CHECKPOINT, 'HEAD']).returncode == 0
own = git('rev-list', CHECKPOINT + '..HEAD').split()
for commit in own:
    assert len(git('show', '-s', '--format=%P', commit).split()) == 1
    paths = git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines()
    assert all(p == 'Examples/claude/arm8_inet_makeaddr_proof.v' or
               p.startswith('notes/a-inet-makeaddr-fix/') for p in paths), paths
assert set(git('rev-list', BASE + '..HEAD').split()) == ALLOWED | set(own)

p = Path('Examples/claude/arm8_inet_makeaddr_proof.v')
current = p.read_text()
initial = Path('notes/a-inet-makeaddr/initial-attempt.v.txt').read_text()
statements = r'^(?:Theorem|Lemma)\s+[A-Za-z0-9_]+:[\s\S]*?(?=\nProof\.)'
defs = r'^Definition\s+[\s\S]*?\.\s*$'
original_statements = re.findall(statements, initial, re.M)
current_statements = re.findall(statements, current, re.M)
# The fixer adds no theorem contracts; every original statement stays byte exact.
assert current_statements == original_statements
assert len(original_statements) == 18
assert re.findall(defs, current, re.M) == re.findall(defs, initial, re.M)
print('PASS: all 18 theorem/lemma statements and all', len(re.findall(defs, initial, re.M)),
      'definitions retained verbatim; no new theorem contracts.')
assert len(re.findall(r'\bQed\.', current)) == 18
assert not re.search(r'\b(?:Abort|Admitted|admit|Axiom|Axioms|Parameter|Parameters)\b', current)
print('PASS: 18 Qed; no Abort/admission/axiom/parameter in completed module.')
lift = Path('Examples/claude/lifter/scalar_bitforms/e29_inet_makeaddr_arm8.v')
assert hashlib.sha256(lift.read_bytes()).hexdigest() == '41c9789da4f26019b8c8b9269f421d8f1ac74b0a34925d1b2b5d4c74a8d75ae8'
assert not git('diff', CHECKPOINT, '--', 'notes/a-inet-makeaddr', 'dune',
               'Examples/claude/lifter/scalar_bitforms')
assert Path('_build/default/Examples/claude/arm8_inet_makeaddr_proof.vo').is_file()
print('PASS: generated lift, original author evidence, and Dune list unchanged; full .vo exists.')
print('PASS: pinned merge base, seven exact checkpoint commits, only scoped linear fixer commits:', own)
