"""Check the assigned history, retained statements, and original evidence."""
from pathlib import Path
import hashlib
import re
import subprocess

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()

base = '49956416928e5b6bb3928b54ae33e3b81091f006'
checkpoint = '97fd8ecfb6adac59f137ca465a0bfb4beb3862ac'
proof = 'Examples/FreeRTOS/armv6m_vTaskInternalSetTimeOutState_proof.v'
lift = 'Examples/FreeRTOS/vTaskInternalSetTimeOutState_armv6m.v'
assert git('rev-parse', 'origin/llm_generated_proofs') == base
assert git('merge-base', base, 'HEAD') == base
assert git('rev-parse', '71470bff^') == base
assert git('merge-base', checkpoint, 'HEAD') == checkpoint
assert git('branch', '--show-current') == 'llm-proofs/r14-timeout-internal-fix'
for commit in git('rev-list', f'{checkpoint}..HEAD').splitlines():
    assert len(git('rev-list', '--parents', '-n', '1', commit).split()) == 2
    for path in git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines():
        assert path == proof or path.startswith('notes/r14-timeout-internal-fix/'), path
assert not git('diff', checkpoint, '--', lift, 'notes/r14-timeout-internal', 'dune')
original = Path('notes/r14-timeout-internal/initial-attempt.v.txt').read_text()
assert hashlib.sha256(original.encode()).hexdigest() == '49df58ae049ed945efccef14bb57475133dd0b09633ef4e9a75195f02baf55cf'
# Existing declarations and definitions must remain textually identical.
# Added helper lemmas may precede the first execution theorem.
strip = lambda s: re.sub(r'Proof\..*?(?:Qed|Abort)\.', 'PROOF_BODY', s, flags=re.S)
remove_comments = lambda s: re.sub(r'\(\*.*?\*\)', '', s, flags=re.S)
extract = lambda s: re.findall(r'(?:Definition|Theorem|Lemma|Corollary)\s+\w+\b.*?(?=PROOF_BODY|(?:Definition|Theorem|Lemma|Corollary)\s|\Z)', remove_comments(strip(s)), flags=re.S)
current = Path(proof).read_text()
cur_decls = {re.match(r'\w+\s+(\w+)', d)[1]: d.strip() for d in extract(current)}
for declaration in extract(original):
    name = re.match(r'\w+\s+(\w+)', declaration)[1]
    assert cur_decls[name] == declaration.strip(), name
prefix = 'Theorem timeout_correct :'
# Original eleven helper proof bodies also remain unchanged.
assert remove_comments(original.split(prefix)[0]).strip() in remove_comments(current).strip()
print('PASS: pinned origin, exact checkpoint ancestry, linear scoped fixer commits only')
print('PASS: generated map, root Dune, original author notes and snapshot unchanged')
print('PASS: every original statement/definition and eleven helper proofs unchanged')
for args in [('rev-parse', 'HEAD'), ('merge-base', 'origin/llm_generated_proofs', 'HEAD'),
             ('log', '--format=%H %s', 'origin/llm_generated_proofs..HEAD'),
             ('diff', '--stat', 'origin/llm_generated_proofs...HEAD'), ('status', '--short')]:
    print('git ' + ' '.join(args), flush=True)
    print(git(*args), flush=True)
