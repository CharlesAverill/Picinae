from pathlib import Path
import hashlib, re
attempt = Path('notes/a-remque/initial-attempt.v.txt').read_text()
active = Path('Examples/claude/arm8_remque_proof.v').read_text()
assert hashlib.sha256(attempt.encode()).hexdigest() == '18b7fa70349834a758a6f45f018dd98da6f0f196812664ead382de997ebf38e2'
def statements(text):
    text = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
    text = re.sub(r'Proof\..*?Qed\.', 'Abort.', text, flags=re.S)
    return re.sub(r'\s+', ' ', text).strip()
assert statements(attempt) == statements(active), 'Statement/definition changed'
assert active.count('Abort.') == 8
assert not Path('_build/default/Examples/claude/arm8_remque_proof.vo').exists()
print('Initial attempt hash unchanged; every statement and definition retained.')
print('Eight unfinished proof bodies marked Abort; no full proof-module .vo exists.')
print('No second compilation performed.')
