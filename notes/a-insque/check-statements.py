from pathlib import Path
import re
import hashlib
initial = Path('notes/a-insque/initial-attempt.v.txt').read_text()
final = Path('Examples/claude/arm8_insque_proof.v').read_text()
def statements(text):
    return re.findall(r'(?:Theorem|Lemma)\s+\w+\s*:.*?(?=Proof\.)', text, re.S)
assert statements(initial) == statements(final)
assert len(statements(initial)) == 19
print('All 19 initial theorem/lemma statements preserved exactly.')
print('Initial snapshot SHA256:', hashlib.sha256(initial.encode()).hexdigest())
print('Remaining Qed:', len(re.findall(r'\bQed\.', final)))
print('Abort:', len(re.findall(r'\bAbort\.', final)))
assert not Path('_build/default/Examples/claude/arm8_insque_proof.vo').exists()
print('No full proof target .vo exists.')
