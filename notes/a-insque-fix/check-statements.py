from pathlib import Path
import re
import hashlib
initial = Path('notes/a-insque/initial-attempt.v.txt').read_text()
final = Path('Examples/claude/arm8_insque_proof.v').read_text()
def statements(text):
    return re.findall(r'(?:Theorem|Lemma)\s+\w+\s*:.*?(?=Proof\.)', text, re.S)
def definitions(text):
    return re.findall(r'Definition\s+\w+.*?\.\n', text, re.S)
assert statements(initial) == statements(final)
assert len(statements(initial)) == 19
assert definitions(initial) == definitions(final)
print('All 19 initial theorem/lemma statements and all', len(definitions(initial)), 'definitions preserved exactly.')
print('Initial snapshot SHA256:', hashlib.sha256(initial.encode()).hexdigest())
assert len(re.findall(r'\bQed\.', final)) == 19
assert not re.search(r'\b(?:Abort|Admitted|admit|Axiom|Parameter)\b', final)
assert Path('_build/default/Examples/claude/arm8_insque_proof.vo').exists()
print('19 Qed; no Abort/admission/axiom/parameter; full proof .vo exists.')
