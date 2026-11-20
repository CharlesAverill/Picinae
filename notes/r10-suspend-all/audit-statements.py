"""Keep the Astra declarations stable across any subsequent authorized repair."""
import hashlib
import re
from pathlib import Path

initial = Path('notes/r10-suspend-all/initial-attempt.v.txt').read_text()
current = Path('Examples/FreeRTOS/armv6m_vTaskSuspendAll_proof.v').read_text()
assert hashlib.sha256(initial.encode()).hexdigest() == '50f84eb3cf4b90cf8ac40dac817e929faed92c5a6981a0470a606b1b524ee87b'

def statements(text):
    return re.findall(r'^((?:Theorem|Lemma|Corollary)\s+.*?)(?=\nProof\.)', text, re.M | re.S)

def definitions(text):
    return re.findall(r'^(Definition\s+.*?)(?=\n\n)', text, re.M | re.S)

assert statements(current) == statements(initial), 'Theorem statement changed; explain genuine corrections explicitly'
assert definitions(current) == definitions(initial), 'Definition changed; explain genuine corrections explicitly'
print(f'PASS: {len(statements(initial))} exact original statements and {len(definitions(initial))} exact original definitions')
for declaration in statements(current):
    print(declaration.splitlines()[0])
