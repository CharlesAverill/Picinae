"""Archive hygiene only: discard unchecked proofs, retaining exact statements."""
from pathlib import Path
import re
import hashlib
root = Path(__file__).resolve().parent
source = root.parent.parent / 'Examples/FreeRTOS/armv6m_uxListRemove_proof.v'
original = (root / 'initial-attempt.v.txt').read_text()
assert hashlib.sha256(original.encode()).hexdigest() == '9c3ab7428dc523d7df0de3df5f962f8c40d2017f1700ee09aad1235ee79c7833'
cut = original.index('Theorem list_remove_correct:')
rest, count = re.subn(r'\bProof\.(.*?)\bQed\.', 'Abort.', original[cut:], flags=re.S)
assert count == 9
final = original[:cut] + rest
source.write_text(final)
def statements(text):
    return re.sub(r'\bProof\.(.*?)\bQed\.|\bAbort\.', '', text, flags=re.S)
assert statements(final) == statements(original)
assert final.count('Qed.') == 7 and final.count('Abort.') == 9
print('All definitions, theorem statements and Ltac declarations are byte-for-byte preserved.')
print('Seven completed Qed bodies preserved verbatim; nine unchecked proof bodies replaced by Abort.')
for kind, name in re.findall(r'\b(Theorem|Lemma)\s+(\w+)\s*:', final):
    print(kind, name)
