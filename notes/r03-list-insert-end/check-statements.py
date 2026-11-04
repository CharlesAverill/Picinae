from pathlib import Path
import re
original = Path('notes/r03-list-insert-end/initial-attempt.v.txt').read_text()
current = Path('Examples/FreeRTOS/armv6m_vListInsertEnd_proof.v').read_text()
def without_proofs(text):
    return re.sub(r'Proof\.(.*?)(?:Qed|Abort)\.', '', text, flags=re.S)
assert without_proofs(original) == without_proofs(current)
print('PASS: all statements, definitions and non-proof text unchanged')
print('Completed Qed blocks:', current.count('Qed.'))
print('Aborted unchecked proof blocks:', current.count('Abort.'))
