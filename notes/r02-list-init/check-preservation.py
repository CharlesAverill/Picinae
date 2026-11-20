from pathlib import Path
import re

original = Path('notes/r02-list-init/initial-attempt.v.txt').read_text()
current = Path('Examples/FreeRTOS/armv6m_vListInitialise_proof.v').read_text()

def declarations(text):
    text = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
    text = re.sub(r'Proof\..*?(?:Qed|Abort)\.', '', text, flags=re.S)
    return re.sub(r'\s+', ' ', text).strip()

assert declarations(original) == declarations(current), 'Declarations changed'
assert len(re.findall(r'^(?:Theorem|Lemma) ', original, re.M)) == 12
assert current.count('Abort.') == 4
print('PASS: all 12 theorem/lemma statements and all definitions unchanged; four unchecked proofs aborted')
