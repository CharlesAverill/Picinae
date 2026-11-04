from pathlib import Path
import re
old = Path('notes/r13-reset-event/initial-attempt.v.txt').read_text()
new = Path('Examples/FreeRTOS/armv6m_uxTaskResetEventItemValue_proof.v').read_text()
def declarations(s):
    s = re.sub(r'\(\*.*?\*\)', '', s, flags=re.S)
    s = re.sub(r'\bProof\..*?\bQed\.', 'Abort.', s, flags=re.S)
    return re.sub(r'\s+', ' ', s).strip()
assert declarations(old) == declarations(new)
names = re.findall(r'^(?:Theorem|Lemma|Corollary)\s+(\w+)', old, re.M)
assert len(names) == 15
for name in names:
    print('PRESERVED declaration:', name)
print('WIP: declarations preserved; proof status requires full .vo and assumptions.')
