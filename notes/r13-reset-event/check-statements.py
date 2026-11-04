from pathlib import Path
import re
old=Path('notes/r13-reset-event/initial-attempt.v.txt').read_text()
new=Path('Examples/FreeRTOS/armv6m_uxTaskResetEventItemValue_proof.v').read_text()
def declarations(s):
    s=re.sub(r'\(\*.*?\*\)','',s,flags=re.S)
    s=re.sub(r'\bProof\..*?\bQed\.','Abort.',s,flags=re.S)
    return re.sub(r'\s+',' ',s).strip()
assert declarations(old)==declarations(new)
for name in re.findall(r'^(?:Theorem|Lemma|Corollary)\s+(\w+)',old,re.M):
    print('PRESERVED, ABORTED:',name)
print('All definitions, declarations, theorem statements unchanged; only proof bodies removed.')
