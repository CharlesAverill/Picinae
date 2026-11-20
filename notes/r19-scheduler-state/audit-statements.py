import hashlib,re
from pathlib import Path
p=Path('Examples/FreeRTOS/armv6m_xTaskGetSchedulerState_proof.v')
a=Path('notes/r19-scheduler-state/initial-attempt.v.txt').read_text()
b=p.read_text()
assert hashlib.sha256(a.encode()).hexdigest()=='d7db5e3a1d34a8ad8ba713349e3c17af3548e2968a02f134636bd08b6aa9f4d7'
pattern=r'(?ms)^(?:Theorem|Lemma|Corollary)\s+(\w+)\s*:(.*?)\nProof\.'
orig=re.findall(pattern,a)
active=re.findall(pattern,b)
assert orig==active, 'Theorem statements changed'
print('All',len(orig),'theorem/lemma/corollary statements retained verbatim:')
for name,_ in orig:print(name)
# Definitions contain no periods except their terminator; check exact text.
pat=r'(?ms)^Definition\s+\w+.*?\.\n'
assert re.findall(pat,a)==re.findall(pat,b)
print('All',len(re.findall(pat,a)),'definitions retained verbatim')
