import re
from pathlib import Path
initial=Path('notes/r18-mutex-held/initial-attempt.v.txt').read_text()
current=Path('Examples/FreeRTOS/armv6m_pvTaskIncrementMutexHeldCount_proof.v').read_text()
def declarations(text):
 text=re.sub(r'\(\*.*?\*\)','',text,flags=re.S)
 return [(m.group(1),' '.join(m.group(0).split())) for m in re.finditer(r'^(?:Theorem|Lemma|Corollary)\s+(\w+)\b.*?(?=\nProof\.)',text,re.M|re.S)]
a,b=declarations(initial),declarations(current)
assert a==b,(a,b)
for name,_ in a:print('PRESERVED',name)
assert len(a)==16
print('PASS: all 16 initial theorem/helper statements preserved exactly modulo whitespace.')
