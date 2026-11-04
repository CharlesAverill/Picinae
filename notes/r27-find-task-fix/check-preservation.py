from pathlib import Path
import re, subprocess
path = 'Examples/FreeRTOS/armv6m_prvSearchForNameWithinSingleList_proof.v'
old = Path('notes/r27-find-task/initial-attempt.v.txt').read_text()
new = Path(path).read_text()
pat = r'(?m)^(?:Theorem|Lemma|Corollary)\s+(\w+)\s*:(.*?)\nProof\.'
a, b = (dict(re.findall(pat, text, re.S)) for text in (old, new))
assert all(b.get(k) == v for k,v in a.items()), 'Original statement changed'
def definitions(text):
    return re.findall(r'(?ms)^(?:Definition|Fixpoint)\s+.*?(?=\n\n)', text)
assert definitions(old) == definitions(new), 'Original definition changed'
subprocess.run(['git', 'diff', '--exit-code', '00ca4312875f97177309034d7ee743a5ca7bb03f', '--', 'notes/r27-find-task', 'Examples/FreeRTOS/prvSearchForNameWithinSingleList_armv6m.v', 'Examples/FreeRTOS/armv6m_list_model.v'], check=True)
print('PASS: all 19 original statements and all original definitions unchanged; original evidence, generated map and list kit unchanged')
print('Additional lemmas:', ', '.join(k for k in b if k not in a) or '(none)')
