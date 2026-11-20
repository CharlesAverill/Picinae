"""Compare all declarations/definitions with the exact Astra archive."""
from pathlib import Path
import re
import subprocess
archive = Path('notes/a-wcschrnul/initial-attempt.v.txt').read_text()
current = Path('Examples/claude/arm8_wcschrnul_proof.v').read_text()
pattern = r'(?ms)^(?:Theorem|Lemma) .*?(?=^Proof\.)'
a, b = re.findall(pattern, archive), re.findall(pattern, current)
assert a == b and len(a) == 11, 'Original theorem declarations changed'
print('All 11 original theorem/lemma statements retained verbatim.')
pattern = r'(?ms)^Definition .*?(?=\n\n)'
a, b = re.findall(pattern, archive), re.findall(pattern, current)
assert a == b, 'Original definitions changed'
print(f'All {len(a)} original definitions retained verbatim.')
for directory in ('notes/a-wcschrnul', 'Examples/claude/lifter/scalar_ccmp'):
    delta = subprocess.check_output(['git', 'diff', '1c2abb70e24ea225674978b19053cd05b392b334', '--', directory])
    assert not delta, f'Protected original artifacts changed: {directory}'
print('Original notes/archive and entire e30 artifact directory unchanged.')
