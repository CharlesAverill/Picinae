"""Preserve every previously checked and original x01 declaration verbatim."""
import re
import subprocess
from pathlib import Path
for name in ['amd64_memcpy_nt_proof', 'amd64_memcpy_nt_dispatch_proof']:
    path = 'Examples/claude/' + name + '.v'
    original = subprocess.check_output(['git', 'show', 'bd8890e88451eef3ee9ce382629b8a710b95e3ed:' + path], text=True)
    current = Path(path).read_text()
    for pattern in [r'(?m)^((?:Lemma|Theorem)\s+(\w+)\s*:[\s\S]*?)\nProof\.',
                    r'(?m)^(Definition\s+(\w+)\b[\s\S]*?\.)(?=\n)']:
        before = {name: statement for statement, name in re.findall(pattern, original)}
        after = {name: statement for statement, name in re.findall(pattern, current)}
        assert before
        for name, statement in before.items():
            assert after.get(name) == statement, 'Changed/missing: ' + name
            print('PRESERVED', path, name)
print('All checkpoint declarations preserved verbatim.')
