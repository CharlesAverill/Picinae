"""Compare original author statements and definitions, ignoring proof bodies."""
import re
import subprocess
from pathlib import Path

path = 'Examples/claude/amd64_memcpy_nt_proof.v'
old = subprocess.check_output(['git', 'show', 'c63095989bf5d49153046d2285b3e27580346fde:' + path], text=True)
new = Path(path).read_text()
patterns = [r'(?m)^((?:Lemma|Theorem)\s+(\w+)\s*:[\s\S]*?)\nProof\.',
            r'(?m)^(Definition\s+(\w+)\b[\s\S]*?\.)(?=\n)']
for pattern in patterns:
    original = {name: text for text, name in re.findall(pattern, old)}
    current = {name: text for text, name in re.findall(pattern, new)}
    assert original
    for name, text in original.items():
        assert current.get(name) == text, 'Changed/missing author declaration: ' + name
        print('PRESERVED ' + name)
print('Every original theorem/lemma statement and definition is preserved verbatim.')
