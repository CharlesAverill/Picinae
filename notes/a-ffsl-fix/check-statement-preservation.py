"""Compare every author declaration independently of proof terminators.

Additional declarations are printed by name; changed/missing declarations fail.
The author's archived script and all author evidence remain unchanged.
"""
from pathlib import Path
import re


def declarations(text):
    text = re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    starts = list(re.finditer(r"^(Definition|Theorem|Lemma)\s+(\w+)\b", text, re.M))
    result = {}
    for i, m in enumerate(starts):
        end = re.search(r"\.(?=\s|$)", text[m.start():])
        assert end, f'Unterminated declaration: {m[2]}'
        declaration = text[m.start():m.start()+end.end()]
        assert m[2] not in result, m[2]
        result[m[2]] = ''.join(declaration.split())
    return result

initial = declarations(Path('notes/a-ffsl/initial-attempt.v.txt').read_text())
current_text = Path('Examples/claude/arm8_ffsl_proof.v').read_text()
current = declarations(current_text)
for name, statement in initial.items():
    assert name in current, f'Missing author declaration: {name}'
    assert current[name] == statement, f'Changed author declaration: {name}'
print(f'All {len(initial)} author declarations (including definitions) preserved exactly.')
print('New supporting declarations:', ', '.join(sorted(current.keys()-initial.keys())) or '(none)')
assert not re.search(r'^Abort\.$', current_text, re.M), 'Unfinished exported declarations'
print('Every proof terminates without Abort.')
