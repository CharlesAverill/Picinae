from pathlib import Path
import subprocess
source = 'Examples/claude/amd64_memmove_avx_nt_proof.v'
base = subprocess.check_output(['git', 'show', '49956416928e5b6bb3928b54ae33e3b81091f006:' + source], text=True)
current = Path(source).read_text()
attempt = Path('notes/x02-avx-nt/initial-repair.v.txt').read_text()
for name in ('nt_seg_1285', 'memmove_avx_correct_nt'):
    def statement(s):
        return s[s.index(name + ':'):].split('Proof.', 1)[0]
    assert statement(base) == statement(current) == statement(attempt), name
    print(name + ': statement exactly unchanged in packaged source and attempt')
assert subprocess.check_output(['git', 'diff', '49956416928e5b6bb3928b54ae33e3b81091f006', '--', 'Examples/claude/memmove_avx_amd64.v']) == b''
print('Generated memmove_avx_amd64.v: unchanged against pinned origin base')
