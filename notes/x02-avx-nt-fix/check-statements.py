from pathlib import Path
import re
import subprocess
base = '49956416928e5b6bb3928b54ae33e3b81091f006'
p = 'Examples/claude/amd64_memmove_avx_nt_proof.v'
a = subprocess.check_output(['git', 'show', base + ':' + p], text=True)
b = Path(p).read_text()
for name in ('nt_seg_1285', 'memmove_avx_correct_nt'):
    def statement(text):
        return text[text.index(name + ':'):].split('Proof.', 1)[0]
    assert statement(a) == statement(b), name
    print(name + ': public statement byte-for-byte unchanged')
for name in ('nk', 'nr', 'done2', 'done4', 'nt_exit', 'nt_invs'):
    def definition(text):
        return re.search(r'^Definition ' + name + r'\b.*?\.(?=\s)', text, re.M | re.S)[0]
    assert definition(a) == definition(b), name
    print(name + ': predicate byte-for-byte unchanged')
for name in ('nt_seg_1117', 'nt_seg_1125', 'nt_seg_1210',
             'nt_seg_1613', 'nt_seg_1621', 'nt_seg_1706', 'nt_adv2', 'cpy_store8'):
    def lemma(text):
        start = text.index('Lemma ' + name + ':')
        end = text.index('Qed.', start) + 4
        return text[start:end]
    assert lemma(a) == lemma(b), name
    print(name + ': existing proved source byte-for-byte unchanged')
p = 'Examples/claude/memmove_avx_amd64.v'
assert subprocess.check_output(['git', 'diff', base, '--', p]) == b''
print(p + ': generated lift unchanged')
