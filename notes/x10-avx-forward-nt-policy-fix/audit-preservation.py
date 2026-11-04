from pathlib import Path
import re, subprocess
proof='Examples/claude/amd64_memmove_avx_forward_nt_policy_proof.v'
original=Path('notes/x10-avx-forward-nt-policy/initial-attempt.v.txt').read_text()
current=Path(proof).read_text()
statements=lambda s: re.findall(r'(?ms)^(?:Theorem|Lemma|Corollary) .*?(?=^Proof\.)',s)
definitions=lambda s: re.findall(r'(?ms)^Definition .*?\.\n',s)
assert statements(original)==statements(current)
assert definitions(original)==definitions(current)
for s in statements(current): print('PRESERVED',s.split(':')[0])
for f in ['Examples/claude/memmove_avx_amd64.v',
          'Examples/claude/amd64_memmove_avx_overlap_forward_proof.v',
          'Examples/claude/amd64_memmove_avx_nt_proof.v',
          'Examples/claude/amd64_memmove_avx_nt_stores.v',
          'Examples/claude/amd64_memmove_avx_nt_witness.v']:
    assert Path(f).read_bytes()==subprocess.check_output(['git','show','3a3ad45b34c22a8b1e41ffd5807807c13dd3567a:'+f])
    print('UNCHANGED',f)
assert not subprocess.check_output(['git','diff','--name-only','3a3ad45b34c22a8b1e41ffd5807807c13dd3567a','--','notes/x10-avx-forward-nt-policy'])
print('Original Astra evidence unchanged; all statements and definitions retained.')
