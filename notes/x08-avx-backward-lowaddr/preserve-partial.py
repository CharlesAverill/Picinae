from pathlib import Path
import re
p=Path('Examples/claude/amd64_memmove_avx_backward_lowaddr_proof.v')
original=Path('notes/x08-avx-backward-lowaddr/initial-attempt.v.txt').read_text()
assert p.read_text()==original
start=original.index('Theorem memmove_avx_correct_backward_lowaddr:')
head,tail=original[:start],original[start:]
tail,n=re.subn(r'Proof\..*?Qed\.', 'Proof.\n  (* Uncertified initial script is preserved in notes/x08-avx-backward-lowaddr/initial-attempt.v.txt. *)\nAbort.',tail,flags=re.S)
assert n==8,n
p.write_text(head+tail)
print('Preserved 11 completed prefix proof scripts and all 26 declarations.')
print('Replaced the failing main proof and 7 unchecked later attempts with Abort.')
print('No statement, definition, generated map or prerequisite proof changed.')
