from pathlib import Path
import re
notes = Path(__file__).parent
initial = (notes/'initial-attempt.v.txt').read_text()
cut = initial.index('Lemma ofw_dispatch:')
prefix, suffix = initial[:cut], initial[cut:]
# No proof repairs: preserve every statement, discard unchecked proof bodies
# from the active source, and keep their verbatim original in the frozen text.
suffix, count = re.subn(r'\bProof\..*?(?:Time\s+)?Qed\.',
    'Abort. (* PARTIAL: exact initial proof is in notes/x03-avx-overlap-forward/initial-attempt.v.txt. *)',
    suffix, flags=re.S)
assert count == 7, count
result = prefix + suffix
# Check all declaration text outside proof bodies is preserved exactly.
def statement_text(text):
    text = re.sub(r'\bProof\..*?(?:Time\s+)?Qed\.', '<PROOF>', text, flags=re.S)
    return re.sub(r'Abort\. \(\* PARTIAL: exact initial proof is in notes/x03-avx-overlap-forward/initial-attempt.v.txt\. \*\)', '<PROOF>', text)
assert statement_text(initial) == statement_text(result)
Path('Examples/claude/amd64_memmove_avx_overlap_forward_proof.v').write_text(result)
print('Preserved all statements exactly; retained earlier Qed blocks; aborted 7 unchecked declarations.')
