"""Mechanical failure handoff, not a proof repair or a compiler invocation."""
from pathlib import Path
import re
unit = Path('notes/x07-avx-rep-overlap')
source = Path('Examples/claude/amd64_memmove_avx_rep_overlap_proof.v')
original = (unit / 'initial-attempt.v.txt').read_text()
assert source.read_text() == original, 'Initial source changed after snapshot'
pattern = r'Proof\.[\s\S]*?(?:Time )?Qed\.'
partial, count = re.subn(pattern, 'Proof. Abort.', original)
assert count == 9, count
source.write_text('(* PARTIAL: initial full-target build failed. All nine proof attempts\n'
                  '   are archived verbatim in notes/x07-avx-rep-overlap/initial-attempt.v.txt.\n'
                  '   Statements below are retained with Abort, not exported as theorems.\n'
                  '   No post-failure Astra repair or second compiler run was performed. *)\n'
                  + partial)
def statements(text):
    return re.findall(r'(?m)^(?:Lemma|Theorem|Corollary)\s+[\s\S]*?(?=\nProof\.)', text)
assert statements(original) == statements(partial)
print(f'Preserved {count} exact statements; all proof bodies replaced by Abort.')
for statement in statements(original):
    print(statement.splitlines()[0])
