"""Negative controls for declaration extraction; no Rocq compilation."""
from pathlib import Path
import runpy

ns = runpy.run_path('notes/a-ffsl-fix/check-statement-preservation.py')
parse = ns['declarations']
source = Path('notes/a-ffsl/initial-attempt.v.txt').read_text()
original = parse(source)
assert parse(source.replace('Qed.', 'Abort.')) == original
assert parse(source.replace('r <= 64', 'r <= 63'))['ffsl_spec'] != original['ffsl_spec']
assert parse(source.replace('(MDL: models arm8typctx s)', '(MDL: True)'))['ffsl_correct'] != original['ffsl_correct']
assert 'ffsl_correct' not in parse(source.replace('Theorem ffsl_correct:', 'Theorem renamed_correct:'))
assert parse(source + '\nLemma new_support: True. Proof. exact I. Qed.\n')['ffsl_correct'] == original['ffsl_correct']
print('Negative controls detect changed spec, changed entry requirement, and removed theorem.')
print('Proof terminators and additional helpers do not hide or change author declarations.')
