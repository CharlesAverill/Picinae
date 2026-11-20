"""Check saved raw kernel query output; never manufacture assumptions evidence."""
from pathlib import Path
import re

names = '''timeout_nwc timeout_welltyped timeout_zero_bound timeout_witness_models
 timeout_entry_satisfiable timeout_ranges_separate timeout_separation_nonvacuous
 timeout_original_memory timeout_original_fields timeout_original_bytes
 timeout_memory_frame timeout_correct timeout_post_at_bx
 timeout_preserves_callee_saved timeout_return_step timeout_caller_result'''.split()
log = Path('notes/r14-timeout-internal-fix/assumptions.log').read_text()
assert log.rstrip().endswith('EXIT_CODE=0')
assert 'RELEASED r14-timeout-internal-fix exit=0' in log
matches = list(re.finditer(r'^(' + '|'.join(names) + r')\n', log, re.M))
assert [m[1] for m in matches] == names
closed = []
fe = []
for i, match in enumerate(matches):
    end = matches[i+1].start() if i+1 < len(matches) else log.index('RELEASED', match.end())
    chunk = log[match.end():end]
    if 'Closed under the global context' in chunk:
        assert 'Axioms:' not in chunk
        closed.append(match[1])
    else:
        raw = chunk.split('Axioms:\n', 1)[1].strip()
        expected = '''FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g'''
        assert raw == expected, raw
        fe.append(match[1])
assert closed == names[:11]
assert fe == names[11:]
print('PASS: 16 successful raw Check / Print Assumptions queries')
print('Closed under the global context (' + str(len(closed)) + '): ' + ', '.join(closed))
print('Inherited Stdlib FunctionalExtensionality.functional_extensionality_dep ONLY (' + str(len(fe)) + '): ' + ', '.join(fe))
print('No imported admitted theorem or other axiom in any transitive assumption set.')
source = Path('Examples/FreeRTOS/armv6m_vTaskInternalSetTimeOutState_proof.v').read_text()
source = re.sub(r'\(\*.*?\*\)', '', source, flags=re.S)
assert not re.search(r'\b(?:Abort|admit|Admitted|Axioms?|Parameters?)\b', source)
assert len(re.findall(r'\bQed\.', source)) == 16
print('PASS: 16 completed Qed proofs; no active Abort/admission/axiom/parameter')
