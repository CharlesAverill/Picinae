from pathlib import Path
import re
raw = Path('notes/x02-avx-nt-fix/16-assumptions.log').read_text()
assert raw.endswith('EXIT_CODE=0\n')
fe = '''Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g'''
closed = 'Closed under the global context'
expected = {
    'memmove_avx_correct_nt': fe, 'nt_seg_1285': fe,
    'nt_adv4': closed, 'nt_adv2': closed, 'cpy_store8': closed,
    **{f'nt_seg_{n}': fe for n in (1117,1125,1210,1613,1621,1706)},
    'nt_entry_inputs_satisfiable': closed, 'nt_zero_memory_load': closed,
    'cpy_store16': closed, 'cpy_store16_inputs_satisfiable': closed,
    'memmove_avx_welltyped': fe, 'memmove_avx_nwc': closed,
    'memmove_avx_preserves_callee_saved': closed,
}
starts = [re.search('^'+name+'$', raw, re.M) for name in expected]
assert all(starts)
for i, ((name, assumptions), start) in enumerate(zip(expected.items(), starts)):
    end = starts[i+1].start() if i+1 < len(starts) else raw.index('\nEXIT_CODE=')
    block = raw[start.end():end]
    found = re.search(r'^(Axioms:|Closed under the global context)', block, re.M)
    assert found, name
    actual = block[found.start():].strip()
    assert actual == assumptions, (name,actual)
    print(name+':\n'+actual+'\n')
print('All 18 exact transitive assumption sets match; no admitted dependency.')
