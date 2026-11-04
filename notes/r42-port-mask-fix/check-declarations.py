from pathlib import Path
import re
initial = Path('notes/r42-port-mask/initial-attempt.v.txt').read_text()
final = Path('Examples/FreeRTOSMask/armv6m_port_mask_proof.v').read_text()
def declarations(text):
    text = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
    text = re.sub(r'Proof\..*?(?:Qed|Abort)\.', '', text, flags=re.S)
    parts = re.split(r'(?m)^(?=(?:Definition|Theorem|Lemma)\s)', text)[1:]
    return {re.match(r'(?:Definition|Theorem|Lemma)\s+(\w+)', part)[1]: ' '.join(part.split()) for part in parts}
old, new = declarations(initial), declarations(final)
for name, statement in old.items():
    assert name in new, f'missing original declaration: {name}'
    assert statement == new[name], f'changed statement/definition: {name}'
    print('RETAINED', name)
assert not re.search(r'\b(?:Abort|Admitted|admit|Axiom|Parameter)\b', re.sub(r'\(\*.*?\*\)', '', final, flags=re.S))
print(f'PASS: all {len(old)} original declarations retained; no unfinished declarations.')
