from pathlib import Path
import re
source = Path('Examples/FreeRTOSMask/armv6m_port_mask_proof.v').read_text()
facts = re.findall(r'^(?:Theorem|Lemma) (\w+)', source, re.M)
raw = Path('notes/r42-port-mask-fix/assumptions.log').read_text()
assert raw.endswith('EXIT_CODE=0\n')
positions = [(name, re.search(r'^' + name + r'\n', raw, re.M)) for name in facts]
assert all(m for _, m in positions)
closed = fe = 0
for i, (name, match) in enumerate(positions):
    end = positions[i+1][1].start() if i+1 < len(positions) else len(raw)
    block = raw[match.end():end]
    if 'Closed under the global context' in block:
        assert 'Axioms:' not in block
        print(name + ': closed')
        closed += 1
    else:
        assert 'Axioms:' in block
        assumptions = re.findall(r'^([\w.]+)\s*:', block.split('Axioms:', 1)[1], re.M)
        assert assumptions == ['FunctionalExtensionality.functional_extensionality_dep'], (name, assumptions)
        print(name + ': inherited functional_extensionality_dep only')
        fe += 1
print(f'PASS: {len(facts)} transitive queries; {closed} closed, {fe} FE-only; no imported admission.')
