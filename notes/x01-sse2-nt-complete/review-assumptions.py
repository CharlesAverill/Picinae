import re
from pathlib import Path
allowed = {'FunctionalExtensionality.functional_extensionality_dep'}
total_closed = total_fe = 0
for path in sorted(Path('notes/x01-sse2-nt-complete').glob('assumptions-*.log')):
    text = path.read_text()
    assert text.endswith('EXIT_CODE=0\n'), path
    in_axioms = False
    names = set()
    for line in text.splitlines():
        if line == 'Axioms:':
            in_axioms = True
            continue
        if in_axioms and line and not line[0].isspace():
            match = re.match(r"^([A-Za-z_][A-Za-z_0-9.']*)\s*:", line)
            if match:
                names.add(match[1])
            else:
                in_axioms = False
    assert names <= allowed, (path, names)
    closed = text.count('Closed under the global context')
    fe = text.count('\nAxioms:\n')
    assert text.count('FunctionalExtensionality.functional_extensionality_dep :') == fe
    total_closed += closed
    total_fe += fe
    print(path.name, 'closed=', closed, 'FE_only=', fe, 'axiom_names=', sorted(names))
print('TOTAL', total_closed + total_fe, 'CLOSED', total_closed, 'FE_ONLY', total_fe)
assert total_closed + total_fe == 68
