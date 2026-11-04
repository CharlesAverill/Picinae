from pathlib import Path
import re
log=Path('notes/a-memcpy-medium/initial-build.log').read_text()
out=Path('notes/a-memcpy-medium/initial-compiler-output.txt').read_text()
assert log.endswith('EXIT_CODE=1\n')
assert 'Fatal error: out of memory' in out
assert out.count('Axioms:') == 15
assert out.count('Closed under the global context') == 4
assert out.count('Goal at') == 15
assert not Path('_build/default/Examples/claude/arm8_memcpy_medium_proof.vo').exists()
s=Path('Examples/claude/arm8_memcpy_medium_proof.v').read_text()
assert len(re.findall(r'\bQed\.',s))==19
assert len(re.findall(r'^Abort\.',s,re.M))==85
assert not re.search(r'\b(?:Admitted|admit|Axiom|Parameter)\b',s)
print('PARTIAL: single build exit 1, out-of-memory, no unit vo.')
print('19 prefix Qeds observed: five initial facts and fourteen cases (33..46).')
print('85 unchanged statements aborted: cases 47..128 plus three main theorems.')
print('Four closed prefix queries; fifteen inherited-FE-only prefix queries.')
print('No new admission/axiom/parameter; no post-handoff compiler run.')
