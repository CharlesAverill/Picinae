"""Sequential capped queries for every exported unit proof and inherited frame."""
import re
import subprocess
from pathlib import Path
root = Path('notes/x01-sse2-nt-complete')
modules = ['amd64_memcpy_nt_proof', 'amd64_memcpy_nt_dispatch_proof',
           'amd64_memcpy_nt_head_proof', 'amd64_memcpy_nt_domain_proof',
           'amd64_memcpy_nt_bulk_proof', 'amd64_memcpy_nt_bulk4_proof',
           'amd64_memcpy_nt_strategy_proof']
for name in modules + ['amd64_memcpy_proof']:
    source = Path('Examples/claude') / (name + '.v')
    names = re.findall(r'(?m)^(?:Lemma|Theorem)\s+(\w+)\s*:', source.read_text())
    if name == 'amd64_memcpy_proof':
        names = ['memcpy_welltyped', 'memcpy_nwc', 'memcpy_preserves_callee_saved']
    log = root / ('assumptions-' + name + '.log')
    args = ['bash', 'tools/record-command.sh', str(log),
            '/home/charles/code/friends/.toolchains/arm-validation/picinae-env',
            'env', 'PROOF_MEMORY_KB=8000000', 'PROOF_STACK_KB=65536',
            'bash', 'tools/print-assumptions.sh',
            'Picinae.Examples.claude.' + name, *names]
    result = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    print(name, 'constants=' + str(len(names)), 'exit=' + str(result.returncode), 'log=' + str(log), flush=True)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    text = log.read_text()
    assert 'Admitted' not in text
    forbidden = re.findall(r'(?m)^([\w.]+)\s*:', text[text.find('Axioms:'):])
    # Raw outputs are authoritative; manual review follows these queries.
print('All sequential queries completed; inspect every raw Axioms block.')
