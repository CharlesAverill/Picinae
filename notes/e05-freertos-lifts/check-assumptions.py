#!/usr/bin/env python3
"""Query every generated fact, in one capped sequential Rocq process.

Run inside the read-only Picinae environment with the unit no-pip Python.
The build and compiler commands and their real exits appear in the log.
"""
import os
from pathlib import Path
import re
import resource
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
os.chdir(root)
cap = int(os.environ.get('PROOF_MEMORY_KB', '2000000'))
assert cap <= 2000000
resource.setrlimit(resource.RLIMIT_AS, (cap * 1024, cap * 1024))
resource.setrlimit(resource.RLIMIT_STACK, (65536 * 1024, 65536 * 1024))


def run(command):
    print('COMMAND:', repr(command), flush=True)
    proc = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(proc.stdout, end='', flush=True)
    print('EXIT_CODE:', proc.returncode, flush=True)
    assert proc.returncode == 0
    return proc.stdout


run(['dune', 'build', '--cache=disabled', '-j1', '--display', 'short', '@Examples/FreeRTOS/freertos-lifts'])
query = []
count = 0
for path in sorted((root / 'Examples/FreeRTOS').glob('*_armv6m.v')):
    module = 'Picinae.Examples.FreeRTOS.' + path.stem
    query.append(f'Require Import {module}.')
    for theorem in re.findall(r'^(?:Theorem|Example) (\w+)\s*:', path.read_text(), re.M):
        query += [f'Check {module}.{theorem}.', f'Print Assumptions {module}.{theorem}.']
        count += 1
for theorem in ('welltyped_lift_armv6m', 'welltyped_armv6mprog', 'welltyped_arm2il'):
    query += [f'Check Picinae_armv6m.{theorem}.', f'Print Assumptions Picinae_armv6m.{theorem}.']
    count += 1
text = '\n'.join(query) + '\n'
(root / 'notes/e05-freertos-lifts/assumptions-query.v.txt').write_text(text)
with tempfile.TemporaryDirectory(prefix='e05-assumptions-', dir=root / '_build') as temporary:
    path = Path(temporary) / 'Assumptions.v'
    path.write_text(text)
    output = run(['rocq', 'compile', '-q', '-R', '_build/default', 'Picinae', str(path)])
    assert output.count('Closed under the global context') == count
    assert 'Axioms:' not in output
print(f'PASS: Print Assumptions for all {count} generated/imported facts is closed under the global context')
