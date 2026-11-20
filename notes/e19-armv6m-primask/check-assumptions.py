#!/usr/bin/env python3
"""Raw assumptions for all e19 examples, generated facts, and changed typing."""
import os
from pathlib import Path
import re
import resource
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
os.chdir(root)
cap = int(os.environ.get('PROOF_MEMORY_KB','2000000'))
assert 0 < cap <= 2000000
resource.setrlimit(resource.RLIMIT_AS,(cap*1024,cap*1024))
resource.setrlimit(resource.RLIMIT_STACK,(65536*1024,65536*1024))
query = ['Require Import Picinae_armv6m.']
count = 0
paths = [root/'tests/armv6m_primask/fixture.v', root/'tests/armv6m_primask/Checks.v',
         *sorted((root/'Examples/FreeRTOSMask').glob('*.v'))]
for path in paths:
    module = 'Picinae.' + '.'.join(path.relative_to(root).with_suffix('').parts)
    query.append(f'Require Import {module}.')
    for name in re.findall(r'^(?:Theorem|Lemma|Example) (\w+)\s*:',path.read_text(),re.M):
        query += [f'Check {module}.{name}.', f'Print Assumptions {module}.{name}.']
        count += 1
for name in ('welltyped_arm2il','welltyped_lift_armv6m','welltyped_armv6mprog','welltyped_lift_armv6m_mask'):
    query += [f'Check {name}.',f'Print Assumptions {name}.']
    count += 1
text = '\n'.join(query)+'\n'
(root/'notes/e19-armv6m-primask/assumptions-query.v.txt').write_text(text)
with tempfile.TemporaryDirectory(dir=root/'_build',prefix='e19-assumptions-') as tmp:
    path = Path(tmp)/'Assumptions.v'
    path.write_text(text)
    cmd = ['rocq','compile','-q','-R','_build/default','Picinae',str(path)]
    print('COMMAND:',repr(cmd),flush=True)
    proc = subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print(proc.stdout,end='',flush=True)
    print('EXIT_CODE:',proc.returncode,flush=True)
    assert proc.returncode == 0
    assert proc.stdout.count('Closed under the global context') == count
    assert 'Axioms:' not in proc.stdout
print(f'PASS: all {count} facts closed under the global context')
