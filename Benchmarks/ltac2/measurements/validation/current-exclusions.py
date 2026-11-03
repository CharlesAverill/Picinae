"""Optional sequential current-library checks of baseline-failing examples."""
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import time

directory = Path(__file__).resolve().parent
root = Path('/home/charles/.t3/worktrees/Picinae/t3-68d408bf')
scratch = Path('/tmp/picinae-ltac-final-602efc7-20261103')
wrapper = '/home/charles/code/friends/.toolchains/picinae-env'
records = []
for stem in ['riscv_addloop_proof', 'riscv_cfi']:
    source = scratch / 'ltac2' / (stem + '.v')
    assert source.read_bytes() == (root / 'Examples' / source.name).read_bytes()
    log = directory / (stem + '-current.log')
    timer = directory / (stem + '-current.time.json')
    command = [wrapper, '/usr/bin/time', '-o', str(timer), '-f',
               '{"wall":%e,"user":%U,"sys":%S,"rss_kb":%M,"exit_code":%x}',
               'rocq', 'compile', '-R', str(root), 'Picinae',
               '-Q', str(source.parent), '', str(source)]
    before_load = os.getloadavg()
    start = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=source.parent, stdout=stream, stderr=subprocess.STDOUT)
    record = dict(example=stem, command=command, shell_command=shlex.join(command),
                  cwd=str(source.parent), exit_code=result.returncode,
                  outer_seconds=time.monotonic()-start,
                  load_before=before_load, load_after=os.getloadavg(),
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  log=str(log), timing_log=str(timer),
                  gnu_time=json.loads(timer.read_text().splitlines()[-1]))
    records.append(record)
    (directory / 'current-exclusions.json').write_text(json.dumps(records, indent=2) + '\n')
    print(json.dumps(record), flush=True)
    assert result.returncode == 1, 'Unexpected change in baseline-failing example outcome'
