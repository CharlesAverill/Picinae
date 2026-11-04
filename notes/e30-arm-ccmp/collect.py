#!/usr/bin/env python3
"""Fresh pinned Ghidra raw-pcode evidence; no lifting or publication bypass."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

p = argparse.ArgumentParser()
p.add_argument('--run', required=True)
a = p.parse_args()
assert a.run.replace('-', '').isalnum()
repo = Path(__file__).resolve().parents[2]
deps = Path('/home/charles/code/friends/.toolchains/e02-arm-inventory')
state = Path('/home/charles/code/friends/.toolchains/e30-arm-ccmp') / a.run
state.mkdir(parents=True, exist_ok=False)
for part in ('config', 'cache', 'tmp', 'projects'):
    (state / part).mkdir()
java = deps / 'jdk-21.0.8+9'
env = {**os.environ, 'JAVA_HOME': str(java),
       'GHIDRA_INSTALL_DIR': str(deps / 'ghidra_11.4.2_PUBLIC'),
       'XDG_CONFIG_HOME': str(state / 'config'), 'XDG_CACHE_HOME': str(state / 'cache'),
       'TMPDIR': str(state / 'tmp'), 'PYTHONDONTWRITEBYTECODE': '1',
       'JAVA_TOOL_OPTIONS': f'-Xmx1G -Duser.home={state} -Djava.io.tmpdir={state / "tmp"}'}
for name in ('PYTHONPATH', 'PYTHONHOME', '_JAVA_OPTIONS', 'JDK_JAVA_OPTIONS'):
    env.pop(name, None)
cmd = [str(deps / 'venv/bin/python'), '-m', 'pyghidra', '--skip-analysis',
       '--project-path', str(state / 'projects'), '--project-name', 'e30',
       str(deps / 'root/lib/aarch64-linux-gnu/libc.so.6'),
       str(repo / 'notes/e30-arm-ccmp/collect_headless.py'), str(repo), str(state)]
print('COMMAND=' + json.dumps(cmd), flush=True)
with (state / 'ghidra.log').open('w') as f:
    r = subprocess.run(cmd, env=env, stdout=f, stderr=subprocess.STDOUT)
app = state / 'config/ghidra/ghidra_11.4.2_PUBLIC/application.log'
if app.exists():
    with (state / 'ghidra.log').open('a') as f:
        f.write(app.read_text())
print('LAUNCHER_EXIT=' + str(r.returncode))
assert r.returncode == 0 and (state / 'raw.json').is_file(), (state / 'ghidra.log').read_text()
print('PASS', state / 'raw.json')
