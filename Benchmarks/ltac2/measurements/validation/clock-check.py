"""Supplementary sleep calibration; never part of compiler comparisons.

Run only after the benchmark harness exits, through picinae-env python3.
All child commands also enter the same wrapper. GNU time's wall clock is
compared with Python's realtime, monotonic, and monotonic-raw clocks.
"""
import json
import os
from pathlib import Path
import shlex
import subprocess
import time

directory = Path(__file__).resolve().parent
wrapper = '/home/charles/code/friends/.toolchains/picinae-env'

def clocks():
    return {'realtime': time.time_ns(), 'monotonic': time.monotonic_ns(),
            'monotonic_raw': time.clock_gettime_ns(time.CLOCK_MONOTONIC_RAW)}

records = []
for seconds in [1, 10, 30]:
    timer = directory / f'clock-sleep-{seconds}.time.json'
    command = [wrapper, '/usr/bin/time', '-o', str(timer), '-f',
               '{"wall":%e,"user":%U,"sys":%S,"rss_kb":%M,"exit_code":%x}',
               'python3', '-c', f'import time; time.sleep({seconds})']
    before_load = os.getloadavg()
    before = clocks()
    result = subprocess.run(command, capture_output=True, text=True)
    after = clocks()
    timing = json.loads(timer.read_text().splitlines()[-1])
    record = {'sleep_seconds': seconds, 'command': command,
              'shell_command': shlex.join(command), 'exit_code': result.returncode,
              'stdout': result.stdout, 'stderr': result.stderr,
              'before': before, 'after': after, 'gnu_time': timing,
              'elapsed': {k: (after[k] - before[k]) / 1e9 for k in before},
              'load_before': before_load, 'load_after': os.getloadavg()}
    records.append(record)
    (directory / 'clock-check.json').write_text(json.dumps(records, indent=2) + '\n')
    print(json.dumps(record), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
