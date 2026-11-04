#!/usr/bin/env python3
"""Read the mandatory admission state; optionally stop ONLY this unit's waiter."""
import argparse
import fcntl
import json
import os
from pathlib import Path
import signal
import time

p=argparse.ArgumentParser()
p.add_argument('--cancel-waiter',action='store_true')
a=p.parse_args()
root=Path('/home/charles/code/friends/.refs/picinae-llm-proofs/resources')
unit='a-strcmp-complete'
with (root/'admission.lock').open('r') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX)
    cfg=json.loads((root/'config.json').read_text())
    entries=json.loads((root/'active.json').read_text())
    mem={k.rstrip(':'):int(v.split()[0]) for k,v in (x.split(None,1) for x in Path('/proc/meminfo').read_text().splitlines())}
    reserve=max(cfg['available_floor_kib'],int(mem['MemTotal']*.20)+cfg['other_jobs_working_set_kib']+cfg['burst_reserve_kib'])
    reserved=sum(x['memory_kib'] for x in entries)+cfg['legacy_reserved_kib']
    print('UTC:',time.strftime('%Y-%m-%d %H:%M:%S',time.gmtime()))
    print('MemAvailable_KiB:',mem['MemAvailable'])
    print('Active_reservations_KiB:',reserved)
    print('Required_floor_KiB:',reserve)
    print('Requested_unit_KiB:',4000000)
    print('Headroom_shortfall_KiB:',max(0,reserve+reserved+4000000-mem['MemAvailable']))
    log=Path('notes/a-strcmp-complete/08-mask-probe.log').read_text()
    count=log.count('ADMISSION WAIT')
    print('Admission_wait_messages:',count)
    print('Conservative_wait_lower_bound_seconds:',max(0,count-1)*20)
    candidates=[]
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit(): continue
        try:
            cmd=proc.joinpath('cmdline').read_bytes().split(b'\0')
            expected=[str(root/'resource-run.py').encode(),b'--unit',unit.encode(),b'--memory-kib',b'4000000']
            if cmd[1:6]!=expected: continue
            if proc.joinpath('cwd').resolve()!=Path.cwd(): continue
            pid=int(proc.name)
            stat=proc.joinpath('stat').read_text().rsplit(')',1)[1].split()
            elapsed=float(Path('/proc/uptime').read_text().split()[0])-int(stat[19])/os.sysconf('SC_CLK_TCK')
            print('Own_gate_PID:',pid,'elapsed_seconds:',round(elapsed,2))
            candidates.append(pid)
        except (OSError,ValueError): continue
    if a.cancel_waiter:
        assert len(candidates)==1, candidates
        pid=candidates[0]
        assert not any(x['pid']==pid for x in entries), 'Gate already admitted: leave running'
        assert not any(x['unit']==unit for x in entries), 'Own compiler active: leave running'
        os.kill(pid,signal.SIGTERM)
        print('Stopped only own unadmitted waiter:',pid)
