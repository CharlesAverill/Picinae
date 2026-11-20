from pathlib import Path
import os
import signal
for p in Path('/proc').iterdir():
    if not p.name.isdigit():
        continue
    try:
        if (p/'comm').read_text().strip() != 'rocqworker':
            continue
        if (p/'cwd').resolve() != Path.cwd()/'_build/default':
            continue
        if b'Examples/claude/amd64_memmove_avx_nt_witness.v' not in (p/'cmdline').read_bytes():
            continue
        os.kill(int(p.name), signal.SIGINT)
        print('Sent SIGINT only to this unit witness compiler PID', p.name)
    except (PermissionError, FileNotFoundError, ProcessLookupError):
        pass
