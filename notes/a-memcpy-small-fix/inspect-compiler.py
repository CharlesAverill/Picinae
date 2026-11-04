import os
from pathlib import Path
root = str(Path.cwd())
found = 0
for proc in Path('/proc').iterdir():
    if not proc.name.isdigit():
        continue
    try:
        args = (proc / 'cmdline').read_bytes().split(b'\0')
        if not args[0].endswith(b'/rocqworker'):
            continue
        if os.readlink(proc / 'cwd') != root + '/_build/default':
            continue
        if b'Examples/claude/arm8_memcpy_small_proof.v' not in args:
            continue
        found += 1
        print('Unit compiler PID:', proc.name)
        limits = (proc / 'limits').read_text()
        for line in limits.splitlines():
            if line.startswith('Max address space'):
                assert line.split()[-3:] == ['2048000000', '2048000000', 'bytes'], line
                print(line)
            if line.startswith('Max stack size'):
                assert line.split()[-3:] == ['67108864', '67108864', 'bytes'], line
                print(line)
        for line in (proc / 'status').read_text().splitlines():
            if line.startswith(('VmPeak:', 'VmSize:', 'VmHWM:', 'VmRSS:')):
                print(line)
    except (FileNotFoundError, PermissionError, ProcessLookupError):
        continue
assert found == 1, found
print('PASS: exactly one unit compiler, assigned hard/soft memory and stack caps.')
