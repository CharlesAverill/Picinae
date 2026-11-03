from pathlib import Path
root = Path.cwd()
for p in Path('/proc').iterdir():
    if not p.name.isdigit(): continue
    try:
        comm = (p/'comm').read_text().strip()
        if comm not in ('dune', 'rocq', 'rocqworker', 'coqc'): continue
        cwd = (p/'cwd').resolve()
        if cwd not in (root, root/'_build/default'): continue
        cmd = (p/'cmdline').read_bytes().replace(b'\0', b' ').decode()
        print('PID', p.name, 'CWD', cwd, 'CMD', cmd)
        print('\n'.join(x for x in (p/'status').read_text().splitlines() if x.startswith(('VmPeak:', 'VmSize:', 'VmRSS:', 'State:'))))
        print('\n'.join(x for x in (p/'limits').read_text().splitlines() if 'stack size' in x or 'address space' in x))
    except (PermissionError, FileNotFoundError, ProcessLookupError): pass
