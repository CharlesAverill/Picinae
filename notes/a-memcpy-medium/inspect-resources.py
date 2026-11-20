from pathlib import Path
root=Path.cwd()
for p in Path('/proc').iterdir():
    if not p.name.isdigit(): continue
    try:
        if not (p/'cwd').resolve().is_relative_to(root): continue
        cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode()
        exe=Path(cmd.split(' ',1)[0]).name
        if exe not in ('dune','rocq','rocqworker','rocqworker.opt','coqc'): continue
        print('PID',p.name,'COMMAND',cmd)
        for row in (p/'status').read_text().splitlines():
            if row.startswith(('VmPeak:', 'VmSize:', 'VmRSS:')): print(row)
        for row in (p/'limits').read_text().splitlines():
            if row.startswith(('Max stack size','Max address space')): print(row)
    except (FileNotFoundError, PermissionError, ProcessLookupError): pass
