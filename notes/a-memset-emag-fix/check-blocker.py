#!/usr/bin/env python3
from pathlib import Path
s=Path('notes/a-memset-emag-fix/02-restored-build.log').read_text()
waits=sum(x.startswith('ADMISSION WAIT ') for x in s.splitlines())
print('Gate wait messages:',waits)
assert waits == 33
assert not any(x.startswith('ADMITTED ') for x in s.splitlines())
assert s.endswith('EXIT_CODE=130\n')
print('No compiler admitted; recorder exit 130 verified.')
print('Substring count also includes the traceback source line; count messages by line prefix.')
