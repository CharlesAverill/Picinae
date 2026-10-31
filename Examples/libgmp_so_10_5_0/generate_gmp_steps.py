#!/usr/bin/env python3
"""Regenerate the GMP proof steps using the checked compiler backend.

Run after building the Picinae libraries. An optional argument selects a
single lift: copyi, add_nc, sub_nc, or add_n_sub_n.
"""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
LIFTS = Path(__file__).resolve().parent
NC = [0x1284e0, 0x128500, 0x128517, 0x12851e, 0x128521, 0x128524,
      0x128527, 0x12852f, 0x128532, 0x128536, 0x12853d,
      0x128540, 0x128544, 0x128547, 0x12854b, 0x12854f, 0x12855a,
      0x128560, 0x128563, 0x128567, 0x12856b, 0x12856f,
      0x128594, 0x12859e, 0x1285a2, 0x1285a5, 0x1285a9, 0x1285ad,
      0x1285b1, 0x1285ca, 0x1285d2]
RET = [0x128526, 0x12853f, 0x12855d, 0x1285d4]
CONFIG = {
    'copyi': ([0x15b186, 0x15b190, 0x15b1bc, 0x15b1cf], [0x15b1e2], []),
    'add_nc': (NC, RET, ['R_OF', 'R_SF', 'R_PF', 'R_AF']),
    'sub_nc': ([a+0x260 for a in NC], [a+0x260 for a in RET], ['R_OF', 'R_SF', 'R_PF', 'R_AF']),
    'add_n_sub_n': ([0x15c360, 0x15c448, 0x15c508, 0x15c3b8, 0x15c480,
                     0x15c538, 0x15c3ef, 0x15c420, 0x15c4b7, 0x15c4e8,
                     0x15c568, 0x15c597, 0x15c5b1, 0x15c432],
                    [0x15c443, 0x10c030, 0x10b8f0, 0x10bbe0], ['R_PF', 'R_AF']),
}

def main():
    names = sys.argv[1:] or list(CONFIG)
    if any(name not in CONFIG for name in names):
        raise SystemExit('choose from: ' + ', '.join(CONFIG))
    for name in names:
        points, exits, ignored = CONFIG[name]
        generator = ROOT / 'tools' / 'bigsteps'
        if not generator.is_file():
            generator = ROOT / 'bigsteps'
        command = [str(generator),
                   str(LIFTS / f'gmpn_{name}_amd64.v'),
                   '--backend', 'compiler', '--timeout', '600',
                   '--invariants', *map(hex, points+exits), '--exits', *map(hex, exits)]
        if ignored:
            command += ['--ignore', *ignored]
        subprocess.run(command, cwd=ROOT, check=True)

if __name__ == '__main__':
    main()
