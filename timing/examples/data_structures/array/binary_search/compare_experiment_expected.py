import sys
from pathlib import Path
sys.path.append(str(Path(__file__).resolve().parents[4]))

import argparse
import re
from examples.neorv32.NEORV32Config import NEORV32Config
from examples import *

PLOT_LEN = 1000
CALLING_CONVENTION_CYCLES = 13

# Closed forms of the NEORV32 instantiation in binary_search_proofs.v:
#   cycles = setup + k * body + exit, where k is the number of loop iterations.
def setup(il, dl):         return 6
def body(il, dl):          return 62 + 2 * il + dl
def found_exit(il, dl):    return 36 + 3 * il + dl
def notfound_exit(il, dl): return 10 + il

def size(n):  return n.bit_length()          # N.size n  = floor(log2 n) + 1
def log2(n):  return n.bit_length() - 1      # N.log2 n

# Iteration-count bounds proved by binary_search_timing:
#   found:     0 <= k < size(len)
#   not found: log2(len + 1) <= k <= size(len)
def found_bounds(length, cpu):
    lo = setup(cpu.min_inst_lat, cpu.min_data_lat) + found_exit(cpu.min_inst_lat, cpu.min_data_lat)
    il, dl = cpu.max_inst_lat, cpu.max_data_lat
    hi = setup(il, dl) + (size(length) - 1) * body(il, dl) + found_exit(il, dl)
    return lo, hi

def notfound_bounds(length, cpu):
    il, dl = cpu.min_inst_lat, cpu.min_data_lat
    lo = setup(il, dl) + log2(length + 1) * body(il, dl) + notfound_exit(il, dl)
    il, dl = cpu.max_inst_lat, cpu.max_data_lat
    hi = setup(il, dl) + size(length) * body(il, dl) + notfound_exit(il, dl)
    return lo, hi

def parse_cycle_counts(log_path):
    with open(log_path, 'r') as f:
        lines = f.readlines()

    cycle_counts, lengths, found = [], [], []
    for line in lines:
        match = re.match(r'Cycle count read: (\d+)', line.strip())
        if match:
            cycle_counts.append(int(match.group(1)))
        match = re.search(r'Len: (\d+)', line.strip())
        if match:
            lengths.append(int(match.group(1)))
            found.append(not re.search(r'not found', line))
    return cycle_counts, lengths, found


def main():
    parser = argparse.ArgumentParser(description='Compare experiment cycle counts with the verified binary search bounds.')
    parser.add_argument('log_file', nargs='?', default=None,
                        help='Path to the experiment log file (omit to plot only the verified bounds)')
    parser.add_argument('--cpu_config_file', help='Path to JSON file containing CPU configuration', default=None, type=str)

    args = parser.parse_args()

    cpu = NEORV32Config(args.cpu_config_file)

    xs = list(range(1, PLOT_LEN + 1))
    found_lo, found_hi = zip(*[found_bounds(n, cpu) for n in xs])
    nf_lo, nf_hi = zip(*[notfound_bounds(n, cpu) for n in xs])

    lines = []
    if args.log_file is not None:
        cycle_counts, lengths, found = parse_cycle_counts(args.log_file)
        found_points, notfound_points = [], []
        in_bounds = 0

        print(f"{'In Bounds':>9} | {'Len':>5} | {'Found':>5} | {'Measured':>8} | {'Expected Bounds':>15}")
        print("-" * 56)
        for measured, length, was_found in zip(cycle_counts, lengths, found):
            measured -= CALLING_CONVENTION_CYCLES
            lo, hi = (found_bounds if was_found else notfound_bounds)(length, cpu)
            in_bounds += lo <= measured <= hi
            (found_points if was_found else notfound_points).append((length, measured))
            print(f"{str(lo <= measured <= hi):9} | {length:5} | {str(was_found):>5} | {measured:8} | {lo:7} {hi:7}")
        print(f"{in_bounds}/{len(cycle_counts)} measurements within the verified bounds")

        lines = [('Measured (found)', found_points), ('Measured (not found)', notfound_points)]

    plot_comparison(
        "binary search",
        "Array Length",
        "Cycle Count",
        [
            ('Expected (found)', (0.53, 0.81, 0.92, 0.6), found_lo, found_hi),
            ('Expected (not found)', (0.6, 0.6, 0.6, 0.45), nf_lo, nf_hi),
        ],
        lines,
        range_xs=[xs, xs],
        loc='lower right',
        savepath="./binary_search_plot.png"
    )


if __name__ == '__main__':
    main()
