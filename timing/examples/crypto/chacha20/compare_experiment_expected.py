import sys
from pathlib import Path
sys.path.append(str(Path(__file__).resolve().parents[3]))

import argparse
import re
from sympy import Piecewise, Eq
from examples.neorv32.NEORV32Config import NEORV32Config
from examples import *

PLOT_LEN = 100
CALLING_CONVENTION_CYCLES = 17

def parse_cycle_counts(log_path):
    with open(log_path, 'r') as f:
        lines = f.readlines()

    cycle_counts = []
    for line in lines:
        match = re.match(r'Cycle count read: (\d+)', line.strip())
        if match:
            cycle_counts.append(int(match.group(1)))
    return cycle_counts


def main():
    parser = argparse.ArgumentParser(description='Compare experiment cycle counts with an expected equation.')
    parser.add_argument('log_file', help='Path to the experiment log file')
    parser.add_argument('equation_file', help='Path to the file containing the verified timing equation')
    parser.add_argument('--cpu_config_file', help='Path to JSON file containing CPU configuration', default=None, type=str)

    args = parser.parse_args()

    cpu = NEORV32Config(args.cpu_config_file)

    cycle_counts = parse_cycle_counts(args.log_file)
    equation = compile_equation(args.equation_file, cpu, [])

    pct_off = []
    # measured_vals = [m - CALLING_CONVENTION_CYCLES for m in cycle_counts]

    print(f"{'In Bounds':>9} | {'Measured':>8} | {'Expected Bounds':>15} | {'Diffs':>9} | {'Diffs/Measured':>14}")
    print("-" * 89)

    for i, measured in enumerate(cycle_counts):
        measured -= CALLING_CONVENTION_CYCLES

        # Compute expected bounds
        min_expected = equation([], "min")
        max_expected = equation([], "max")

        # Compute percent error
        min_diff = abs(measured - min_expected)
        max_diff = abs(measured - max_expected)
        pct_off.append((min_diff / measured, max_diff / measured))

        print(f"{str(min_expected <= measured <= max_expected):9} | \
{measured:8} | \
{min_expected:7} {max_expected:7} | \
{min_diff:4} {max_diff:4} | \
{round(pct_off[-1][0], 4)} {round(pct_off[-1][1], 4)}")

    # Summary statistics
    print(f"Avg min percent off: {100.0 * sum(i[0] for i in pct_off) / len(cycle_counts):.4}%")
    print(f"Avg max percent off: {100.0 * sum(i[1] for i in pct_off) / len(cycle_counts):.4}%")
    print(f"Variance percent off: {variance(pct_off)}%")
    

if __name__ == '__main__':
    main()

