import sys
from pathlib import Path
sys.path.append(str(Path(__file__).resolve().parents[5]))

import argparse
import re
from sympy import symbols
from examples.neorv32.NEORV32Config import NEORV32Config
from examples import *

PLOT_LEN = 100
CALLING_CONVENTION_CYCLES = 13

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
    parser = argparse.ArgumentParser(description='Compare experiment cycle counts with min/max expected bounds.')
    parser.add_argument('log_file', help='Path to the experiment log file')
    parser.add_argument('min_equation_file', help='Path to the file containing the verified timing minimum equation')
    parser.add_argument('max_equation_file', help='Path to the file containing the verified timing maximum equation')
    parser.add_argument('--cpu_config_file', help='Path to JSON file containing CPU configuration', default=None, type=str)

    args = parser.parse_args()

    cpu = NEORV32Config(args.cpu_config_file)
    cycle_counts = parse_cycle_counts(args.log_file)

    min_eq = compile_equation(args.min_equation_file, cpu, ["length"])
    max_eq = compile_equation(args.max_equation_file, cpu, ["length"])

    pct_off_min = []
    pct_off_max = []
    measured_vals = [m - CALLING_CONVENTION_CYCLES for m in cycle_counts]
    min_expected_vals = []
    max_expected_vals = []

    print(f"{'In Bounds':>9} | {'Len':>5} | {'Measured':>8} | {'Expected Bounds':>15} | {'Diffs':>9} | {'Diffs/Measured':>14}")
    print("-" * 89)

    for i, measured in enumerate(measured_vals):
        len_value = i + 1

        expected_min = min_eq([len_value], 'min')
        expected_max = max_eq([len_value], 'max')

        min_expected_vals.append(expected_min)
        max_expected_vals.append(expected_max)

        min_diff = abs(measured - expected_min)
        max_diff = abs(measured - expected_max)
        pct_off_min.append(min_diff / measured)
        pct_off_max.append(max_diff / measured)

        in_bounds = expected_min <= measured <= expected_max
        print(f"{str(in_bounds):9} | {len_value:5} | \
{measured:8} | \
{expected_min:7} {expected_max:7} | \
{min_diff:4} {max_diff:4} | \
{round(pct_off_min[-1], 4)} {round(pct_off_max[-1], 4)}")

    print(f"Avg min percent off: {100.0 * sum(pct_off_min) / len(pct_off_min):.4f}%")
    print(f"Avg max percent off: {100.0 * sum(pct_off_max) / len(pct_off_max):.4f}%")
    print(f"Variance percent off: {variance(list(zip(pct_off_min, pct_off_max)))[0]:.4f}% {variance(list(zip(pct_off_min, pct_off_max)))[1]:.4f}%")

    plot_comparison("bubble_sort", "Array Length", "Cycle Count", 
                    [('Expected Range', 'lightgray', min_expected_vals[:PLOT_LEN], max_expected_vals[:PLOT_LEN])], 
                    [('Measured', [(x, y) for x, y in zip(range(PLOT_LEN), measured_vals[:PLOT_LEN])])], s=5)


if __name__ == '__main__':
    main()
