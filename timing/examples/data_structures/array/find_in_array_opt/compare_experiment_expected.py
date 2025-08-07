import sys
from pathlib import Path
sys.path.append(str(Path(__file__).resolve().parents[4]))

import argparse
import re
from sympy import Piecewise, Eq
from examples.neorv32.NEORV32Config import NEORV32Config
from examples import *

PLOT_LEN = 100
CALLING_CONVENTION_CYCLES = 15

def parse_cycle_counts(log_path):
    with open(log_path, 'r') as f:
        lines = f.readlines()

    cycle_counts = []
    found = []
    for line in lines:
        match = re.match(r'Cycle count read: (\d+)', line.strip())
        if match:
            cycle_counts.append(int(match.group(1)))
        match = re.search(r' found at index (\d+)', line.strip())
        if match:
            found.append(int(match.group(1)))
        elif re.search(r'not found', line.strip()):
            found.append(-1)
    return cycle_counts, found


def main():
    parser = argparse.ArgumentParser(description='Compare experiment cycle counts with an expected equation.')
    parser.add_argument('log_file', help='Path to the experiment log file')
    parser.add_argument('equation_file', help='Path to the file containing the verified timing equation')
    parser.add_argument('--cpu_config_file', help='Path to JSON file containing CPU configuration', default=None, type=str)

    args = parser.parse_args()

    cpu = NEORV32Config(args.cpu_config_file)

    cycle_counts, found = parse_cycle_counts(args.log_file)
    equation = compile_equation(args.equation_file, cpu, ["length", "i"])

    pct_off = []
    measured_vals = [m - 13 for m in cycle_counts]
    min_expected_vals = []
    max_expected_vals = []

    print(f"{'In Bounds':>9} | {'Len':>5} | {'Found Index':>11} | {'Measured':>8} | {'Expected Bounds':>15} | {'Diffs':>9} | {'Diffs/Measured':>14}")
    print("-" * 89)

    for i, (measured, found_idx) in enumerate(zip(cycle_counts, found)):
        measured -= CALLING_CONVENTION_CYCLES
        len_value = i + 1

        min_expected, max_expected = \
            equation([len_value, found_idx], "min"), \
            equation([len_value, found_idx], "max")        
        min_expected_vals.append(min_expected)
        max_expected_vals.append(max_expected)

        min_diff = abs(measured - min_expected)
        max_diff = abs(measured - max_expected)
        pct_off.append((min_diff / measured, max_diff / measured))
        print(f"{str(min_expected <= measured <= max_expected):9} | {len_value:5} | \
{str(found_idx):>11} | \
{measured:8} | \
{min_expected:7} {max_expected:7} | \
{min_diff:4} {max_diff:4} | \
{round(pct_off[-1][0], 4)} {round(pct_off[-1][1], 4)}")
        

    print(f"Avg min percent off: {100.0 * sum([i[0] for i in pct_off]) / len(found):.4}%")
    print(f"Avg max percent off: {100.0 * sum([i[1] for i in pct_off]) / len(found):.4}%")
    print(f"Variance percent off: {variance(pct_off)}%")

    plot_comparison("find (naïve)", "Array Length", "Cycle Count", 
                    [('Expected Range (min-max)', 'lightgray', min_expected_vals[:PLOT_LEN], max_expected_vals[:PLOT_LEN])], 
                    [('Measured', measured_vals[:PLOT_LEN])])
    

if __name__ == '__main__':
    main()

