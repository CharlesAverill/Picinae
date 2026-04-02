import sys
from pathlib import Path
sys.path.append(str(Path(__file__).resolve().parents[4]))

import argparse
import re
from sympy import Piecewise, Eq
from examples.neorv32.NEORV32Config import NEORV32Config
from examples import *

PLOT_LEN = 100
CALLING_CONVENTION_CYCLES = 13

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
    # measured_vals = [m - CALLING_CONVENTION_CYCLES for m in cycle_counts]

    # Separate lists for found / not found cases
    found_points = []
    notfound_min, notfound_max, notfound_points = [], [], []

    print(f"{'In Bounds':>9} | {'Len':>5} | {'Found Index':>11} | {'Measured':>8} | {'Expected Bounds':>15} | {'Diffs':>9} | {'Diffs/Measured':>14}")
    print("-" * 89)

    for i, (measured, found_idx) in enumerate(zip(cycle_counts, found)):
        measured -= CALLING_CONVENTION_CYCLES
        len_value = i + 1

        # Compute expected bounds
        min_expected = equation([len_value, found_idx], "min")
        max_expected = equation([len_value, found_idx], "max")

        # Record per case
        if found_idx == -1 and len_value - 1 < PLOT_LEN:
            # notfound_min.append(min_expected)
            # notfound_max.append(max_expected)
            notfound_points.append((len_value - 1, measured))
        elif found_idx != -1 and len_value - 1 < PLOT_LEN:
            found_points.append((found_idx, len_value - 1, measured, min_expected, max_expected))

        # Compute percent error
        min_diff = abs(measured - min_expected)
        max_diff = abs(measured - max_expected)
        pct_off.append((min_diff / measured, max_diff / measured))

        print(f"{str(min_expected <= measured <= max_expected):9} | {len_value:5} | \
{str(found_idx):>11} | \
{measured:8} | \
{min_expected:7} {max_expected:7} | \
{min_diff:4} {max_diff:4} | \
{round(pct_off[-1][0], 4)} {round(pct_off[-1][1], 4)}")

    # Summary statistics
    print(f"Avg min percent off: {100.0 * sum(i[0] for i in pct_off) / len(found):.4}%")
    print(f"Avg max percent off: {100.0 * sum(i[1] for i in pct_off) / len(found):.4}%")
    print(f"Variance percent off: {variance(pct_off)}%")

    notfound_min = [equation([length + 1, -1], "min") for length in range(1, PLOT_LEN)]
    notfound_max = [equation([length + 1, -1], "max") for length in range(1, PLOT_LEN)]
    notfound_xs  = list(range(1, PLOT_LEN))

    # found (search success) range depends only on found_idx
    found_xs  = [plot_x for (plot_x, _, _, _, _) in found_points]
    found_idxs = [found_idx for (_, found_idx, _, _, _) in found_points]
    found_measured = [measured for (_, _, measured, _, _) in found_points]
    found_min = [min for (_, _, _, min, _) in found_points]
    found_max = [max for (_, _, _, _, max) in found_points]

    # repackage measured points for plotting
    found_plot_points = list(zip(found_xs, found_measured))

    # Plot both ranges and measurement sets
    plot_comparison(
        "find (naïve)",
        "Found Index",
        "Cycle Count",
        [
            ('Expected', 'lightgray', notfound_min, notfound_max),
            # ('Expected Range (found)', 'skyblue', found_min, found_max)
            
        ],
        [
            ('Measured (found)', found_plot_points),
            ('Measured (not found)', notfound_points)
        ],
        range_xs=[notfound_xs, 
                #   found_idxs
                ],
        savepath="./find_naive_plot.png"
    )
    

if __name__ == '__main__':
    main()

