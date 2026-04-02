import sys
from pathlib import Path
sys.path.append(str(Path(__file__).resolve().parents[5]))

import argparse
import re
from sympy import symbols, Function
from examples.neorv32.NEORV32Config import NEORV32Config
from examples import *

PLOT_LEN = 100
CALLING_CONVENTION_CYCLES = 13

import re

def parse_cycle_counts(log_path):
    with open(log_path, 'r') as f:
        lines = f.readlines()

    cycle_counts = []
    swap_traces = []
    current_swaps = []

    for line in lines:
        line = line.strip()

        if line.startswith("Swaps:"):
            swap_text = line[len("Swaps:"):].strip()
            if swap_text == "[]":
                current_swaps = []
            else:
                current_swaps = re.findall(r'\((\d+),\s*(\d+)\)', swap_text)
                current_swaps = [(int(i), int(j)) for i, j in current_swaps]

        match = re.match(r'Cycle count read: (\d+)', line)
        if match:
            cycle_counts.append(int(match.group(1)))
            swap_traces.append(current_swaps)
            current_swaps = []

    swaps = []
    for st in swap_traces:
        def swap(i, j):
            return (i, j) in st
        swaps.append(swap)

    return cycle_counts, swaps

def compile_equation(equation_path, cpu, swap):
    with open(equation_path, 'r') as file:
        expr_str = file.read().strip()
    syms = [symbols(s) for s in ["length", "T_inst_latency", "T_data_latency"]]
    # swap = Function("swap")
    try:
        parsed_expr = sympify(expr_str, locals={"swap": swap})
        def equation(args, mode):
            if mode == "min":
                inst = cpu.min_inst_lat
                data = cpu.min_data_lat
            elif mode == "max":
                inst = cpu.max_inst_lat
                data = cpu.max_data_lat
            args += [inst, data]
            return int(parsed_expr.subs([(syms[i], args[i]) for i in range(len(syms))]).evalf())
        return equation
    except Exception as e:
        print(f"Failed to parse equation: {e}")
        return None

def main():
    parser = argparse.ArgumentParser(description='Compare experiment cycle counts with min/max expected bounds.')
    parser.add_argument('log_file', help='Path to the experiment log file')
    parser.add_argument('equation_file', help='Path to the file containing the verified timing equation')
    parser.add_argument('--cpu_config_file', help='Path to JSON file containing CPU configuration', default=None, type=str)

    args = parser.parse_args()

    cpu = NEORV32Config(args.cpu_config_file)
    cycle_counts, swaps = parse_cycle_counts(args.log_file)

    measured_vals = [m - CALLING_CONVENTION_CYCLES for m in cycle_counts]

    pct_off_min = []
    pct_off_max = []
    min_expected_vals = []
    max_expected_vals = []

    print(f"{'In Bounds':>9} | {'Len':>5} | {'Measured':>8} | {'Expected Bounds':>15} | {'Diffs':>10} | {'Diffs/Measured':>13}")
    print("-" * 77)

    for i, (measured, swap) in enumerate(zip(measured_vals, swaps)):
        equation = compile_equation(args.equation_file, cpu, swap)
        length = i + 1

        expected_min = equation([length], 'min')
        expected_max = equation([length], 'max')

        min_expected_vals.append(expected_min)
        max_expected_vals.append(expected_max)

        min_diff = abs(measured - expected_min)
        max_diff = abs(measured - expected_max)
        pct_off_min.append(min_diff / measured if measured else 0)
        pct_off_max.append(max_diff / measured if measured else 0)

        in_bounds = expected_min <= measured <= expected_max

        print(f"{str(in_bounds):9} | {length:5} | {measured:8} | {expected_min:7} {expected_max:7} | {min_diff:5} {max_diff:4} | {pct_off_min[-1]:6.4f} {pct_off_max[-1]:6.4f}")

    print(f"Avg min percent off: {100.0 * sum(pct_off_min) / len(pct_off_min):.4f}%")
    print(f"Avg max percent off: {100.0 * sum(pct_off_max) / len(pct_off_max):.4f}%")
    print(f"Variance percent off: {variance(list(zip(pct_off_min, pct_off_max)))[0]:.4f}% {variance(list(zip(pct_off_min, pct_off_max)))[1]:.4f}%")

    plot_comparison("bubble_sort (exact)", "Array Length", "Cycle Count", 
                    [('Expected Range (min-max)', 'lightgray', min_expected_vals[:PLOT_LEN], max_expected_vals[:PLOT_LEN])], 
                    [('Measured', measured_vals[:PLOT_LEN])])


if __name__ == '__main__':
    main()
