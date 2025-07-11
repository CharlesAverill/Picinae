import argparse
import re
from sympy import symbols, sympify, Piecewise, Eq

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

def compile_equation(equation_path):
    with open(equation_path, 'r') as file:
        expr_str = file.read().strip()
    length_sym = symbols('length')
    i_sym = symbols('i')
    try:
        parsed_expr = sympify(expr_str)
        return lambda length_value, i_value: int(parsed_expr.subs(length_sym, length_value).subs(i_sym, i_value).evalf())
    except Exception as e:
        print(f"Failed to parse equation: {e}")
        return lambda length_value, i_value: None

def variance(data, sample=False):
    if not data:
        return 0.0
    mean = sum(data) / len(data)
    squared_diffs = [(x - mean) ** 2 for x in data]
    divisor = len(data) - 1 if sample and len(data) > 1 else len(data)
    return sum(squared_diffs) / divisor


def main():
    parser = argparse.ArgumentParser(description='Compare experiment cycle counts with an expected equation.')
    parser.add_argument('log_file', help='Path to the experiment log file')
    parser.add_argument('equation_file', help='Path to the file containing the verified timing equation')

    args = parser.parse_args()

    cycle_counts, found = parse_cycle_counts(args.log_file)
    equation = compile_equation(args.equation_file)

    print(f"{'Len':>5} | {'Found Index':>11} | {'Measured':>8} | {'Expected':>8} | {'Diff':>6} | {'Diff/Measured':>13}")
    print("-" * 66)

    pct_off = []

    for i, (measured, found_idx) in enumerate(zip(cycle_counts, found)):
        measured -= 9999 # To account for calling convention cycles in the caller # TODO
        len_value = i + 1
        expected = equation(len_value, found_idx)
        if expected is not None:
            diff = abs(measured - expected)
            pct_off.append(diff / measured)
            print(f"{len_value:5} | {str(found_idx):>11} | {measured:8} | {expected:8} | {diff:6} | {diff/measured:.4f}")
        else:
            print(f"{len_value:5} | {str(found_idx):>11} | {measured:8} | {'ERROR':>8} | {'--':>6} | {'--':13}")

    print(f"Avg percent off: {100.0 * sum(pct_off) / len(found):.4}%")
    print(f"Variance percent off: {variance(pct_off)}%")

if __name__ == '__main__':
    main()

