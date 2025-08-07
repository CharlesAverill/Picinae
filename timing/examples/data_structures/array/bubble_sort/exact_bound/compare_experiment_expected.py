import argparse
import re
from sympy import symbols, sympify, Piecewise, Eq, Max

def parse_cycle_counts(log_path):
    with open(log_path, 'r') as f:
        lines = f.readlines()

    cycle_counts = []
    for line in lines:
        match = re.match(r'Cycle count read: (\d+)', line.strip())
        if match:
            cycle_counts.append(int(match.group(1)))
    return cycle_counts

def compile_equation(equation_path):
    with open(equation_path, 'r') as file:
        expr_str = file.read().strip()
    length_sym = symbols('length')
    try:
        parsed_expr = sympify(expr_str)
        return lambda length_value: int(parsed_expr.subs(length_sym, length_value).evalf())
    except Exception as e:
        print(f"Failed to parse equation: {e}")
        return lambda length_value: None

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
    parser.add_argument('min_equation_file', help='Path to the file containing the verified timing minimum equation')
    parser.add_argument('max_equation_file', help='Path to the file containing the verified timing maximum equation')

    args = parser.parse_args()

    cycle_counts = parse_cycle_counts(args.log_file)
    min_eq, max_eq = compile_equation(args.min_equation_file), compile_equation(args.max_equation_file)

    print(f"{'Len':>5} | {'Expected Min':>12} | {'Measured':>8} | {'Expected Max':>12} | {'Within Bounds':13} | {'Diff Min':8} | {'Diff Min %':10} | {'Diff Max':8} | {'Diff Max %':10}")
    print("-" * 110)

    for i, measured in enumerate(cycle_counts):
        measured -= 13 # To account for calling convention cycles in the caller
        len_value = i + 1
        expected_min, expected_max = min_eq(len_value), max_eq(len_value)
        if expected_min is not None and expected_max is not None:
            print(f"{len_value:5} | {expected_min:12} | {measured:8} | {expected_max:12} | {'True' if expected_min < measured < expected_max else 'False':13} | \
{abs(measured - expected_min):8} | {100*abs(measured - expected_min)/measured:10.2f} | {abs(measured - expected_max):8} | {100*abs(measured - expected_max)/measured:10.2f}")
        else:
            print(f"Error for len={len_value}")

if __name__ == '__main__':
    main()

