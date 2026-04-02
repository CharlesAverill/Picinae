import sys
from pathlib import Path
sys.path.append(str(Path(__file__).resolve().parents[4]))

import argparse
import re
from bisect import bisect_left
from examples.neorv32.NEORV32Config import NEORV32Config
from examples import *

PLOT_LEN = 100
CALLING_CONVENTION_CYCLES = 11


def parse_insert_log(log_path):
    """
    Parse the vListInsert test block from the log.
    Returns a list of (value, cycle_count, insert_index) tuples.
    """
    with open(log_path, 'r') as f:
        lines = f.readlines()

    capture = False
    entries = []
    current_list = []  # tracks the evolving sorted list of inserted values

    for i, line in enumerate(lines):
        line = line.strip()
        if line.startswith("=== Test: vListInsert ==="):
            capture = True
            continue
        elif line.startswith("===") and capture:
            # Stop when next test starts
            break
        if not capture:
            continue

        # Parse each new item value
        match_val = re.match(r"Iteration\s+\d+: inserting new item \(value=(\d+)\)", line)
        if match_val:
            current_value = int(match_val.group(1))
            # Determine where this value would be inserted in ascending order
            insert_idx = bisect_left(current_list, current_value)
            # Insert it into our local list representation
            current_list.insert(insert_idx, current_value)
            entries.append({"value": current_value, "insert_idx": insert_idx, "cycle": None})
            continue

        match_cycle = re.match(r"Cycle count read: (\d+)", line)
        if match_cycle and entries:
            entries[-1]["cycle"] = int(match_cycle.group(1))

    return entries


def main():
    parser = argparse.ArgumentParser(description="Analyze and plot vListInsert cycle counts vs. insertion index.")
    parser.add_argument("log_file", help="Path to the experiment log file")
    parser.add_argument("equation_file", help="Path to the file containing the verified timing equation")
    parser.add_argument("--cpu_config_file", help="Path to JSON file containing CPU configuration", default=None)
    args = parser.parse_args()

    cpu = NEORV32Config(args.cpu_config_file)
    equation = compile_equation(args.equation_file, cpu, ["le_addr"])

    data = parse_insert_log(args.log_file)
    data.sort(key=lambda entry: entry["insert_idx"])
    pct_off = []
    measured_vals = []
    min_expected_vals = []
    max_expected_vals = []

    print(f"{'In Bounds':>9} | {'Iter':>4} | {'Insert Idx':>10} | {'Value':>10} | "
          f"{'Measured':>8} | {'Expected Bounds':>15} | {'Diffs':>9} | {'Diffs/Measured':>14}")
    print("-" * 95)

    min_expected_vals = [equation([i], "min") for i in range(0, PLOT_LEN)]
    max_expected_vals = [equation([i], "max") for i in range(0, PLOT_LEN)]

    for i, entry in enumerate(data):
        measured = entry["cycle"] - CALLING_CONVENTION_CYCLES
        insert_idx = entry["insert_idx"]
        if insert_idx < PLOT_LEN:
            measured_vals.append((insert_idx, measured))

        min_expected = equation([insert_idx], "min")
        max_expected = equation([insert_idx], "max")

        min_diff = abs(measured - min_expected)
        max_diff = abs(measured - max_expected)
        pct_off.append((min_diff / measured, max_diff / measured))
        print(f"{str(min_expected <= measured <= max_expected):9} | {i:4} | {insert_idx:10} | "
              f"{entry['value']:10} | {measured:8} | {min_expected:7} {max_expected:7} | "
              f"{min_diff:4} {max_diff:4} | {round(pct_off[-1][0], 4):>7} {round(pct_off[-1][1], 4):>7}")

    print(f"\nAvg min percent off: {100.0 * sum([i[0] for i in pct_off]) / len(pct_off):.4}%")
    print(f"Avg max percent off: {100.0 * sum([i[1] for i in pct_off]) / len(pct_off):.4}%")
    print(f"Variance percent off: {variance(pct_off)}%")

    plot_comparison(
        "vListInsert Timing",
        "Insertion Index",
        "Cycle Count",
        [('Expected', 'lightgray',
          min_expected_vals[:PLOT_LEN], max_expected_vals[:PLOT_LEN])],
        [('Measured', measured_vals)], savepath="./plots/vListInsert.png"
    )


if __name__ == "__main__":
    main()
