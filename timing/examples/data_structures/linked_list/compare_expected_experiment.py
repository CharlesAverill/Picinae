import sys
from pathlib import Path
sys.path.append(str(Path(__file__).resolve().parents[3]))

import argparse
import re
from examples.neorv32.NEORV32Config import NEORV32Config
from examples import *
from statistics import variance
from sympy import Piecewise, Eq, Lt

PLOT_LEN = 100
CALLING_CONVENTION_CYCLES = 13

def parse_cycle_counts(log_path, func_name):
    """
    Parse a log file and extract cycle counts, lengths, and metadata for a specific linked list function.
    """
    with open(log_path, 'r') as f:
        lines = f.readlines()

    cycle_counts = []
    metadata = []

    capture = False
    for line in lines:
        line = line.strip()
        if line.startswith(f"=== {func_name} ==="):
            capture = True
            continue
        if line.startswith("===") and capture:
            break  # stop at next function

        if not capture:
            continue

        # match cycle count
        m_cycle = re.match(r'Cycle count read: (\d+)', line)
        if m_cycle:
            cycle_counts.append(int(m_cycle.group(1)))

        # match other metadata (len, key, pos, found/not found)
        if func_name == "find_in_list":
            m = re.match(r'Len: (\d+), found @ (\d+)', line)
            if m:
                length = int(m.group(1))
                found_idx = int(m.group(2))
                metadata.append((length, found_idx))
            else:
                m = re.match(r'Len: (\d+), not found', line)
                if m:
                    length = int(m.group(1))
                    metadata.append((length, -1))
        elif func_name == "insert_after_pos_in_list":
            m = re.match(r'Len: (\d+), Pos: (\d+), Inserted: (\d+)', line)
            if m:
                length = int(m.group(1))
                pos = int(m.group(2))
                val = int(m.group(3))
                metadata.append((length, pos, val))
        elif func_name == "insert_in_sorted_list":
            m = re.match(r'Len: (\d+), Inserted: (\d+)', line)
            if m:
                length = int(m.group(1))
                val = int(m.group(2))
                metadata.append((length, val))
    return cycle_counts, metadata

def main():
    parser = argparse.ArgumentParser(description='Compare linked-list experiment cycle counts with expected equation.')
    parser.add_argument('log_file', help='Path to the experiment log file')
    parser.add_argument('find_equation_file', help='Path to the file containing the verified timing equation for find_in_list')
    parser.add_argument('insert_equation_file', help='Path to the file containing the verified timing equation for insert_at_pos_in_list')
    parser.add_argument('--cpu_config_file', help='Path to JSON file containing CPU configuration', default=None, type=str)
    args = parser.parse_args()

    cpu = NEORV32Config(args.cpu_config_file)
    find_equation = compile_equation(args.find_equation_file, cpu, ["length", "found_idx"])
    insert_equation = compile_equation(args.insert_equation_file, cpu, ["l", "value", "position", "length"])

    for func_name, (equation, _) in [
        ("find_in_list", (find_equation, ["length", "found_idx"])),
        ("insert_after_pos_in_list", (insert_equation, ["l", "value", "position", "len"]))
    ]:
        print(f"\n=== Processing {func_name} ===\n")
        cycle_counts, metadata = parse_cycle_counts(args.log_file, func_name)
        pct_off = []

        # Organize measured points and compute expected ranges
        found_points = []
        notfound_points = []
        notfound_min = []
        notfound_max = []

        for i, measured in enumerate(cycle_counts):
            measured -= CALLING_CONVENTION_CYCLES

            # Handle each function with its parameter mapping
            if func_name == "find_in_list":
                length, found_idx = metadata[i]
                args_for_equation = [length, found_idx]
                args_for_equation2 = [length, found_idx]

            elif func_name == "insert_after_pos_in_list":
                length, pos, val = metadata[i]
                # Only "position" and "len" matter in the equation; others can be dummy
                args_for_equation = [1, 1, pos, length]
                args_for_equation2 = [1, 1, pos, length]

            else:
                raise ValueError(f"Unsupported function: {func_name}")

            # Compute expected min/max
            min_expected = equation(args_for_equation, "min")
            max_expected = equation(args_for_equation2, "max")

            # Organize by type
            if func_name == "find_in_list":
                if i == 0:
                    print(f"{'In Bounds':9} | {'Length':7} | {'Arguments':25} | {'Measured':8} | {'Min - Max':15} | {'Diffs':15} | Percent Off")
                if found_idx == -1 and 5 < length:
                    notfound_points.append((length, measured))
                    notfound_min.append(min_expected)
                    notfound_max.append(max_expected)
                elif 5 < found_idx:
                    found_points.append((found_idx, measured, min_expected, max_expected))
            else:
                found_points.append((length, pos, measured, min_expected, max_expected))

            # Compute diffs
            min_diff = abs(measured - min_expected)
            max_diff = abs(measured - max_expected)
            pct_off.append((min_diff / measured, max_diff / measured))

            print(f"{str(min_expected <= measured <= max_expected):9} | {length:7} | "
                f"{args_for_equation!s:>25} | {measured:8} | "
                f"{min_expected:7} {max_expected:7} | "
                f"{min_diff:7} {max_diff:7} | "
                f"{round(pct_off[-1][0],4)} {round(pct_off[-1][1],4)}")

        print(f"Avg min percent off: {100.0 * sum(i[0] for i in pct_off) / len(pct_off):.4}%")
        print(f"Avg max percent off: {100.0 * sum(i[1] for i in pct_off) / len(pct_off):.4}%")
        # print(f"Variance percent off: {variance(pct_off):.4}%")

        # Prepare data for plotting
        if func_name == "find_in_list":
            notfound_xs = [x for x, _ in notfound_points]
            found_xs = [x for x, _, _, _ in found_points]
            found_measured = [m for _, m, _, _ in found_points]
            found_min = [m for _, _, m, _ in found_points]
            found_max = [m for _, _, _, m in found_points]
            found_plot_points = list(zip(found_xs, found_measured))

            notfound_xs.insert(0, 1)
            notfound_min.insert(0, find_equation([1, 0], "min"))
            notfound_max.insert(0, find_equation([1, 0], "max"))

            plot_comparison(
                f"{func_name} timing",
                "Found Index",
                "Cycle Count",
                [
                    ('Expected', 'lightgray', notfound_min, notfound_max)
                    # ('Expected Found', 'skyblue', found_min, found_max)
                ],
                [
                    ('Measured Found', found_plot_points),
                    ('Measured Not Found', notfound_points)
                ],
                range_xs=[notfound_xs],
                savepath="./find_in_list_plot.png"
            )
        elif func_name == "insert_after_pos_in_list":
            found_points.sort(key=lambda t: t[1])
            found_xs = [x for _, x, _, _, _ in found_points]
            found_measured = [m for _, _, m, _, _ in found_points]
            found_min = [m for _, _, _, m, _ in found_points]
            found_max = [m for _, _, _, _, m in found_points]
            found_plot_points = list(zip(found_xs, found_measured))

            plot_comparison(
                f"{func_name} timing",
                "Insertion Position",
                "Cycle Count",
                [
                    ('Expected', 'lightgray', found_min, found_max)
                ],
                [
                    ('Measured', found_plot_points)
                ],
                range_xs=[found_xs],
                savepath="./insert_at_pos_plot.png"
            )

if __name__ == "__main__":
    main()
