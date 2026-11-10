"""Compare on-board cycle counts against the Rocq timing models and aiT.

    python3 compare.py [results/flash]

Reads the CSVs written by run_on_board.py and writes summary.txt next to them.
The models are direct ports of the time_of_* definitions in the *_proofs.v
files, instantiated with CortexM0NoWait.
"""
import csv
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'scripts'))
from collatz_max import cyc as collatz_cycles  # noqa: E402  (copy of collatz_proofs.v)

# CortexM0NoWait.v
tmovs_imm = tmovs_reg = tadds_3reg = tadds_imm8 = tsubs_imm8 = tmuls = 1
tcmp_reg = tcmp_imm = tlsls_imm = tlsrs_imm = ttst = tuxth = 1
tldr_imm = tldr_pc = tstr_imm = 2
tldm_base = tpush_base = 1
tpop_pc_base = 4
tb_taken, tb_not_taken, tb, tbl, tbx = 3, 1, 3, 4, 3
INT_MAX = 2**31 - 1


def sum_model(size, *_):
    t = tcmp_imm
    if size == 0:
        return t + tb_taken + tmovs_imm + tb + tbx
    return (t + tb_not_taken + tlsls_imm + tmovs_reg + tadds_3reg + tmovs_imm
            + (size - 1) * ((tldm_base + 1) + tadds_3reg + tcmp_reg + tb_taken)
            + (tldm_base + 1) + tadds_3reg + tcmp_reg + tb_not_taken + tbx)


def wtb_model(n, *_):
    t = tmovs_reg + tmuls + tlsls_imm + tcmp_reg
    if n * n <= n + n:
        return t + tb_taken + tbx
    it = tsubs_imm8 + tmovs_reg + tmuls + tlsls_imm + tcmp_reg
    return t + tb_not_taken + (n - 3) * (it + tb_taken) + it + tb_not_taken + tbx


NOT_FOUND = 0xFFFFFFFF


def find_model(length, idx, pm):
    t = (tpush_base + 2 + 1) + tcmp_imm
    if length == 0:
        return t + tb_taken + tldr_pc + (tpop_pc_base + 3)
    t += tb_not_taken + tmovs_imm + tb + pm * (tb_not_taken + tldr_imm + tcmp_reg)
    miss = tldr_imm + tcmp_reg + tb_taken + tadds_imm8 + tadds_imm8 + tcmp_reg + tb_not_taken
    if idx != NOT_FOUND:
        return (t + idx * miss + tldr_imm + tcmp_reg + tb_not_taken + tldr_imm + tcmp_reg
                + tb_not_taken + tuxth + tb + (tpop_pc_base + 3))
    return (t + (length - 1) * miss + tldr_imm + tcmp_reg + tb_taken + tadds_imm8
            + tadds_imm8 + tcmp_reg + tb_taken + tldr_pc + (tpop_pc_base + 3))


def collatz_model(n, *_):
    return collatz_cycles(n)


def find_in_list_model(length, idx, _):
    # time_of_find_in_list in ../llsearch/find_in_list_proof.v
    if length == 0:
        return tcmp_imm + tb_taken + tmovs_imm + tb + tbx
    t = tcmp_imm + tb_not_taken
    miss = tldr_imm + tcmp_reg + tb_not_taken + tldr_imm + tcmp_imm + tb_taken
    if idx != NOT_FOUND:
        return t + idx * miss + tldr_imm + tcmp_reg + tb_taken + tbx
    return (t + (length - 1) * miss + tldr_imm + tcmp_reg + tb_not_taken + tldr_imm
            + tcmp_imm + tb_not_taken + tbx)


def insert_after_pos_model(length, pos, kind):
    t = (tpush_base + 1 + 1) + tcmp_imm
    if kind == 1:                      # l == NULL
        return t + tb_taken + (tpop_pc_base + 2)
    t += tb_not_taken + tcmp_imm
    if kind == 2:                      # value == NULL
        return t + tb_taken + (tpop_pc_base + 2)
    t += tb_not_taken + tmovs_imm + tcmp_imm
    if pos == 0:
        return (t + tb_not_taken + tb + tmovs_reg + tldr_imm + tb + tstr_imm + tstr_imm
                + (tpop_pc_base + 2))
    t += tb_taken + (min(pos, length) - 1) * (
        tmovs_reg + tldr_imm + tcmp_imm + tb_taken + tadds_imm8 + tcmp_reg + tb_not_taken)
    t += tmovs_reg + tldr_imm + tcmp_imm
    if pos < length:
        t += tb_taken + tadds_imm8 + tcmp_reg + tb_taken + tmovs_reg + tldr_imm + tb
    else:
        t += tb_not_taken
    return t + tstr_imm + tstr_imm + (tpop_pc_base + 2)


def insert_in_sorted_model(_k, val, d):
    t = tldr_imm + tldr_pc + (tpush_base + 1 + 1) + tcmp_reg
    if val == INT_MAX:
        return (t + tb_taken + tmovs_reg + tldr_imm + tb + tstr_imm + tstr_imm
                + (tpop_pc_base + 2))
    return (t + tb_not_taken + d * (tmovs_reg + tldr_imm + tldr_imm + tcmp_reg + tb_taken)
            + tmovs_reg + tldr_imm + tldr_imm + tcmp_reg + tb_not_taken + tstr_imm + tstr_imm
            + (tpop_pc_base + 2))


# Calibration stubs in harness.S, in main.c's order: (name, expected cycles)
CALIB = [
    ('bx lr', tbx),
    ('nop; bx lr', 1 + tbx),
    ('8x nop; bx lr', 8 + tbx),
    ('ldr [sram]; bx lr', tldr_imm + tbx),
    ('ldr [flash]; bx lr', tldr_imm + tbx),
    ('str [sram]; bx lr', tstr_imm + tbx),
    ('ldm {r1}; bx lr', tldm_base + 1 + tbx),
    ('ldr =lit; bx lr', tldr_pc + tbx),
    ('muls; bx lr', tmuls + tbx),
    ('uxth; bx lr', tuxth + tbx),
    ('b; bx lr', tb + tbx),
    ('cmp; beq (taken); bx lr', tcmp_reg + tb_taken + tbx),
    ('cmp; beq (not taken); bx lr', tcmp_imm + tb_not_taken + tbx),
    ('push {r4,lr}; pop {r4,pc}', (tpush_base + 2) + (tpop_pc_base + 2)),
    ('push {r4,r5,lr}; pop {r4,r5,pc}', (tpush_base + 3) + (tpop_pc_base + 3)),
    ('push {lr}; bl stub_bx; pop {pc}', (tpush_base + 1) + tbl + tbx + (tpop_pc_base + 1)),
]


def calib_model(i, *_):
    return CALIB[i][1]


# name -> (model, aiT WCET from the *report.txt files, what in0/in1/in2 mean)
BENCHES = {
    'calib': (calib_model, None, 'stub'),
    'sum': (sum_model, 15032385539, 'size'),
    'while_true_break': (wtb_model, 8981, 'n'),
    'find': (find_model, 983077, 'len, idx (or not found), partial matches'),
    'collatz': (collatz_model, 990042, 'n'),
    'find_in_list': (find_in_list_model, 20496, 'len, idx (or not found)'),
    'insert_after_pos_in_list': (insert_after_pos_model, 21474836499,
                                 'len, pos, kind (0 normal, 1 l=NULL, 2 value=NULL)'),
    'insert_in_sorted_list': (insert_in_sorted_model, 18448, 'k, value, nodes passed over'),
}


def load(path):
    with open(path) as f:
        return [{k: int(v) for k, v in row.items()} for row in csv.DictReader(f)]


def summarize(results_dir):
    results_dir = Path(results_dir)
    lines = []
    for name, (model, wcet, params) in BENCHES.items():
        path = results_dir / f'{name}.csv'
        if not path.exists():
            continue
        rows = load(path)
        n = len(rows)
        bad_ok = [r for r in rows if not r['ok']]
        jitter = [r for r in rows if r['cmin'] != r['cmax']]
        miss = [r for r in rows if r['cmin'] != model(r['in0'], r['in1'], r['in2'])]
        worst = max(rows, key=lambda r: r['cmax'])
        lines.append(f'== {name}  ({n} inputs; in = {params})')
        lines.append(f'   functional result correct : {n - len(bad_ok)}/{n}')
        lines.append(f'   identical over repetitions: {n - len(jitter)}/{n}')
        lines.append(f'   measured == model         : {n - len(miss)}/{n}')
        if name == 'calib':
            for r in rows:
                stub, exp = CALIB[r['in0']]
                lines.append(f'     {stub:34s} measured {r["cmin"]:3d}  expected {exp:3d}'
                             f'{"" if r["cmin"] == exp else "   <-- MISMATCH"}')
        for r in miss[:10]:
            m = model(r['in0'], r['in1'], r['in2'])
            lines.append(f'     MISMATCH in=({r["in0"]}, {r["in1"]}, {r["in2"]}): '
                         f'measured {r["cmin"]}, model {m} ({r["cmin"] - m:+d})')
        if len(miss) > 10:
            lines.append(f'     ... {len(miss) - 10} more mismatches')
        if wcet is not None:
            lines.append(f'   max measured: {worst["cmax"]} cycles at in=({worst["in0"]}, '
                         f'{worst["in1"]}, {worst["in2"]});  aiT WCET bound: {wcet} '
                         f'({wcet / worst["cmax"]:.3g}x)')
        lines.append('')
    text = '\n'.join(lines)
    (results_dir / 'summary.txt').write_text(text)
    return text


if __name__ == '__main__':
    print(summarize(sys.argv[1] if len(sys.argv) > 1 else HERE / 'results' / 'flash'))
