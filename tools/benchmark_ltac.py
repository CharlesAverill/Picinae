#!/usr/bin/env python3
"""Compile all partial-correctness examples sequentially with both backends.
Run after make, with rocq on PATH. All generated files/logs go to --output.
"""
import argparse
import csv
import json
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--runs', type=int, default=3)
parser.add_argument('--baseline', type=Path, help='unmodified source tree, already built')
args = parser.parse_args()
if args.runs < 3:
    parser.error('at least three runs required')
root = Path(__file__).resolve().parent.parent
out = args.output.resolve()
out.mkdir(parents=True, exist_ok=True)
selector = '''
Ltac psimpl_goal ::= psimpl_goal_ltac1.
Ltac psimpl_hyp h ::= psimpl_hyp_ltac1 h.
Ltac psimpl_exp_goal e ::= psimpl_exp_goal_ltac1 e.
Ltac psimpl_exp_hyp e h ::= psimpl_exp_hyp_ltac1 e h.
Ltac ISA_step ::= ISA_step_ltac1.
'''
proofs = sorted((root / 'Examples').glob('*proof.v'))
records = []
metadata = dict(machine=platform.node(), platform=platform.platform(),
                cpu=Path('/proc/cpuinfo').read_text().split('model name')[1].splitlines()[0],
                version=subprocess.check_output(['rocq', '--version'], text=True),
                start_load=os.getloadavg(), commands=[])


def compile_file(tree, source, log):
    cmd = ['rocq', 'compile', '-R', str(tree), 'Picinae', '-Q', str(source.parent), '', str(source)]
    metadata['commands'].append(cmd)
    (out / 'metadata.json').write_text(json.dumps(metadata, indent=2))
    load = os.getloadavg()
    start = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run(['/usr/bin/time', '-f', 'wall=%e user=%U sys=%S rss_kb=%M', *cmd],
                                stdout=stream, stderr=subprocess.STDOUT, cwd=source.parent)
    return result.returncode, time.monotonic() - start, load, os.getloadavg()


# Establish the complete baseline eligibility list before timing migrated code.
eligible = []
metadata["baseline_results"] = {}
tree = args.baseline.resolve() if args.baseline else root
for dependency in sorted((tree / 'Examples').glob('*.v')):
    if dependency.stem.endswith('_proof') or dependency.name == 'riscv_cfi.v':
        continue
    code, *_ = compile_file(tree, dependency, out / (dependency.stem + '-dependency.log'))
    if code:
        print('Dependency failed:', dependency, flush=True)
for proof in proofs:
    source = tree / 'Examples' / proof.name
    code, *_ = compile_file(tree, source, out / (proof.stem + '-baseline.log'))
    metadata["baseline_results"][proof.name] = code
    if code == 0:
        eligible.append(proof)
    else:
        print('Baseline failed:', proof.name, flush=True)

for proof in eligible:
    for backend in ['ltac1', 'ltac2']:
        directory = out / backend
        directory.mkdir(exist_ok=True)
        text = proof.read_text()
        if backend == 'ltac1':
            text = re.sub(r'(Require Import Picinae_\w+\.)', r'\1\n' + selector, text, count=1)
        (directory / proof.name).write_text(text)
# Build dependency .vo files for each generated source directory.
for backend in ['ltac1', 'ltac2']:
    directory = out / backend
    directory.mkdir(exist_ok=True)
    for dependency in sorted((root / 'Examples').glob('*.v')):
        if dependency.stem.endswith('_proof') or dependency.name == 'riscv_cfi.v':
            continue
        target = directory / dependency.name
        target.write_text(dependency.read_text())
        compile_file(root, target, out / (backend + '-' + dependency.stem + '-dependency.log'))

# Alternate backend order to reduce bias; timing processes never overlap.
for proof in eligible:
    for run in range(1, args.runs + 1):
        for backend in (['ltac1', 'ltac2'] if run % 2 else ['ltac2', 'ltac1']):
            source = out / backend / proof.name
            code, wall, before, after = compile_file(root, source, out / f'{proof.stem}-{backend}-{run}.log')
            record = dict(example=proof.stem, backend=backend, run=run, seconds=wall,
                          exit_code=code, load_before=before, load_after=after)
            records.append(record)
            (out / 'runs.json').write_text(json.dumps(records, indent=2))
            print(record, flush=True)
    # Rerun a backend twice when any sample differs from its median by >15%.
    for backend in ['ltac1', 'ltac2']:
        samples = [r['seconds'] for r in records
                   if r['example'] == proof.stem and r['backend'] == backend and r['exit_code'] == 0]
        if samples and max(abs(x / statistics.median(samples) - 1) for x in samples) > .15:
            for run in [args.runs + 1, args.runs + 2]:
                code, wall, before, after = compile_file(root, out / backend / proof.name,
                    out / f'{proof.stem}-{backend}-{run}.log')
                records.append(dict(example=proof.stem, backend=backend, run=run, seconds=wall,
                                    exit_code=code, load_before=before, load_after=after))
                (out / 'runs.json').write_text(json.dumps(records, indent=2))
    # Profile separately: profiling overhead is excluded from timing runs.
    for backend in ['ltac1', 'ltac2']:
        source = out / backend / proof.name
        original = source.read_text()
        source.write_text('Set Ltac Profiling.\n' + original + '\nShow Ltac Profile.\n')
        compile_file(root, source, out / f'{proof.stem}-{backend}-profile.log')
        source.write_text(original)

with (out / 'medians.csv').open('w') as stream:
    writer = csv.writer(stream)
    writer.writerow(['example', 'ltac1_seconds', 'ltac2_seconds', 'percent_change'])
    for proof in eligible:
        values = {}
        for backend in ['ltac1', 'ltac2']:
            rows = [r for r in records if r['example'] == proof.stem and r['backend'] == backend]
            if all(r['exit_code'] == 0 for r in rows):
                values[backend] = statistics.median(r['seconds'] for r in rows)
        if len(values) == 2:
            a, b = values['ltac1'], values['ltac2']
            writer.writerow([proof.stem, a, b, 100 * (b / a - 1)])
metadata['end_load'] = os.getloadavg()
(out / 'metadata.json').write_text(json.dumps(metadata, indent=2))
