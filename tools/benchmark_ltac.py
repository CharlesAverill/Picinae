#!/usr/bin/env python3
"""Benchmark unchanged partial-correctness examples through picinae-env.

Build this tree and an unmodified baseline through the same wrapper first.
Every compiler invocation is sequential. Generated sources and logs go to
--output; the original Examples sources are never edited.
"""
import argparse
import csv
import hashlib
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
parser.add_argument('--baseline', type=Path, required=True,
                    help='unmodified source tree, already built through the wrapper')
parser.add_argument('--runs', type=int, default=3)
parser.add_argument('--wrapper', type=Path,
                    default=Path('/home/charles/code/friends/.toolchains/picinae-env'))
parser.add_argument('--profile', nargs='*', default=['arm7_memset_proof', 'i386_strlen_proof'],
                    help='example stems to profile separately (default: memset and x86 strlen)')
args = parser.parse_args()
if args.runs < 3:
    parser.error('at least three runs required')
if not args.wrapper.is_file():
    parser.error(f'wrapper is not available: {args.wrapper}')
root = Path(__file__).resolve().parent.parent
baseline = args.baseline.resolve()
out = args.output.resolve()
out.mkdir(parents=True, exist_ok=True)
if (out / 'runs.json').exists():
    parser.error('use a fresh output directory to keep timing passes separate')
wrapper = str(args.wrapper.resolve())
selector = '''
Ltac psimpl_goal ::= psimpl_goal_ltac1.
Ltac psimpl_hyp h ::= psimpl_hyp_ltac1 h.
Ltac psimpl_exp_goal e ::= psimpl_exp_goal_ltac1 e.
Ltac psimpl_exp_hyp e h ::= psimpl_exp_hyp_ltac1 e h.
Ltac ISA_step ::= ISA_step_ltac1.
'''
proofs = sorted((root / 'Examples').glob('*proof.v'))
dependencies = [p for p in sorted((root / 'Examples').glob('*.v'))
                if not p.stem.endswith('_proof') and p.name != 'riscv_cfi.v']
records = []
metadata = dict(
    machine=platform.node(), platform=platform.platform(),
    cpu=next(line.split(':', 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines()
             if line.startswith('model name')),
    version=subprocess.check_output([wrapper, 'rocq', '--version'], text=True),
    revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
    wrapper=wrapper, wrapper_sha256=hashlib.sha256(args.wrapper.read_bytes()).hexdigest(),
    started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
    start_load=os.getloadavg(), commands=[], baseline_results={}, profiles={},
    source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in proofs})


def save():
    (out / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    (out / 'runs.json').write_text(json.dumps(records, indent=2) + '\n')


def compile_file(tree, source, log):
    cmd = [wrapper, '/usr/bin/time', '-f', 'wall=%e user=%U sys=%S rss_kb=%M',
           'rocq', 'compile', '-R', str(tree), 'Picinae',
           '-Q', str(source.parent), '', str(source)]
    record = dict(command=cmd, log=log.name, load_before=os.getloadavg())
    start = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run(cmd, stdout=stream, stderr=subprocess.STDOUT, cwd=source.parent)
    record.update(exit_code=result.returncode, outer_seconds=time.monotonic() - start,
                  load_after=os.getloadavg())
    match = re.search(r'^wall=([0-9.]+) user=', log.read_text(), re.MULTILINE)
    record['compile_seconds'] = float(match.group(1)) if match else None
    metadata['commands'].append(record)
    save()
    return record


def checked_compile(tree, source, log):
    record = compile_file(tree, source, log)
    if record['exit_code'] or record['compile_seconds'] is None:
        raise SystemExit(f'Compilation failed; inspect {log}')
    return record


def summarize():
    with (out / 'medians.csv').open('w') as stream:
        writer = csv.writer(stream)
        writer.writerow(['example', 'ltac1_seconds', 'ltac2_seconds', 'percent_change',
                         'ltac1_outer_seconds', 'ltac2_outer_seconds', 'ltac1_runs', 'ltac2_runs'])
        for proof in eligible:
            a = [r for r in records if r['example'] == proof.stem and r['backend'] == 'ltac1']
            b = [r for r in records if r['example'] == proof.stem and r['backend'] == 'ltac2']
            if len(a) >= args.runs and len(b) >= args.runs:
                med_a = statistics.median(r['compile_seconds'] for r in a)
                med_b = statistics.median(r['compile_seconds'] for r in b)
                writer.writerow([proof.stem, med_a, med_b, 100 * (med_b / med_a - 1),
                    statistics.median(r['outer_seconds'] for r in a),
                    statistics.median(r['outer_seconds'] for r in b), len(a), len(b)])


# Establish baseline eligibility before collecting any comparison samples.
for dependency in dependencies:
    checked_compile(baseline, baseline / 'Examples' / dependency.name,
                    out / (dependency.stem + '-baseline-dependency.log'))
eligible = []
for proof in proofs:
    if proof.read_bytes() != (baseline / 'Examples' / proof.name).read_bytes():
        raise SystemExit(f'Example differs from baseline: {proof.name}')
    record = compile_file(baseline, baseline / 'Examples' / proof.name,
                          out / (proof.stem + '-baseline.log'))
    metadata['baseline_results'][proof.name] = record['exit_code']
    if record['exit_code'] == 0:
        eligible.append(proof)
    print('Baseline:', proof.name, record['exit_code'], flush=True)
save()

for backend in ['ltac1', 'ltac2']:
    directory = out / backend
    directory.mkdir()
    for proof in eligible:
        source = proof.read_text()
        if backend == 'ltac1':
            source, count = re.subn(r'(Require Import Picinae_\w+\.)', r'\1\n' + selector,
                                    source, count=1)
            if count != 1:
                raise SystemExit(f'Cannot insert backend selector: {proof.name}')
        (directory / proof.name).write_text(source)
    for dependency in dependencies:
        target = directory / dependency.name
        target.write_bytes(dependency.read_bytes())
        checked_compile(root, target, out / f'{backend}-{dependency.stem}-dependency.log')


def sample(proof, backend, run):
    record = checked_compile(root, out / backend / proof.name,
                             out / f'{proof.stem}-{backend}-{run}.log')
    record.update(example=proof.stem, backend=backend, run=run)
    records.append(record)
    save()
    print(proof.stem, backend, run, record['compile_seconds'], flush=True)


for proof in eligible:
    for run in range(1, args.runs + 1):
        for backend in (['ltac1', 'ltac2'] if run % 2 else ['ltac2', 'ltac1']):
            sample(proof, backend, run)
    # Rerun twice when a sample differs from its backend median by >15%.
    for backend in ['ltac1', 'ltac2']:
        values = [r['compile_seconds'] for r in records
                  if r['example'] == proof.stem and r['backend'] == backend]
        median = statistics.median(values)
        if max(abs(value / median - 1) for value in values) > .15:
            for run in [args.runs + 1, args.runs + 2]:
                sample(proof, backend, run)
    summarize()

# Profiling is separate from every uninstrumented timing pass.
for proof in eligible:
    if proof.stem not in args.profile:
        continue
    for backend in ['ltac1', 'ltac2']:
        source = out / backend / proof.name
        original = source.read_text()
        try:
            source.write_text('Set Ltac Profiling.\n' + original + '\nShow Ltac Profile.\n')
            record = checked_compile(root, source, out / f'{proof.stem}-{backend}-profile.log')
            metadata['profiles'][f'{proof.stem}-{backend}'] = record['exit_code']
        finally:
            source.write_text(original)
metadata.update(end_load=os.getloadavg(), finished_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
save()
