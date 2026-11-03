#!/usr/bin/env python3
r"""Sequential Ltac1/Ltac2 comparison harness.

All library builds and verification must use
`/home/charles/code/friends/.toolchains/picinae-env` (Rocq 9.1.1 for this migration).
Build the unchanged baseline snapshot and the final merged migration first. Stop
other implementation/build/benchmark jobs before collecting comparison samples.
The harness does not build either library. It rejects concurrent harness processes
across output directories, but cannot exclude unrelated external compiler jobs.

An eligibility/selection check collects no comparison samples:

```sh
/home/charles/code/friends/.toolchains/picinae-env python3 tools/benchmark_ltac.py \
  --baseline /tmp/picinae-ltac2/baseline-9.1.1 \
  --output /tmp/picinae-ltac-eligibility --phase prepare
```

Use `--phase baseline` to check only the baseline. Every `Examples/*.v` is
compiled in local dependency order, including lifted inputs and `riscv_cfi.v`.
A baseline example failure is recorded with its complete log, and discovery
continues. Only baseline-building `*_proof.v` files enter comparisons. Other
baseline-building examples compile on each migrated backend during preparation;
CFI safety is validation, not a partial-correctness timing target. The original
example files must be byte-identical in both trees. The baseline snapshot's `.v`
files and `_CoqProject` must also match `--baseline-revision` (default full original
master revision `a87fc67dd1bafd4eccb35812f6459f51e4d79e3b`) in git.

After merging, clean-building, and stopping other jobs, use a **fresh output**:

```sh
/home/charles/code/friends/.toolchains/picinae-env python3 tools/benchmark_ltac.py \
  --baseline /tmp/picinae-ltac2/baseline-9.1.1 \
  --output /tmp/picinae-ltac-final --runs 3
```

No comparisons from pre-merge checks or interrupted earlier experiments belong
in this final output. A directory must be outside both source trees, preventing
recursive library load paths from including generated benchmark modules.

The Ltac2 copies of **all** examples remain byte-identical, including whitespace
and line endings. The Ltac1 proof/CFI copies insert only a selector after their
single architecture import. It rebinds the four resolved `PSimpl_*` adapters,
four resolved `ISA_*` adapters, and architecture step alias to explicit retained
`*_ltac1` entries. Separate sentinel probes compile for all five architectures
and check that each public simplifier form and ISA entry reaches the intended
retained entry. The probe substitutions never appear in measured sources.
Default-backend semantic probes poison retained entry points and must still
solve their goals, preventing a silently unchanged Ltac1 default from being
labeled Ltac2. These checks stop collection before any comparison samples.
The retained graph still uses the original Ltac1 reflective simplifier and ISA
hooks; this benchmark compares orchestration in the same migrated libraries,
not all of the old baseline library against the new library.

Every compiler invocation is sequential, including validation and profiling.
Backend order alternates per round (1/2, 2/1, 1/2). At least three successful
samples per backend are mandatory. If any original sample differs from its
backend median by more than 15%, that backend gets two additional samples.
All samples, including outliers, remain in the median. `medians.csv` reports
final outlier run numbers so persistent variation remains visible. The rerun
decision is checkpointed, making interrupted passes deterministic.
Percent change is `100 * (Ltac2 median / Ltac1 median - 1)`; negative means faster.

`metadata.json` contains exact argument arrays, shell-rendered commands, working
directories, toolchain/config/package versions, executable/wrapper/harness/source
and `.vo` digests, machine information, UTC timestamps, return codes, load averages
before/after each invocation, and the full command history. Separate `.time.json`
files contain GNU time's inner `rocq compile` wall/user/system/RSS measurements.
`outer_seconds` covers the complete wrapper/opam/time/compiler process;
`wrapper_and_launch_seconds = outer_seconds - compile_seconds` includes opam,
wrapper, launcher, and measurement overhead. It is an estimate (GNU time wall
resolution is 0.01 seconds), not a measurement of opam alone. CSV contains medians
of both wall clocks and of the per-invocation overhead estimates.

Profiles run only after all uninstrumented comparisons. They use separate source
and artifact directories, `Set Ltac Profiling`, **and**
`Set Ltac2 In Ltac1 Profiling`; without the latter the Ltac2 function profile is
missing. Every eligible proof is profiled by default. Use `--profile stem ...` for
a subset, or a bare `--profile` to disable profiling. Profile commands have kind
`profile` and never enter `runs.json` or `medians.csv`. The original timed sources
and their `.vo` files are never overwritten with instrumented versions.

On any migrated compilation failure, stop immediately and inspect the recorded
log. The default per-compile timeout is 1800 seconds (`--timeout` overrides it).
Interruptions/timeouts kill the entire compiler process group before returning.
To continue the *same experiment*, rerun the exact command with `--resume`.
Completed samples are reused, failed/interrupted work gets new logs, and stale
`running` records become `interrupted`. Successful dependency artifacts are
checked and rebuilt if absent or changed. Completed logs must remain intact.
Source, library artifact, wrapper, executable/version, harness, baseline revision,
or measurement-option changes reject resume; use a fresh output for those.
The phase may advance from baseline to prepare to all while other inputs remain
identical. Library digest changes between samples or before completion abort the
pass. Load averages are observational; the harness does not silently wait for or
discard high-load samples.

Harness bookkeeping tests use fake compilers and collect no performance data:

```sh
/home/charles/code/friends/.toolchains/picinae-env python3 tools/test_benchmark_ltac.py
```
"""
import argparse
from contextlib import contextmanager
import csv
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import signal
import statistics
import subprocess
import time

BASELINE_REVISION = 'a87fc67dd1bafd4eccb35812f6459f51e4d79e3b'
BINARY_DIGESTS = '''import hashlib,json,pathlib,shutil
names=['rocq','rocqchk','ocamlc','opam']
paths={name:shutil.which(name) for name in names}
rocq=pathlib.Path(paths['rocq']).resolve()
for path in (rocq.parent.parent/'lib'/'rocq-runtime').glob('rocq*'):
    if path.is_file(): paths[str(path)]=str(path)
paths['time']='/usr/bin/time'
print(json.dumps({name:{'path':p,'sha256':hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()}
                  for name,p in paths.items() if p},sort_keys=True))'''
ARCHITECTURES = {
    'armv7': ('arm7', 'arm7_step'), 'armv8': ('arm8', 'arm8_step'),
    'i386': ('i386', 'x86_step'), 'amd64': ('amd64', 'x64_step'),
    'riscv': ('RISCV', 'r5_step'),
}
PSIMPL = [('psimpl_goal', ''), ('psimpl_hyp', 'h'),
          ('psimpl_exp_goal', 'e'), ('psimpl_exp_hyp', 'e h')]
ISA = [('ISA_step_and_simplify', 'h'), ('ISA_invhere', ''),
       ('ISA_invseek', ''), ('ISA_step', '')]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atomic_json(path, value):
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


@contextmanager
def benchmark_lock():
    # Serialize all harness outputs, and release even on setup/validation errors.
    path = Path('/tmp') / f'picinae-ltac-benchmark-{os.getuid()}.lock'
    with path.open('a') as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError(f'another harness holds {path}') from None
        yield


def selector(arch):
    """Rebind resolved module constants, including all public ISA entry points."""
    module, step = ARCHITECTURES[arch]
    lines = ['\n(* Benchmark only: select the retained Ltac1 graph. *)']
    for prefix, entries in [('PSimpl_' + module, PSIMPL), ('ISA_' + module, ISA)]:
        for name, params in entries:
            lines.append(f'Ltac {prefix}.{name} {params} ::= {prefix}.{name}_ltac1 {params}.')
    lines.append(f'Ltac {step} ::= ISA_{module}.ISA_step_ltac1.')
    return '\n'.join(lines) + '\n'


def select_ltac1(source):
    # Current examples import one architecture. Fail closed if conventions change.
    matches = list(re.finditer(r'(?m)^Require Import Picinae_(\w+)\.', source))
    if len(matches) != 1 or matches[0][1] not in ARCHITECTURES:
        raise ValueError('expected exactly one supported architecture import')
    match = matches[0]
    return source[:match.end()] + selector(match[1]) + source[match.end():]


def selection_probe(arch):
    """Sentinels prove the public syntax reaches each retained entry point.

    Probe sources are separate from the actual byte-checked benchmark copies.
    Nothing is changed in library sources or in real comparison samples.
    """
    module, step = ARCHITECTURES[arch]
    source = f'From Stdlib Require Import NArith.\nRequire Import Picinae_{arch}.\n'
    expected = []
    for prefix, entries in [('PSimpl_' + module, PSIMPL), ('ISA_' + module, ISA)]:
        for name, params in entries:
            token = f'BENCH_SELECTED_{arch}_{name}'
            expected.append(token)
            source += f'Ltac {prefix}.{name}_ltac1 {params} ::= idtac "{token}".\n'
    source += selector(arch)
    source += '''Goal True -> True.
Proof. intro H.
  psimpl. psimpl in H. psimpl (N.add _ 0). psimpl (N.add _ 0) in H.
  ISA_step_and_simplify H. ISA_invhere. ISA_invseek. ISA_step.
'''
    source += f'  {step}. exact H. Qed.\n'
    # The ISA_step sentinel occurs once through ISA_step and once via the alias.
    expected.append(f'BENCH_SELECTED_{arch}_ISA_step')
    return source.encode(), expected


def default_backend_probe(arch):
    """Reject default adapters that still enter a retained Ltac1 controller."""
    module, step = ARCHITECTURES[arch]
    source = f'From Stdlib Require Import NArith.\nRequire Import Picinae_{arch}.\n'
    for prefix, entries in [('PSimpl_' + module, PSIMPL), ('ISA_' + module, ISA)]:
        for name, params in entries:
            source += (f'Ltac {prefix}.{name}_ltac1 {params} ::= '
                       f'fail 1000 "BENCH_DEFAULT_ENTERED_RETAINED_{name}".\n')
    source += f'''Open Scope N_scope.
Goal forall n:N, n + 0 = n.
Proof. intro. psimpl. reflexivity. Qed.
Goal forall n:N, n + 0 = n -> n = n.
Proof. intros n H. psimpl in H. exact H. Qed.
Goal forall n:N, n + 0 = n.
Proof. intro. psimpl (N.add _ 0). reflexivity. Qed.
Goal forall n:N, n + 0 = n -> n = n.
Proof. intros n H. psimpl (N.add _ 0) in H. exact H. Qed.
Goal nextinv (fun _ _ => None) (fun _ => Some True) (fun _ => true) true nil.
Proof. {step}. exact I. Qed.
Goal forall c s c' s' x, exec_stmt c s Nop c' s' x -> True.
Proof. intros c s c' s' x XS. ISA_step_and_simplify XS. exact I. Qed.
'''
    return source.encode()


def example_order(examples):
    """Topologically order the local Require imports in these repository files."""
    by_stem = {p.stem: p for p in examples}
    dependencies = {}
    for path in examples:
        text = re.sub(r'\(\*.*?\*\)', '', path.read_text(), flags=re.S)
        imports = re.findall(r'\bRequire\s+(?:(?:Import|Export)\s+)?([^.]*)\.', text)
        dependencies[path] = {by_stem[word] for clause in imports for word in clause.split()
                              if word in by_stem}
    result = []
    while dependencies:
        ready = sorted(p for p, deps in dependencies.items() if not deps)
        if not ready:
            raise ValueError('cyclic local example dependencies')
        for path in ready:
            result.append(path)
            del dependencies[path]
        for deps in dependencies.values():
            deps.difference_update(ready)
    return result


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--baseline', type=Path, required=True,
                        help='unmodified, wrapper-built source snapshot')
    parser.add_argument('--baseline-revision', default=BASELINE_REVISION)
    parser.add_argument('--runs', type=int, default=3)
    parser.add_argument('--wrapper', type=Path,
                        default=Path('/home/charles/code/friends/.toolchains/picinae-env'))
    parser.add_argument('--phase', choices=['baseline', 'prepare', 'all'], default='all')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--profile', nargs='*', default=None,
                        help='stems to profile separately (default: all eligible proofs; empty: none)')
    parser.add_argument('--outlier-threshold', type=float, default=.15)
    parser.add_argument('--timeout', type=float, default=1800,
                        help='seconds per compilation; failures stop comparison immediately')
    args = parser.parse_args(argv)
    if args.runs < 3:
        parser.error('at least three runs per backend required')
    if args.outlier_threshold <= 0 or args.timeout <= 0:
        parser.error('threshold and timeout must be positive')
    if not args.wrapper.is_file():
        parser.error(f'wrapper is not available: {args.wrapper}')
    return args


class Benchmark:
    def __init__(self, args, root=None):
        self.args = args
        self.root = root or Path(__file__).resolve().parent.parent
        self.baseline = args.baseline.resolve()
        self.out = args.output.resolve()
        self.wrapper = str(args.wrapper.resolve())
        if self.out.is_relative_to(self.root) or self.out.is_relative_to(self.baseline):
            raise ValueError('--output must be outside both library trees')
        self.out.mkdir(parents=True, exist_ok=True)
        self.examples = example_order(sorted((self.root / 'Examples').glob('*.v')))
        if not self.examples:
            raise ValueError('no Examples/*.v inputs found')
        self.proofs = [p for p in self.examples if p.stem.endswith('_proof')]
        if set(p.name for p in self.examples) != set(p.name for p in (self.baseline / 'Examples').glob('*.v')):
            raise ValueError('baseline/current example inventories differ')
        for path in self.examples:
            if path.read_bytes() != (self.baseline / 'Examples' / path.name).read_bytes():
                raise ValueError(f'Example differs from baseline: {path.name}')
        # Validate the snapshot against git objects; it need not be a git checkout.
        self.baseline_revision = self.git('rev-parse', args.baseline_revision + '^{commit}').strip()
        for name in self.git('ls-tree', '-r', '--name-only', self.baseline_revision).splitlines():
            if name.endswith('.v') or name == '_CoqProject':
                original = subprocess.check_output(['git', 'show', f'{self.baseline_revision}:{name}'], cwd=self.root)
                if (self.baseline / name).read_bytes() != original:
                    raise ValueError(f'baseline snapshot differs from revision: {name}')
        self.toolchain = {}
        for name, cmd in [('rocq', ['rocq', '--version']), ('ocaml', ['ocamlc', '-version']),
                          ('packages', ['opam', 'list', '--installed', '--columns=name,version', '--short']),
                          ('config', ['rocq', 'compile', '-config']),
                          ('binaries', ['python3', '-c', BINARY_DIGESTS])]:
            self.toolchain[name] = {'command': [self.wrapper] + cmd,
                                    'output': subprocess.check_output([self.wrapper] + cmd, text=True)}
        fingerprint = {
            'root': str(self.root), 'baseline': str(self.baseline),
            'revision': self.git('rev-parse', 'HEAD').strip(),
            'baseline_revision': self.baseline_revision,
            'wrapper': self.wrapper, 'wrapper_sha256': sha(Path(self.wrapper)),
            'harness_sha256': sha(Path(__file__)), 'toolchain': self.toolchain,
            'runs': args.runs, 'profile': args.profile, 'outlier_threshold': args.outlier_threshold,
            'timeout': args.timeout,
            'inputs': {label: {str(p.relative_to(tree)): sha(p)
                              for p in sorted([*tree.rglob('*.v'), tree / '_CoqProject'])
                              if '.git' not in p.parts and p.is_file()}
                       for label, tree in [('current', self.root), ('baseline', self.baseline)]},
            'libraries': {label: {p.name: sha(p) for p in sorted(tree.glob('*.vo'))}
                          for label, tree in [('current', self.root), ('baseline', self.baseline)]},
        }
        if not fingerprint['libraries']['baseline']:
            raise ValueError('baseline library must be built first through the wrapper')
        state_path = self.out / 'metadata.json'
        if state_path.exists():
            if not args.resume:
                raise ValueError('output already used; pass --resume or choose a fresh directory')
            self.state = json.loads(state_path.read_text())
            if self.state.get('schema') != 2:
                raise ValueError('unsupported checkpoint schema; use a fresh output directory')
            if self.state['fingerprint'] != fingerprint:
                raise ValueError('resume rejected: source/artifact/toolchain/options fingerprint changed')
            for cmd in self.state['commands']:
                if cmd['status'] == 'running':
                    if cmd.get('process_group'):
                        try:
                            os.killpg(cmd['process_group'], 0)
                        except ProcessLookupError:
                            pass
                        else:
                            raise ValueError('prior compiler group still running; stop it before resuming')
                    cmd['status'] = 'interrupted'
        else:
            if args.resume:
                raise ValueError('no checkpoint to resume')
            if any(self.out.iterdir()):
                raise ValueError('fresh output directory must be empty')
            self.state = {'schema': 2, 'fingerprint': fingerprint, 'toolchain': self.toolchain,
                          'machine': platform.node(), 'platform': platform.platform(),
                          'cpu': next((s.split(':', 1)[1].strip() for s in Path('/proc/cpuinfo').read_text().splitlines()
                                       if s.startswith('model name')), 'unknown'),
                          'started_utc': self.utc(), 'start_load': os.getloadavg(),
                          'git_status': self.git('status', '--short'),
                          'commands': [], 'baseline_results': {}, 'outliers': {}, 'phases': []}
        self.save()

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True)

    @staticmethod
    def utc():
        return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())

    def save(self):
        atomic_json(self.out / 'metadata.json', self.state)
        atomic_json(self.out / 'runs.json', [r for r in self.state['commands']
                    if r.get('kind') == 'sample' and r['status'] == 'success'])

    def put_source(self, directory, name, content):
        path = self.out / directory / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if path.exists() and path.read_bytes() != content:
            raise ValueError(f'generated input changed: {path}')
        if not path.exists():
            path.write_bytes(content)
        return path

    def compile(self, tree, source, key, *, kind, expected_failure=False, **fields):
        # Successes can be reused; failures and interrupted commands get new logs.
        for record in reversed(self.state['commands']):
            if record['key'] != key or record['status'] != 'success':
                continue
            if sha(source) != record['source_sha256']:
                raise ValueError(f'generated source changed: {source}')
            if not Path(record['log']).is_file() or sha(Path(record['log'])) != record['log_sha256']:
                raise ValueError(f'completed log missing or changed: {record["log"]}')
            if kind == 'sample' or (source.with_suffix('.vo').is_file()
                                   and sha(source.with_suffix('.vo')) == record.get('vo_sha256')):
                return record
        serial = len(self.state['commands']) + 1
        logs = self.out / 'logs'
        logs.mkdir(exist_ok=True)
        log = logs / f'{serial:04d}-{key}.log'
        timer = log.with_suffix('.time.json')
        cmd = [self.wrapper, '/usr/bin/time', '-o', str(timer), '-f',
               '{"wall":%e,"user":%U,"sys":%S,"rss_kb":%M,"exit_code":%x}',
               'rocq', 'compile', '-R', str(tree), 'Picinae',
               '-Q', str(source.parent), '', str(source)]
        record = dict(key=key, kind=kind, status='running', command=cmd,
                      shell_command=shlex.join(cmd), cwd=str(source.parent),
                      source_sha256=sha(source), log=str(log), timing_log=str(timer),
                      started_utc=self.utc(), load_before=os.getloadavg(), **fields)
        self.state['commands'].append(record)
        self.save()
        start = time.monotonic()
        try:
            with log.open('w') as stream:
                process = subprocess.Popen(cmd, stdout=stream, stderr=subprocess.STDOUT,
                                           cwd=source.parent, start_new_session=True)
                try:
                    record['process_group'] = process.pid
                    self.save()
                    returncode = process.wait(timeout=self.args.timeout)
                except BaseException:
                    # Killing only the wrapper/time PID would leave rocq running.
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    process.wait()
                    raise
            record['exit_code'] = returncode
            record['status'] = 'success' if returncode == 0 else 'failed'
        except BaseException as error:
            record['status'] = 'timeout' if isinstance(error, subprocess.TimeoutExpired) else 'interrupted'
            raise
        finally:
            record.update(outer_seconds=time.monotonic() - start, load_after=os.getloadavg(),
                          finished_utc=self.utc())
            record['log_sha256'] = sha(log)
            lines = timer.read_text().splitlines() if timer.exists() else []
            if lines:
                # GNU time prepends a diagnostic on nonzero exits; JSON is its last line.
                timing = json.loads(lines[-1])
                record.update(compile_seconds=timing['wall'], user_seconds=timing['user'],
                              sys_seconds=timing['sys'], rss_kb=timing['rss_kb'],
                              wrapper_and_launch_seconds=record['outer_seconds'] - timing['wall'])
            if record['status'] == 'success':
                if 'compile_seconds' not in record or not source.with_suffix('.vo').exists():
                    record['status'] = 'invalid'
                else:
                    record['vo_sha256'] = sha(source.with_suffix('.vo'))
            self.save()
        print(key, record['status'], flush=True)
        if record['status'] != 'success' and not expected_failure:
            raise RuntimeError(f'Compilation failed; inspect {log}')
        return record

    def baseline_checks(self):
        for path in self.examples:
            source = self.put_source('baseline', path.name, path.read_bytes())
            # Expected example failures establish exclusion, rather than aborting discovery.
            previous = self.state['baseline_results'].get(path.name)
            if previous is not None and previous['exit_code'] != 0:
                continue
            record = self.compile(self.baseline, source, 'baseline-' + path.stem,
                                  kind='baseline', expected_failure=True)
            if record['status'] not in ('success', 'failed'):
                raise RuntimeError('invalid baseline result')
            self.state['baseline_results'][path.name] = {
                'exit_code': record['exit_code'], 'log': record['log'],
                'partial_correctness_target': path in self.proofs,
            }
            self.save()
        self.eligible = [p for p in self.proofs
                         if self.state['baseline_results'][p.name]['exit_code'] == 0]
        self.state['eligible_proofs'] = [p.name for p in self.eligible]
        self.state['phases'] = sorted(set(self.state['phases'] + ['baseline']))
        self.save()

    def prepare(self):
        if not self.state['fingerprint']['libraries']['current']:
            raise ValueError('current library must be built first through the wrapper')
        for arch in ARCHITECTURES:
            content, expected = selection_probe(arch)
            source = self.put_source('probes', 'select_' + arch + '.v', content)
            record = self.compile(self.root, source, 'probe-' + arch, kind='selection-probe')
            found = re.findall(r'^BENCH_SELECTED_\w+$', Path(record['log']).read_text(), flags=re.M)
            if sorted(found) != sorted(expected):
                raise RuntimeError(f'Ltac1 selection probe failed: {record["log"]}')
            source = self.put_source('probes', 'default_' + arch + '.v', default_backend_probe(arch))
            self.compile(self.root, source, 'default-probe-' + arch, kind='default-backend-probe')
        for backend in ['ltac1', 'ltac2']:
            for path in self.examples:
                content = path.read_bytes()
                if backend == 'ltac1' and (path in self.proofs or path.stem == 'riscv_cfi'):
                    content = select_ltac1(content.decode()).encode()
                source = self.put_source(backend, path.name, content)
                if backend == 'ltac2' and sha(source) != sha(path):
                    raise RuntimeError(f'Ltac2 input changed: {source}')
                # Dependencies and other examples (including CFI safety) are validation,
                # not partial-correctness timings. Proofs compile in the sample pass.
                if path not in self.proofs and self.state['baseline_results'][path.name]['exit_code'] == 0:
                    self.compile(self.root, source, backend + '-validate-' + path.stem,
                                 kind='validation', backend=backend, example=path.stem)
        self.state['phases'] = sorted(set(self.state['phases'] + ['prepare']))
        self.save()

    def sample(self, proof, backend, run):
        self.check_libraries()
        source = self.out / backend / proof.name
        self.compile(self.root, source, f'{proof.stem}-{backend}-{run}', kind='sample',
                     example=proof.stem, backend=backend, run=run)
        self.summarize()

    def check_libraries(self):
        # Catch implementation/rebuild activity between or during comparisons.
        for label, tree in [('current', self.root), ('baseline', self.baseline)]:
            expected = self.state['fingerprint']['libraries'][label]
            if {p.name: sha(p) for p in tree.glob('*.vo')} != expected:
                raise ValueError(f'{label} library artifacts changed during this run')
            for name, digest in self.state['fingerprint']['inputs'][label].items():
                if not (tree / name).is_file() or sha(tree / name) != digest:
                    raise ValueError(f'{label} source changed during this run: {name}')

    def samples(self, proof, backend):
        return [r for r in self.state['commands'] if r['kind'] == 'sample'
                and r['status'] == 'success' and r['example'] == proof.stem and r['backend'] == backend]

    def outliers(self, values):
        median = statistics.median(values)
        if median <= 0:
            raise ValueError('compiler timing resolution too low for this target')
        return [i + 1 for i, value in enumerate(values)
                if abs(value / median - 1) > self.args.outlier_threshold]

    def summarize(self):
        target = self.out / 'medians.csv'
        temporary = target.with_suffix('.tmp')
        with temporary.open('w', newline='') as stream:
            writer = csv.writer(stream)
            writer.writerow(['example', 'ltac1_seconds', 'ltac2_seconds', 'percent_change',
                             'ltac1_outer_seconds', 'ltac2_outer_seconds',
                             'ltac1_wrapper_and_launch_seconds', 'ltac2_wrapper_and_launch_seconds',
                             'ltac1_runs', 'ltac2_runs', 'ltac1_outlier_runs', 'ltac2_outlier_runs'])
            for proof in self.eligible:
                a, b = [self.samples(proof, backend) for backend in ['ltac1', 'ltac2']]
                if min(len(a), len(b)) < self.args.runs:
                    continue
                median_a, median_b = [statistics.median(r['compile_seconds'] for r in group) for group in [a, b]]
                writer.writerow([proof.stem, median_a, median_b, 100 * (median_b / median_a - 1),
                                 *[statistics.median(r[field] for r in group)
                                   for field in ['outer_seconds', 'wrapper_and_launch_seconds'] for group in [a, b]],
                                 len(a), len(b),
                                 *[json.dumps(self.outliers([r['compile_seconds'] for r in group])) for group in [a, b]]])
        temporary.replace(target)

    def measure(self):
        if not self.eligible:
            raise ValueError('no baseline-building partial-correctness examples')
        profiles = self.args.profile
        if profiles is not None and set(profiles) - {p.stem for p in self.eligible}:
            raise ValueError('--profile names must be eligible proof stems')
        for proof in self.eligible:
            for run in range(1, self.args.runs + 1):
                for backend in (['ltac1', 'ltac2'] if run % 2 else ['ltac2', 'ltac1']):
                    self.sample(proof, backend, run)
            # Decide once from the original samples; preserve that decision on resume.
            for backend in ['ltac1', 'ltac2']:
                key = proof.stem + '-' + backend
                if key not in self.state['outliers']:
                    values = [r['compile_seconds'] for r in self.samples(proof, backend)
                              if r['run'] <= self.args.runs]
                    self.state['outliers'][key] = {'initial_runs': self.outliers(values),
                                                  'reruns': 2 if self.outliers(values) else 0}
                    self.save()
                for extra in range(1, self.state['outliers'][key]['reruns'] + 1):
                    self.sample(proof, backend, self.args.runs + extra)
        self.state['phases'] = sorted(set(self.state['phases'] + ['measure']))
        self.save()
        # Profile in different directories; never overwrite a timed input or .vo.
        for proof in self.eligible:
            if profiles is not None and proof.stem not in profiles:
                continue
            for backend in ['ltac1', 'ltac2']:
                directory = 'profiles/' + backend
                for dependency in self.examples:
                    if dependency in self.proofs or dependency.stem == 'riscv_cfi':
                        continue
                    source = self.put_source(directory, dependency.name, dependency.read_bytes())
                    if self.state['baseline_results'][dependency.name]['exit_code'] == 0:
                        self.compile(self.root, source, f'profile-dep-{backend}-{dependency.stem}', kind='profile-dependency')
                content = (b'From Ltac2 Require Import Ltac2.\nSet Default Proof Mode "Classic".\n'
                           b'Set Ltac2 In Ltac1 Profiling.\nSet Ltac Profiling.\n'
                           + (self.out / backend / proof.name).read_bytes() + b'\nShow Ltac Profile.\n')
                source = self.put_source(directory, proof.name, content)
                self.compile(self.root, source, f'profile-{backend}-{proof.stem}', kind='profile',
                             example=proof.stem, backend=backend)
        self.state['phases'] = sorted(set(self.state['phases'] + ['profiles']))
        self.check_libraries()
        self.state.update(end_load=os.getloadavg(), finished_utc=self.utc())
        self.save()

    def run(self):
        self.baseline_checks()
        if self.args.phase == 'baseline':
            return
        self.prepare()
        if self.args.phase == 'all':
            self.measure()


def main():
    try:
        args = parse_args()
        with benchmark_lock():
            Benchmark(args).run()
    except (ValueError, RuntimeError, subprocess.SubprocessError) as error:
        raise SystemExit(str(error)) from error


if __name__ == '__main__':
    main()
