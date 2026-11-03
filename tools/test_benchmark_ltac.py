"""Harness bookkeeping checks; fake compilers never collect performance data."""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import Mock, patch

SPEC = importlib.util.spec_from_file_location('benchmark_ltac', Path(__file__).with_name('benchmark_ltac.py'))
bench = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(bench)


class HarnessTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix='picinae-harness-test-')
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)
        self.b = bench.Benchmark.__new__(bench.Benchmark)
        self.b.out = self.root
        self.b.wrapper = '/fake/wrapper'
        self.b.args = argparse.Namespace(timeout=10, runs=3, outlier_threshold=.15, profile=[])
        self.b.state = {'commands': [], 'outliers': {}, 'phases': []}
        self.source = self.root / 'example.v'
        self.source.write_text('Goal True. exact I. Qed.\n')

    def fake_compiler(self, returncode=0):
        def launch(command, **kwargs):
            self.source.with_suffix('.vo').write_bytes(b'compiled fixture')
            Path(command[3]).write_text(json.dumps({'wall': 1.0, 'user': .8, 'sys': .1, 'rss_kb': 5, 'exit_code': returncode}))
            kwargs['stdout'].write('fake compiler\n')
            return Mock(pid=123, wait=Mock(return_value=returncode))
        return launch

    def test_selection_rebinds_all_resolved_entries(self):
        for arch, (module, alias) in bench.ARCHITECTURES.items():
            content = f'Require Import Picinae_{arch}.\nGoal True. exact I. Qed.\n'
            selected = bench.select_ltac1(content)
            for prefix, entries in [('PSimpl_' + module, bench.PSIMPL), ('ISA_' + module, bench.ISA)]:
                for name, _ in entries:
                    self.assertIn(f'Ltac {prefix}.{name} ', selected)
                    self.assertIn(f'::= {prefix}.{name}_ltac1', selected)
            self.assertIn(f'Ltac {alias} ::= ISA_{module}.ISA_step_ltac1.', selected)
            probe, tokens = bench.selection_probe(arch)
            self.assertEqual(len(tokens), 9)
            self.assertEqual(tokens.count(f'BENCH_SELECTED_{arch}_ISA_step'), 2)
            self.assertIn(bench.selector(arch).encode(), probe)
            default = bench.default_backend_probe(arch).decode()
            self.assertIn(f'Proof. {alias}. exact I. Qed.', default)
            self.assertIn('BENCH_DEFAULT_ENTERED_RETAINED_psimpl_goal', default)
            self.assertNotIn('select the retained Ltac1 graph', default)
        for source in ['', 'Require Import Picinae_unknown.',
                       'Require Import Picinae_i386.\nRequire Import Picinae_armv7.']:
            with self.assertRaises(ValueError):
                bench.select_ltac1(source)

    def test_local_dependency_order(self):
        a, b = self.root / 'a.v', self.root / 'b.v'
        a.write_text('Require Import b.\n')
        b.write_text('')
        self.assertEqual(bench.example_order([a, b]), [b, a])
        b.write_text('Require Import a.\n')
        with self.assertRaises(ValueError):
            bench.example_order([a, b])

    def test_success_resume_and_log_integrity(self):
        with patch.object(bench.subprocess, 'Popen', side_effect=self.fake_compiler()) as compiler:
            first = self.b.compile(self.root, self.source, 'one', kind='sample')
            self.assertIs(first, self.b.compile(self.root, self.source, 'one', kind='sample'))
            compiler.assert_called_once()
        self.assertEqual(first['compile_seconds'], 1)
        self.assertIn('wrapper_and_launch_seconds', first)
        self.assertEqual(json.loads((self.root / 'runs.json').read_text())[0]['key'], 'one')
        Path(first['log']).write_text('changed')
        with self.assertRaisesRegex(ValueError, 'log missing or changed'):
            self.b.compile(self.root, self.source, 'one', kind='sample')

    def test_fail_fast_and_unique_retry_logs(self):
        with patch.object(bench.subprocess, 'Popen', side_effect=self.fake_compiler(1)):
            with self.assertRaisesRegex(RuntimeError, 'Compilation failed'):
                self.b.compile(self.root, self.source, 'fail', kind='sample')
            expected = self.b.compile(self.root, self.source, 'fail', kind='baseline', expected_failure=True)
        self.assertEqual(expected['exit_code'], 1)
        self.assertNotEqual(self.b.state['commands'][0]['log'], expected['log'])
        self.assertEqual(json.loads((self.root / 'runs.json').read_text()), [])

    def test_timeout_stops_entire_compiler_group(self):
        process = Mock(pid=123, wait=Mock(side_effect=[subprocess.TimeoutExpired('rocq', 10), -9]))
        def launch(command, **kwargs):
            Path(command[3]).write_text('')  # time opens this before starting rocq
            return process
        with patch.object(bench.subprocess, 'Popen', side_effect=launch), patch.object(bench.os, 'killpg') as kill:
            with self.assertRaises(subprocess.TimeoutExpired):
                self.b.compile(self.root, self.source, 'timeout', kind='sample')
            kill.assert_called_once_with(123, bench.signal.SIGKILL)
        self.assertEqual(self.b.state['commands'][0]['status'], 'timeout')

    def test_outlier_reruns_medians_and_separate_profiles(self):
        self.b.eligible = [self.source]
        self.b.examples = []
        self.b.sample = Mock()
        self.b.check_libraries = Mock()
        def sample(proof, backend, run):
            value = [1, 1, 2, 1, 1][run - 1] if backend == 'ltac1' else 2
            self.b.state['commands'].append(dict(kind='sample', status='success', example=proof.stem,
                backend=backend, run=run, compile_seconds=value, outer_seconds=value + .1,
                wrapper_and_launch_seconds=.1))
        self.b.sample.side_effect = sample
        self.b.measure()
        self.assertEqual(len(self.b.samples(self.source, 'ltac1')), 5)
        self.assertEqual(len(self.b.samples(self.source, 'ltac2')), 3)
        self.assertEqual(self.b.state['outliers']['example-ltac1']['initial_runs'], [3])
        self.b.summarize()
        lines = (self.root / 'medians.csv').read_text().splitlines()
        self.assertIn('example,1,2,100.0', lines[1])
        self.assertEqual([call.args[1:] for call in self.b.sample.call_args_list[:6]],
                         [('ltac1', 1), ('ltac2', 1), ('ltac2', 2), ('ltac1', 2), ('ltac1', 3), ('ltac2', 3)])
        self.assertEqual(self.b.state['phases'], ['measure', 'profiles'])

    def test_resume_rejects_changed_fingerprint(self):
        root, base, output = [self.root / name for name in ['current', 'baseline', 'output']]
        wrapper = self.root / 'wrapper'
        wrapper.write_text('fixture')
        for tree in [root, base]:
            (tree / 'Examples').mkdir(parents=True)
            (tree / 'Examples' / 'example_proof.v').write_text('fixture')
            (tree / 'library.vo').write_text('fixture')
        args = argparse.Namespace(baseline=base, output=output, wrapper=wrapper, baseline_revision='base',
                                  runs=3, profile=[], outlier_threshold=.15, timeout=10, resume=False)
        def git(*args):
            return 'Examples/example_proof.v\n' if args[0] == 'ls-tree' else 'revision\n'
        def capture(command, **kwargs):
            return b'fixture' if command[0] == 'git' else 'toolchain'
        with patch.object(bench.Benchmark, 'git', side_effect=git), patch.object(bench.subprocess, 'check_output', side_effect=capture):
            first = bench.Benchmark(args, root=root)
            args.resume = True
            resumed = bench.Benchmark(args, root=root)
            self.assertEqual(first.state['fingerprint'], resumed.state['fingerprint'])
            resumed.state['commands'].append(dict(kind='validation', status='running', process_group=123))
            resumed.save()
            with patch.object(bench.os, 'killpg'):
                with self.assertRaisesRegex(ValueError, 'compiler group still running'):
                    bench.Benchmark(args, root=root)
            with patch.object(bench.os, 'killpg', side_effect=ProcessLookupError):
                recovered = bench.Benchmark(args, root=root)
            self.assertEqual(recovered.state['commands'][0]['status'], 'interrupted')
            (root / 'library.vo').write_text('changed')
            with self.assertRaisesRegex(ValueError, 'fingerprint changed'):
                bench.Benchmark(args, root=root)

    def test_profiles_do_not_modify_measured_sources(self):
        self.b.root = self.root
        self.b.eligible, self.b.examples = [self.source], []
        self.b.args.profile = None
        self.b.check_libraries = Mock()
        self.b.compile = Mock()
        def sample(proof, backend, run):
            self.b.state['commands'].append(dict(kind='sample', status='success', example=proof.stem,
                backend=backend, run=run, compile_seconds=1, outer_seconds=1.1, wrapper_and_launch_seconds=.1))
        self.b.sample = sample
        for backend in ['ltac1', 'ltac2']:
            self.b.put_source(backend, self.source.name, self.source.read_bytes())
        self.b.measure()
        self.assertEqual(self.b.compile.call_count, 2)
        for call in self.b.compile.call_args_list:
            profile = call.args[1]
            self.assertIn('profiles', profile.parts)
            self.assertEqual(call.kwargs['kind'], 'profile')
            self.assertIn('Set Ltac2 In Ltac1 Profiling.', profile.read_text())
        for backend in ['ltac1', 'ltac2']:
            self.assertEqual((self.root / backend / self.source.name).read_bytes(), self.source.read_bytes())
        self.assertEqual(len(json.loads((self.root / 'runs.json').read_text())), 6)

    def test_byte_copies_preserve_line_endings_and_reject_edits(self):
        data = b'(* example *)\r\nGoal True.\r\n'
        copied = self.b.put_source('ltac2', 'copy.v', data)
        self.assertEqual(copied.read_bytes(), data)
        copied.write_bytes(data + b'edit')
        with self.assertRaisesRegex(ValueError, 'generated input changed'):
            self.b.put_source('ltac2', 'copy.v', data)

    def test_default_backend_failure_stops_preparation_before_measurement(self):
        self.b.root = self.root
        self.b.args.phase = 'all'
        self.b.state['fingerprint'] = {'libraries': {'current': {'library.vo': 'fixture'}}}
        self.b.baseline_checks = Mock()
        self.b.measure = Mock()
        log = self.root / 'selection.log'
        log.write_text('\n'.join(bench.selection_probe('armv7')[1]))
        self.b.compile = Mock(side_effect=[{'log': str(log)}, RuntimeError('retained default detected')])
        with self.assertRaisesRegex(RuntimeError, 'retained default detected'):
            self.b.run()
        self.b.measure.assert_not_called()
        self.assertEqual(self.b.compile.call_args_list[-1].kwargs['kind'], 'default-backend-probe')

    def test_global_lock_blocks_parallel_harnesses_and_releases(self):
        with bench.benchmark_lock():
            with self.assertRaisesRegex(ValueError, 'another harness holds'):
                with bench.benchmark_lock():
                    self.fail('lock must exclude another process/output directory')
        with bench.benchmark_lock():
            pass


if __name__ == '__main__':
    unittest.main()
