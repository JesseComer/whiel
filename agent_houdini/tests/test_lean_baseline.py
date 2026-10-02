"""Campaign orchestration gates with synthetic worker processes, no model calls."""

import json
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from agent_houdini.lean_baseline import case_command, dispatch, outcome, prepare_bundle, resolve_run, summarize
from agent_houdini.lean_baseline_utils import read_bounded, save, sha, worker_homes


class LeanBaselineTests(unittest.TestCase):
    def test_records_are_exclusive_and_bounded(self):
        with tempfile.TemporaryDirectory() as temporary:
            p = Path(temporary) / 'record.json'
            save(p, {'saved': True})
            with self.assertRaises(FileExistsError):
                save(p, {'overwritten': True})
            with self.assertRaises(ValueError):
                read_bounded(p, 1)
            self.assertTrue(json.loads(p.read_text())['saved'])

    def test_distinct_worker_auth_without_reading_secrets(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for slot in (1, 2):
                home = root / f'worker-{slot}'
                home.mkdir(mode=0o700)
                (home / 'auth.json').write_text('opaque fixture, never parsed')
                (home / 'auth.json').chmod(0o600)
            self.assertEqual(len(worker_homes(root, 2)), 2)
            (root / 'worker-2/auth.json').unlink()
            os.link(root / 'worker-1/auth.json', root / 'worker-2/auth.json')
            with self.assertRaises(ValueError):
                worker_homes(root, 2)

    def test_prepare_copies_only_compiled_generic_sources(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'Whiel').mkdir()
            (root / 'Whiel/Semantics.lean').write_text('generic source')
            (root / 'Whiel/Answer.lean').write_text('not in import closure')
            bundle = root / 'bundle'
            def fake_export(*_args, **_kwargs):
                bundle.mkdir()
                (bundle / 'bundle.json').write_text(json.dumps({'libraries': [
                    {'path': 'Whiel/Semantics.olean'}, {'path': 'Mathlib/Data/Set.olean'}]}))
            with patch('agent_houdini.lean_baseline.ROOT', root), \
                    patch('agent_houdini.lean_baseline.selected_inputs', return_value=['Example0001']), \
                    patch('agent_houdini.lean_baseline.subprocess.run', side_effect=fake_export):
                prepare_bundle(root / 'checker', bundle)
            self.assertEqual((bundle / 'lib-src/Whiel/Semantics.lean').read_text(), 'generic source')
            self.assertFalse((bundle / 'lib-src/Whiel/Answer.lean').exists())
            index = json.loads((bundle / 'source-manifest.json').read_text())['files']
            self.assertEqual(index, {'Whiel/Semantics.lean': sha(b'generic source')})

    def fixture_pool(self, root, cases, jobs):
        config = {'cases': cases, 'jobs': jobs, 'out': str(root)}
        (root / 'cases').mkdir()
        (root / 'launch-logs').mkdir()
        (root / 'run.json').write_text(json.dumps(config))
        return config

    def test_parallel_slots_continue_after_proof_and_memory_failure(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config = self.fixture_pool(root, ['Memory', 'Reject', 'Pass', 'Again'], 2)
            def command(config, slot, case):
                result = {'status': 'check_failed', 'proof_checked': False,
                          'usage': {'coverage': 'complete', 'cumulative': {
                              'input_tokens': 100, 'cached_input_tokens': 60,
                              'output_tokens': 20, 'reasoning_output_tokens': 10,
                              'total_tokens': 120}}}
                if case == 'Pass':
                    result.update(status='valid_proof_checked', proof_checked=True)
                if case == 'Memory':
                    result.update(status='agent_failed', exit_code=137)
                code = ('import json,sys,time; from pathlib import Path; '
                        'p=Path(sys.argv[1]); p.mkdir(); '
                        '(p/"result.json").write_text(sys.argv[2]); '
                        '(p/"native-stderr.txt").write_text('
                        '"WATCHDOG: killing 123 at 4500000 KB RSS (limit 4194304 KB)"); '
                        'time.sleep(.1)')
                return [sys.executable, '-c', code, str(root / 'cases' / case), json.dumps(result)]
            self.assertEqual(dispatch(config, command), 0)
            summary = summarize(root)
            self.assertEqual(summary['finished'], 4)
            self.assertEqual(summary['outcomes'], {'memory_limit': 1, 'proof_rejected': 2, 'accepted': 1})
            self.assertEqual(summary['observed_tokens']['total_tokens'], 480)
            starts = [json.loads(p.read_text()) for p in (root / 'launch-logs').glob('*.started.json')]
            self.assertEqual(len(starts), 4)
            self.assertEqual({s['slot'] for s in starts}, {1, 2})

    def test_final_check_timeout_does_not_stop_pending_cases(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config = self.fixture_pool(root, ['Timeout', 'Next'], 1)
            def command(config, slot, case):
                result = {'status': 'check_timeout' if case == 'Timeout' else 'check_failed',
                          'proof_checked': False}
                code = ('import sys; from pathlib import Path; '
                        'p=Path(sys.argv[1]); p.mkdir(); '
                        '(p/"result.json").write_text(sys.argv[2]); '
                        'sys.exit(1)')
                return [sys.executable, '-c', code, str(root / 'cases' / case), json.dumps(result)]
            self.assertEqual(dispatch(config, command), 0)
            summary = summarize(root)
            self.assertEqual(summary['finished'], 2)
            self.assertEqual(summary['outcomes'], {'proof_rejected': 2})
            self.assertEqual(json.loads((root / 'cases/Timeout/result.json').read_text())['status'],
                             'check_timeout')

    def test_infrastructure_failure_stops_dispatch_without_retry(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config = self.fixture_pool(root, ['First', 'Never'], 1)
            def command(config, slot, case):
                return [sys.executable, '-c', 'raise SystemExit(2)']
            self.assertEqual(dispatch(config, command), 2)
            self.assertFalse((root / 'launch-logs/Never.started.json').exists())
            self.assertEqual(summarize(root)['finished'], 1)
            # Exit 137 alone must not hide authentication/CLI/infrastructure failures.
            self.assertEqual(outcome(root, {'status': 'agent_failed', 'exit_code': 137}),
                             'infrastructure_failure')

    def test_dry_run_never_calls_provider_or_creates_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            bundle = root / 'bundle'
            (bundle / 'Example0001').mkdir(parents=True)
            (bundle / 'lib-src').mkdir()
            (bundle / 'source-manifest.json').write_text('{"files": {}}')
            (bundle / 'reference.txt').write_text('reference')
            (bundle / 'Example0001/Task.lean').write_text('task')
            manifest = {'cases': [{'id': 'Example0001', 'task_sha256': sha(b'task')}],
                        'reference_sha256': sha(b'reference'), 'libraries': []}
            (bundle / 'bundle.json').write_text(json.dumps(manifest))
            spec = root / 'spec.json'
            args = SimpleNamespace(spec=spec, bundle=bundle, jobs=1, auth_root=root,
                                   out=root / 'out', checker=Path(sys.executable))
            for seconds in (600, None):
                with self.subTest(seconds=seconds):
                    spec.write_text(json.dumps({'model': 'caller-model',
                        'reasoning_effort': 'caller-effort', 'provider_cli': sys.executable,
                        'agent_seconds': seconds}))
                    with patch('agent_houdini.lean_baseline.worker_homes', return_value=[root]), \
                            patch('agent_houdini.lean_baseline.subprocess.run') as subprocess_run:
                        config = resolve_run(args)
                    subprocess_run.assert_not_called()
                    self.assertEqual(config['spec']['model'], 'caller-model')
                    self.assertEqual(config['spec']['reasoning_effort'], 'caller-effort')
                    self.assertEqual(config['spec']['agent_seconds'], seconds)
                    command = case_command(config, 1, 'Example0001')
                    value = command[command.index('--seconds') + 1]
                    self.assertEqual(value, 'unlimited' if seconds is None else '600.0')
                    self.assertFalse(args.out.exists())


if __name__ == '__main__':
    unittest.main()
