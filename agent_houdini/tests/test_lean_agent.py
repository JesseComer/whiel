"""Focused unit gates and opt-in real CLI/bwrap/Lean smoke tests (no model calls)."""

import argparse
import asyncio
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import shutil
import shlex
import sys
import tempfile
import threading
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from agent_houdini.lean_agent import (check, execute, prepare, run, sandbox_command,
                                    seconds_arg, submission, validate_sources)
from agent_houdini.stop import Stop


class LeanAgentTests(unittest.TestCase):
    def test_completed_output_is_not_marked_capture_failed(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            (out / 'native/sessions').mkdir(parents=True)
            result = asyncio.run(execute(
                [sys.executable, '-c', 'print("retained output")'], out, b'', 5))
            self.assertEqual(result['stop_reason'], 'exited')
            self.assertEqual((out / 'native-stdout.jsonl').read_text(), 'retained output\n')
            self.assertFalse(result['capture_failed'], result)

    def test_budget_is_capped(self):
        self.assertEqual(seconds_arg('600'), 600)
        self.assertIsNone(seconds_arg('unlimited'))
        self.assertIsNone(seconds_arg(None))
        for value in ('0', '-1', '601', 'nan', 'inf'):
            with self.assertRaises(argparse.ArgumentTypeError):
                seconds_arg(value)

    def test_unlimited_agent_exits_and_can_be_cancelled(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for interrupted in (False, True):
                with self.subTest(interrupted=interrupted):
                    out = root / str(interrupted)
                    (out / 'native/sessions').mkdir(parents=True)
                    async def run_child():
                        stop = Stop()
                        if interrupted:
                            asyncio.get_running_loop().call_later(.2, stop.set, 'interrupted')
                        code = 'import time; time.sleep(30)' if interrupted else 'print("finished")'
                        with patch('agent_houdini.lean_agent.Stop', return_value=stop):
                            return await asyncio.wait_for(execute(
                                [sys.executable, '-c', code], out, b'', None), timeout=5)
                    result = asyncio.run(run_child())
                    self.assertIsNone(result['agent_limit_seconds'])
                    self.assertEqual(result['stop_reason'], 'interrupted' if interrupted else 'exited')
                    self.assertFalse(result['capture_failed'])

    def test_final_saved_files_and_symlink_rejection(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            (work / 'verdict.txt').write_text('invalid\n')
            (work / 'Solution.lean').write_text('by contradiction\n')
            self.assertEqual(submission(work), {'verdict': 'invalid', 'source': 'by contradiction\n'})
            (work / 'Solution.lean').unlink()
            (work / 'Solution.lean').symlink_to(work / 'verdict.txt')
            with self.assertRaises(OSError):
                submission(work)

    def test_source_snapshot_rejects_extra_answers_and_changes(self):
        with tempfile.TemporaryDirectory() as directory:
            bundle = Path(directory)
            source = bundle / 'lib-src/Whiel'
            source.mkdir(parents=True)
            (source / 'Semantics.lean').write_text('trusted generic source')
            index = {'files': {'Whiel/Semantics.lean': hashlib.sha256(b'trusted generic source').hexdigest()}}
            (bundle / 'source-manifest.json').write_text(json.dumps(index))
            manifest = {'libraries': [{'path': 'Whiel/Semantics.olean'}]}
            validate_sources(bundle, manifest)
            (source / 'Answer.lean').write_text('unlisted answer')
            with self.assertRaises(ValueError):
                validate_sources(bundle, manifest)
            (source / 'Answer.lean').unlink()
            (source / 'Semantics.lean').write_text('changed')
            with self.assertRaises(ValueError):
                validate_sources(bundle, manifest)


INTEGRATION = all(os.environ.get(key) for key in
                  ('WHIEL_LEAN_AGENT_TEST_BUNDLE', 'WHIEL_LEAN_AGENT_TEST_CHECKER',
                   'WHIEL_LEAN_AGENT_TEST_CLI'))


@unittest.skipUnless(INTEGRATION, 'set WHIEL_LEAN_AGENT_TEST_* for the real offline smoke tests')
class NativeLeanAgentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        source_bundle = Path(os.environ['WHIEL_LEAN_AGENT_TEST_BUNDLE']).resolve()
        cls.checker = Path(os.environ['WHIEL_LEAN_AGENT_TEST_CHECKER']).resolve()
        cls.cli = Path(os.environ['WHIEL_LEAN_AGENT_TEST_CLI']).resolve()
        cls.model = os.environ.get('WHIEL_LEAN_AGENT_TEST_MODEL', 'gpt-5.5')
        cls.effort = os.environ.get('WHIEL_LEAN_AGENT_TEST_EFFORT', 'medium')
        # A synthetic task uses the prepared library but no paper-task answer.
        cls.case = 'Toy'
        if os.environ.get('WHIEL_LEAN_AGENT_TEST_OUT'):
            cls.root = Path(os.environ['WHIEL_LEAN_AGENT_TEST_OUT']).resolve()
            cls.root.mkdir(mode=0o700)
        else:
            cls.root = Path(tempfile.mkdtemp(prefix='lean-agent-smoke-', dir='/tmp'))
        cls.bundle = cls.root / 'bundle'
        cls.bundle.mkdir()
        shutil.copy2(Path(__file__).resolve().parents[2] / 'Whiel/DirectLean/Audit.lean',
                     cls.bundle / 'Audit.lean')
        task = '''import Whiel.Concrete.Notation
import Whiel.Hoare.Concrete
namespace DirectLeanTask
open Whiel Whiel.Concrete
def inputSchema : UnnamedSchema ProgramNames := programSch![{R} (arity: 1)]
def inputPre : AssertExpr Data inputSchema := programAssert![true]
def inputCmd : Cmd Data inputSchema := .skip
def inputPost : AssertExpr Data inputSchema := programAssert![true]
def goal : Prop := HoareValid inputPre inputCmd inputPost
end DirectLeanTask
'''
        (cls.bundle / cls.case).mkdir()
        (cls.bundle / cls.case / 'Task.lean').write_text(task)
        manifest = json.loads((source_bundle / 'bundle.json').read_text())
        manifest['audit_sha256'] = hashlib.sha256((cls.bundle / 'Audit.lean').read_bytes()).hexdigest()
        manifest['cases'] = [{'id': cls.case, 'task_sha256': hashlib.sha256(task.encode()).hexdigest()}]
        (cls.bundle / 'bundle.json').write_text(json.dumps(manifest))
        (cls.bundle / 'lib').symlink_to(source_bundle / 'lib', target_is_directory=True)
        (cls.bundle / 'reference.txt').write_text('Offline fixture: inspect /task/Task.lean.\n')
        if (source_bundle / 'lib-src').is_dir():
            shutil.copytree(source_bundle / 'lib-src', cls.bundle / 'lib-src')
            shutil.copy2(source_bundle / 'source-manifest.json', cls.bundle / 'source-manifest.json')
        print('Retained smoke evidence:', cls.root, flush=True)

    def test_native_compile_error_then_repair(self):
        model, effort = self.model, self.effort
        requests = []
        outputs = []
        failures = []
        commands = [
            f'test ! -e {shlex.quote(str(Path(__file__).resolve().parents[2]))} || exit 80; '
            'test ! -e /Audit.lean || exit 83; '
            'test ! -e /library/Benchmark || exit 84; '
            'test ! -e /library/Whiel/Synthesis || exit 85; '
            'test ! -e /library/VampLean || exit 86; '
            'test ! -e /library/Whiel/Hoare/Preproc.olean || exit 87; '
            'if command -v vampire; then exit 88; fi; '
            'if test -d /library-src; then test -f /library-src/Whiel/Hoare/Abstract.lean || exit 89; fi; '
            'if echo tamper >> /task/Task.lean; then exit 81; fi; '
            'printf "import Task\\nopen Whiel Whiel.Concrete\\n'
            'theorem DirectLeanTask.answer : DirectLeanTask.goal := by exact (0 : Nat)\\n" '
            '> Solution.lean; lean Solution.lean',
            'printf "import Task\\nopen Whiel Whiel.Concrete\\n'
            'theorem helper : DirectLeanTask.goal := by intro I J h hs; cases hs; exact h\\n'
            'theorem DirectLeanTask.answer : DirectLeanTask.goal := helper\\n" '
            '> Solution.lean; lean Solution.lean',
        ]

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *_args):
                pass

            def do_POST(self):
                try:
                    request = json.loads(self.rfile.read(int(self.headers['Content-Length'])))
                    requests.append(request)
                    index = len(requests) - 1
                    tools = {t.get('name', t.get('type')) for t in request.get('tools', [])}
                    if index == 0:
                        assert tools == {'exec_command', 'write_stdin'}, tools
                        assert request['model'] == model, request['model']
                        assert request['reasoning']['effort'] == effort, request.get('reasoning')
                    previous = [i for i in request.get('input', [])
                                if i.get('type') == 'function_call_output']
                    outputs.extend(previous)
                    if index < 2:
                        cmd = commands[index]
                        if index == 0:
                            network_probe = (
                                'import socket,sys\n'
                                'try:\n'
                                f' s=socket.create_connection(("127.0.0.1",{server.server_port}),timeout=1)\n'
                                'except OSError:\n print("NETWORK_BLOCKED")\n'
                                'else:\n s.close(); print("NETWORK_LEAK"); sys.exit(82)\n')
                            import shlex
                            cmd = 'python3 -c ' + shlex.quote(network_probe) + ' && ' + cmd
                        item = {'id': f'fc_{index}', 'type': 'function_call',
                                'call_id': f'call_{index}', 'name': 'exec_command',
                                'arguments': json.dumps({'cmd': cmd,
                                    'yield_time_ms': 10000, 'max_output_tokens': 2000})}
                    else:
                        item = {'id': 'msg_final', 'type': 'message', 'role': 'assistant',
                                'phase': 'final_answer', 'content': [{'type': 'output_text',
                                 'text': 'Saved and compiled the repaired proof.', 'annotations': []}]}
                    events = [
                        {'type': 'response.output_item.added', 'output_index': 0, 'item': item},
                        {'type': 'response.output_item.done', 'output_index': 0, 'item': item},
                        {'type': 'response.completed', 'response': {
                            'id': f'resp_{index}', 'object': 'response', 'status': 'completed',
                            'output': [item], 'usage': {'input_tokens': 100,
                                'input_tokens_details': {'cached_tokens': 0}, 'output_tokens': 30,
                                'output_tokens_details': {'reasoning_tokens': 10}, 'total_tokens': 130}}},
                    ]
                    body = ''.join('event: '+e['type']+'\ndata: '+json.dumps(e)+'\n\n'
                                   for e in events).encode()
                    self.send_response(200)
                    self.send_header('Content-Type', 'text/event-stream')
                    self.send_header('Content-Length', str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)
                except Exception as error:
                    failures.append(repr(error))
                    self.send_error(500)

        server = ThreadingHTTPServer(('127.0.0.1', 0), Handler)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        out = self.root / 'native-repair'
        try:
            args = SimpleNamespace(bundle=self.bundle, checker=self.checker, cli=self.cli,
                auth_home=None, out=out, case=self.case, model=model,
                reasoning_effort=effort, seconds=45,
                model_catalog=Path(os.environ['WHIEL_LEAN_AGENT_TEST_CATALOG'])
                if os.environ.get('WHIEL_LEAN_AGENT_TEST_CATALOG') else None)
            result = run(args, fixture_url=f'http://127.0.0.1:{server.server_port}')
        finally:
            server.shutdown()
            server.server_close()
            thread.join()
            (out / 'fixture-requests.json').write_text(json.dumps(requests, indent=2))
        self.assertFalse(failures, failures)
        self.assertEqual(len(requests), 3, result)
        self.assertIn('type mismatch', json.dumps(outputs).lower())
        self.assertIn('NETWORK_BLOCKED', json.dumps(outputs))
        self.assertNotIn('NETWORK_LEAK', json.dumps(outputs))
        self.assertIn('read-only file system', json.dumps(outputs).lower())
        self.assertTrue(result['proof_checked'], result)
        self.assertFalse(result['capture_failed'], result)
        self.assertEqual(result['stop_reason'], 'exited')
        self.assertEqual(result['usage']['coverage'], 'complete')
        self.assertGreaterEqual(result['usage']['snapshots'], 2)

    def test_deadline_kills_detached_children(self):
        out = self.root / 'deadline'
        manifest = prepare(self.bundle, self.case, self.checker, out)
        code = ('import subprocess,time; from pathlib import Path; '
                'Path("/workspace/started").write_text("started"); '
                'subprocess.Popen(["/bin/sh","-c","sleep 2; echo leaked > /workspace/escaped"],'
                'start_new_session=True); time.sleep(20)')
        argv = sandbox_command(self.bundle, out, Path(manifest['lean']),
                               ['/usr/bin/python3', '-c', code])
        result = asyncio.run(execute(argv, out, b'', .5))
        self.assertTrue((out / 'workspace/started').exists(), result)
        self.assertEqual(result['stop_reason'], 'deadline')
        self.assertLess(result['agent_seconds'], 2)
        time.sleep(2.5)
        self.assertFalse((out / 'workspace/escaped').exists())

    def test_independent_checker_rejects_sorry(self):
        out = self.root / 'reject-sorry'
        out.mkdir()
        (out / 'response.json').write_text(json.dumps({'verdict': 'valid', 'source':
            'import Task\ntheorem DirectLeanTask.answer : DirectLeanTask.goal := by sorry\n'}))
        result = check(self.checker, self.bundle, self.case, out / 'response.json', out / 'check')
        self.assertFalse(result['proof_checked'])
        self.assertEqual(result['failure_stage'], 'audit')


if __name__ == '__main__':
    unittest.main()
