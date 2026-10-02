"""Minimal sandboxed Lean coding agent with an optional wall-time limit.

Independent of the Houdini proposer; uses the native launcher, process cleanup,
records and standalone Rust/Lean proof checker.
"""

import argparse
import asyncio
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import time
from urllib.parse import urlparse

from .bwrap import (SYSTEM_READONLY_PATHS, SYSTEM_READONLY_BINDINGS,
                    acquire_auth_lock, child_environment, private_file)
from .lean_baseline_utils import RESPONSE_BYTES, read_bounded, save, sha
from .process_tree import OwnedProcess
from .provider_runtime import native_identity_fields
from .providers.codex import launch_command, verify
from .run_records import ConsultationRecord
from .stop import Stop
from .token_usage import RolloutUsage

ROOT = Path(__file__).resolve().parents[1]
MAX_SECONDS = 600
PROMPT = '''Prove DirectLeanTask.goal from /task/Task.lean, or prove its negation.

Library reference: /reference.txt. Generic library sources: /library-src, if
present. Whiel/Databases semantics and generic proof lemmas are available; Houdini,
Whiel preprocessing and synthesis automation, Vampire, skills and the query API
are unavailable. No reference answers or other benchmark tasks are available.

The task and libraries are read-only; /workspace is writable. Shell commands
and the Lean compiler are available, with no tool network access. Dependencies
are already built; `lean <file>` compiles a Lean file.

Submit /workspace/Solution.lean as a complete Lean file importing Task. It may
include helper definitions and lemmas. Its theorem DirectLeanTask.answer must
prove DirectLeanTask.goal (valid) or its negation (invalid). Write valid or
invalid to /workspace/verdict.txt. Only these two files are collected; the final
chat message is not a submission.

Acceptance requires independent checking against the original goal. Classical
reasoning and native_decide are permitted. sorry, admit and unproved custom
axioms are not permitted; native_decide computations are independently checked.
'''


def seconds_arg(raw):
    if raw is None or raw == 'unlimited':
        return None
    value = float(raw)
    if not math.isfinite(value) or not 0 < value <= MAX_SECONDS:
        raise argparse.ArgumentTypeError('seconds must be positive and at most 600, or unlimited')
    return value


def check(checker, bundle, case, response, destination):
    with destination.with_suffix('.stdout').open('xb') as stdout, \
            destination.with_suffix('.stderr').open('xb') as stderr:
        subprocess.run([str(checker), 'check', str(bundle), case, str(response),
                        str(destination), '180'], stdout=stdout, stderr=stderr, check=True)
    return json.loads((destination / 'result.json').read_text())


def prepare(bundle, case, checker, out):
    manifest = json.loads((bundle / 'bundle.json').read_text())
    validate_sources(bundle, manifest)
    if not re.fullmatch(r'[A-Za-z0-9_-]+', case) or case not in {c['id'] for c in manifest['cases']}:
        raise ValueError('case must occur in the prepared bundle')
    out.mkdir(mode=0o700)  # Never overwrite a prior trial.
    # Reuse the independent checker to validate the bundle and compile the trusted
    # task. An intentionally failing file is a setup probe, not a model attempt.
    save(out / 'setup-response.json', {'verdict': 'valid', 'source':
         'import Task\ntheorem DirectLeanTask.answer : DirectLeanTask.goal := '
         'by fail "setup probe"\n'})
    result = check(checker, bundle, case, out / 'setup-response.json', out / 'setup')
    if result['status'] != 'check_failed' or result['failure_stage'] != 'compile':
        raise RuntimeError('task setup failed; see setup logs')
    for name in ('workspace', 'native', 'native/sessions', 'tools'):
        (out / name).mkdir(mode=0o700)
    (out / 'workspace/verdict.txt').write_text('valid\n')
    (out / 'workspace/Solution.lean').write_text(
        'import Task\nopen Whiel Whiel.Concrete\n'
        'theorem DirectLeanTask.answer : DirectLeanTask.goal := by\n'
        '  fail "write your proof here"\n')
    (out / 'tools/lean').write_text(
        '#!/bin/sh\nexec /lean/bin/lean -DmaxHeartbeats=0 "$@"\n')
    (out / 'tools/lean').chmod(0o755)
    (out / 'tools/prompt.txt').write_text('')
    return manifest


def validate_sources(bundle, manifest):
    source = bundle / 'lib-src'
    if not source.exists():
        return
    index = json.loads((bundle / 'source-manifest.json').read_text())['files']
    allowed = {f['path'].removesuffix('.olean') + '.lean' for f in manifest['libraries']
               if f['path'].endswith('.olean') and f['path'].split('/')[0] in ('Whiel', 'Databases')}
    if set(index) != allowed or source.is_symlink():
        raise ValueError('source snapshot must match the generic compiled module list')
    actual = set()
    for path in source.rglob('*'):
        if path.is_symlink():
            raise ValueError('source snapshot cannot contain symlinks')
        if path.is_file():
            relative = str(path.relative_to(source))
            actual.add(relative)
            if relative not in index or sha(read_bounded(path, 2 * 1024 * 1024)) != index[relative]:
                raise ValueError('source snapshot changed or contains an unlisted file')
    if actual != set(index):
        raise ValueError('source snapshot inventory differs')


def sandbox_command(bundle, out, lean, command, *, cli=None, auth=None, catalog=None,
                    network=False):
    args = ['/usr/bin/bwrap', '--unshare-all', '--new-session', '--die-with-parent',
            '--clearenv', '--cap-drop', 'ALL', '--proc', '/proc', '--dev', '/dev',
            '--tmpfs', '/tmp', '--tmpfs', '/run', '--tmpfs', '/home',
            '--dir', '/home/agent', '--dir', '/home/agent/.codex']
    if network:
        args.append('--share-net')  # Native CLI needs its model service.
    if (bundle / 'lib-src').is_dir():
        args += ['--ro-bind', str(bundle / 'lib-src'), '/library-src']
    for raw in ('/usr/bin', '/bin', *SYSTEM_READONLY_PATHS):
        path = Path(raw)
        if path.exists():
            args += ['--ro-bind', str(path.resolve()), raw]
    for raw, target in SYSTEM_READONLY_BINDINGS:
        if Path(raw).is_file():
            args += ['--ro-bind', raw, target]
    for source, target in (
        (lean.parent.parent, '/lean'), (bundle / 'lib', '/library'),
        (bundle / 'reference.txt', '/reference.txt'), (out / 'setup/task', '/task'),
        (out / 'tools/lean', '/tools/lean'),
        (out / 'tools/prompt.txt', '/prompt.txt'),
    ):
        args += ['--ro-bind', str(source), target]
    for source, target in ((out / 'workspace', '/workspace'), (out / 'native', '/native'),
                           (out / 'native/sessions', '/home/agent/.codex/sessions')):
        args += ['--bind', str(source), target]
    if cli:
        args += ['--ro-bind', str(cli), '/tools/codex']
    if catalog:
        args += ['--ro-bind', str(catalog), '/tools/models.json']
    if auth:
        args += ['--bind', str(auth), '/home/agent/.codex/auth.json']
    for key, value in dict(HOME='/home/agent', CODEX_HOME='/home/agent/.codex',
                          PATH='/tools:/usr/bin:/bin', LEAN_PATH='/task:/library:/workspace',
                          LEAN_NUM_THREADS='2', TMPDIR='/tmp', LANG='C.UTF-8',
                          CODEX_INTERNAL_APP_SERVER_REMOTE_CONTROL_DISABLED='1').items():
        args += ['--setenv', key, value]
    for key, value in child_environment(os.environ).items():
        if key != 'PATH':
            args += ['--setenv', key, value]
    return args + ['--chdir', '/workspace', '--', *command]


def native_command(identity, *, catalog=False, fixture_url=None):
    spec = launch_command(identity, Path('/workspace'), None, (), persist_usage=True)
    args = list(spec.argv)
    args[0] = '/tools/codex'
    for feature in ('shell_tool', 'unified_exec'):
        index = next(i for i in range(len(args) - 1)
                     if args[i:i + 2] == ['--disable', feature])
        del args[index:index + 2]
    overrides = ['--enable', 'shell_tool', '--enable', 'unified_exec',
                 '-c', 'sandbox_mode="workspace-write"',
                 '-c', 'sandbox_workspace_write.network_access=false',
                 '-c', 'shell_environment_policy.inherit="all"',
                 '-c', 'log_dir="/native/logs"', '-c', 'sqlite_home="/native/state"']
    if catalog:
        overrides += ['-c', 'model_catalog_json="/tools/models.json"']
    if fixture_url:
        url = urlparse(fixture_url)
        if url.scheme != 'http' or url.hostname != '127.0.0.1':
            raise ValueError('offline fixture must use loopback')
        for key, value in {
            'model_provider': 'fixture', 'model_providers.fixture.name': 'Offline fixture',
            'model_providers.fixture.base_url': fixture_url,
            'model_providers.fixture.wire_api': 'responses',
            'model_providers.fixture.requires_openai_auth': False,
            'model_providers.fixture.request_max_retries': 0,
            'model_providers.fixture.stream_max_retries': 0,
        }.items():
            overrides += ['-c', key + '=' + json.dumps(value)]
    args[-1:-1] = overrides
    # Read the immutable prompt from inside bwrap with explicit stdin ownership.
    return ['/bin/sh', '-c', 'exec "$@" < /prompt.txt', 'lean-agent', *args]


class Events:
    def __init__(self, record):
        self.record = record

    def feed(self, data):
        self.record.stdout(data)

    def finish(self):
        # OwnedProcess finishes its observer after draining stdout. This raw
        # recorder has no parser buffer; execute closes it after usage/stderr.
        pass


async def execute(argv, out, payload, seconds):
    record = ConsultationRecord('lean-agent', out)
    record.prompt(payload)
    stop = Stop()
    loop = asyncio.get_running_loop()
    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        loop.add_signal_handler(sig, stop.set, 'interrupted')
    meter = RolloutUsage(out / 'native/sessions', record)
    started = time.monotonic()
    try:
        child = await OwnedProcess.start(argv, child_environment(os.environ), out,
                                        stdout_limit=8 * 1024 * 1024,
                                        stderr_limit=1024 * 1024, observer=Events(record))
        async def poll():
            while not child.joined:
                meter.poll()
                await asyncio.sleep(.1)
        polling = asyncio.create_task(poll())
        try:
            timeout = None if seconds is None else max(.001, seconds - (time.monotonic() - started))
            native = await child.run(stop, timeout=timeout,
                                     fail_on_stdout_overflow=True, fail_on_stderr_overflow=True)
        finally:
            polling.cancel()
            await asyncio.gather(polling, return_exceptions=True)
        record.stderr(native.stderr)
        return dict(agent_seconds=time.monotonic() - started,
                    agent_limit_seconds=seconds, exit_code=native.returncode,
                    stop_reason=native.reason, capture_failed=native.capture_failed,
                    usage=meter.finish(natural_completion=native.reason == 'exited'
                                       and native.returncode == 0))
    finally:
        save(out / 'retention.json', record.close())
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            loop.remove_signal_handler(sig)


def submission(work):
    verdict = read_bounded(work / 'verdict.txt', 32).decode().strip()
    source = read_bounded(work / 'Solution.lean', RESPONSE_BYTES).decode()
    if verdict not in ('valid', 'invalid') or not source.strip():
        raise ValueError('missing proof or invalid verdict')
    response = {'verdict': verdict, 'source': source}
    if len(json.dumps(response).encode()) > RESPONSE_BYTES:
        raise ValueError('encoded response exceeds checker limit')
    return response


def run(args, *, fixture_url=None):
    seconds = seconds_arg(args.seconds)
    bundle, out, checker = args.bundle.resolve(), args.out.resolve(), args.checker.resolve()
    identity = asyncio.run(verify(args.model, args.reasoning_effort, str(args.cli.resolve())))
    auth = None if fixture_url else args.auth_home.resolve() / 'auth.json'
    if auth:
        private_file(auth)
    manifest = prepare(bundle, args.case, checker, out)
    payload = PROMPT.encode()
    (out / 'tools/prompt.txt').write_bytes(payload)
    save(out / 'run.json', dict(schema_version=1, protocol='lean-agent-v2', case=args.case,
                               native=native_identity_fields(identity), bundle=str(bundle),
                               bundle_sha256=sha((bundle / 'bundle.json').read_bytes()),
                               agent_limit_seconds=seconds, final_check_limit_seconds=180,
                               runtime_memory_limit_bytes=None, lean_max_heartbeats=0,
                               network='native service shared; tool network disabled',
                               tool_sandbox='workspace-write', offline_fixture=bool(fixture_url)))
    command = native_command(identity, catalog=bool(args.model_catalog), fixture_url=fixture_url)
    argv = sandbox_command(bundle, out, Path(manifest['lean']), command,
                           cli=Path(identity.executable), auth=auth,
                           catalog=args.model_catalog.resolve() if args.model_catalog else None,
                           network=True)
    lock = None
    try:
        if auth:
            lock = acquire_auth_lock(auth, time.monotonic() + 30, lambda: False)
            private_file(auth)
        result = asyncio.run(execute(argv, out, payload, seconds))
    finally:
        if lock is not None:
            os.close(lock)
    result['proof_checked'] = False
    result['status'] = 'agent_failed'
    # Cutoff freezes the last saved submission. Never choose among old candidates.
    if result['stop_reason'] == 'deadline' or (result['stop_reason'] == 'exited' and result['exit_code'] == 0):
        try:
            save(out / 'response.json', submission(out / 'workspace'))
            result['check'] = check(checker, bundle, args.case, out / 'response.json', out / 'check')
            result['proof_checked'] = result['check']['proof_checked']
            result['status'] = result['check']['status']
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            result.update(status='submission_failed', error=str(error))
    save(out / 'result.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ('bundle', 'checker', 'cli', 'auth-home', 'out'):
        parser.add_argument('--' + flag, type=Path, required=True)
    parser.add_argument('--case', required=True)
    parser.add_argument('--model', required=True)
    parser.add_argument('--reasoning-effort', default='medium')
    parser.add_argument('--model-catalog', type=Path)
    parser.add_argument('--seconds', type=seconds_arg, default=None,
                        help='agent wall-time limit: 1..600 seconds, or unlimited (default: unlimited)')
    args = parser.parse_args()
    result = run(args)
    print(json.dumps(result, indent=2))
    return 0 if result['proof_checked'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
