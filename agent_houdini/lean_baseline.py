"""Prepare and run the independent compiler-assisted Lean baseline.

The agent protocol and checker are the same for single cases and campaigns.
Campaigns default to a dry run; --launch explicitly enables model calls.
"""

import argparse
from collections import Counter
import csv
import fcntl
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

from .lean_agent import PROMPT, seconds_arg, validate_sources
from .lean_baseline_utils import ROOT, read_bounded, save, selected_inputs, sha, worker_homes
from .token_usage import FIELDS


def prepare_bundle(checker, bundle, inputs=None):
    cases = selected_inputs({'repo': str(ROOT), 'all_inputs': not inputs, 'inputs': inputs})
    subprocess.run([str(checker.resolve()), 'prepare', str(bundle.resolve()), *cases], check=True)
    manifest = json.loads((bundle / 'bundle.json').read_text())
    # Only source counterparts of the checker's generic compiled import closure.
    files = {}
    for entry in manifest['libraries']:
        name = entry['path']
        if not name.endswith('.olean') or name.split('/')[0] not in ('Whiel', 'Databases'):
            continue
        relative = Path(name.removesuffix('.olean') + '.lean')
        if relative.is_absolute() or '..' in relative.parts:
            raise ValueError('invalid library source path')
        data = read_bounded(ROOT / relative, 2 * 1024 * 1024)
        destination = bundle / 'lib-src' / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
        files[str(relative)] = sha(data)
    save(bundle / 'source-manifest.json', {'schema_version': 1, 'files': files})
    validate_sources(bundle, manifest)


def resolve_run(args):
    spec = json.loads(args.spec.read_text())
    required = {'model', 'reasoning_effort', 'provider_cli', 'agent_seconds'}
    if set(spec) - {'model_catalog'} != required:
        raise ValueError('unexpected or missing baseline spec fields')
    if not isinstance(spec['model'], str) or not spec['model'].strip():
        raise ValueError('model is required')
    if not isinstance(spec['reasoning_effort'], str) or not spec['reasoning_effort']:
        raise ValueError('reasoning_effort is required')
    spec['agent_seconds'] = seconds_arg(spec['agent_seconds'])
    if not 1 <= args.jobs <= 4:
        raise ValueError('jobs must be 1..4')
    for key in ('provider_cli', 'model_catalog'):
        if spec.get(key) is not None:
            spec[key] = str((ROOT / spec[key]).resolve(strict=True))
    bundle = args.bundle.resolve(strict=True)
    manifest = json.loads((bundle / 'bundle.json').read_text())
    cases = [row['id'] for row in manifest['cases']]
    if not cases or len(cases) != len(set(cases)) or any(
            not re.fullmatch(r'[A-Za-z0-9_-]+', case) for case in cases):
        raise ValueError('bundle cases must be nonempty, unique identifiers')
    for row in manifest['cases']:
        if sha(read_bounded(bundle / row['id'] / 'Task.lean', 256 * 1024)) != row['task_sha256']:
            raise ValueError('prepared task changed')
    if sha(read_bounded(bundle / 'reference.txt', 2 * 1024 * 1024)) != manifest['reference_sha256']:
        raise ValueError('prepared reference changed')
    validate_sources(bundle, manifest)
    if not (bundle / 'lib-src').is_dir():
        raise ValueError('prepare the bundle with lean_baseline to include generic source files')
    homes = worker_homes(args.auth_root, args.jobs)
    out = args.out.resolve()
    if out.exists():
        raise ValueError('output directory already exists; trials are never overwritten or retried')
    return {'schema_version': 1, 'protocol': 'lean-agent-v2', 'spec': spec,
            'bundle': str(bundle), 'bundle_sha256': sha((bundle / 'bundle.json').read_bytes()),
            'source_manifest_sha256': sha((bundle / 'source-manifest.json').read_bytes()),
            'prompt_sha256': sha(PROMPT.encode()),
            'checker': str(args.checker.resolve(strict=True)), 'cases': cases,
            'jobs': args.jobs, 'auth_homes': [str(home) for home in homes],
            'out': str(out), 'final_check_seconds': 180, 'automatic_retries': 0,
            'runtime_memory_limit_bytes': None, 'lean_max_heartbeats': 0}


def preflight(config, destination):
    """Exercise the real native CLI, bwrap and compiler with a loopback fake model."""
    spec = config['spec']
    env = dict(os.environ, WHIEL_LEAN_AGENT_TEST_BUNDLE=config['bundle'],
               WHIEL_LEAN_AGENT_TEST_CHECKER=config['checker'],
               WHIEL_LEAN_AGENT_TEST_CLI=spec['provider_cli'],
               WHIEL_LEAN_AGENT_TEST_MODEL=spec['model'],
               WHIEL_LEAN_AGENT_TEST_EFFORT=spec['reasoning_effort'],
               WHIEL_LEAN_AGENT_TEST_OUT=str(destination))
    env.pop('WHIEL_LEAN_AGENT_TEST_CATALOG', None)
    if spec.get('model_catalog'):
        env['WHIEL_LEAN_AGENT_TEST_CATALOG'] = spec['model_catalog']
    with destination.with_suffix('.stdout').open('xb') as stdout, \
            destination.with_suffix('.stderr').open('xb') as stderr:
        subprocess.run([sys.executable, '-m', 'unittest', '-v',
                        'agent_houdini.tests.test_lean_agent.NativeLeanAgentTests'],
                       cwd=ROOT, env=env, stdout=stdout, stderr=stderr, check=True)


def case_command(config, slot, case):
    spec = config['spec']
    argv = [sys.executable, '-u', '-m', 'agent_houdini.lean_agent',
            '--bundle', config['bundle'], '--checker', config['checker'],
            '--cli', spec['provider_cli'], '--auth-home', config['auth_homes'][slot - 1],
            '--case', case, '--model', spec['model'], '--reasoning-effort', spec['reasoning_effort'],
            '--seconds', 'unlimited' if spec['agent_seconds'] is None else str(spec['agent_seconds']),
            '--out', str(Path(config['out']) / 'cases' / case)]
    if spec.get('model_catalog'):
        argv += ['--model-catalog', spec['model_catalog']]
    return argv


def read_result(directory):
    try:
        return json.loads((directory / 'result.json').read_text())
    except (OSError, ValueError):
        return {}


def outcome(directory, result):
    if result.get('proof_checked'):
        return 'accepted'
    if result.get('capture_failed'):
        return 'infrastructure_failure'
    if result.get('status') == 'agent_failed':
        stderr = directory / 'native-stderr.txt'
        if (result.get('exit_code') == 137 and stderr.is_file()
                and re.search(rb'WATCHDOG: killing \d+ at \d+ KB RSS', stderr.read_bytes())):
            return 'memory_limit'
        return 'infrastructure_failure'
    if result.get('status') in ('check_failed', 'check_timeout'):
        return 'proof_rejected'
    if result.get('status') == 'submission_failed' and 'check' not in result:
        # A malformed saved term is an outcome; a crashed checker is infrastructure.
        return 'submission_failed' if not (directory / 'check').exists() else 'infrastructure_failure'
    return 'infrastructure_failure'


def summarize(pool):
    config = json.loads((pool / 'run.json').read_text())
    rows = []
    for case in config['cases']:
        directory = pool / 'cases' / case
        result = read_result(directory)
        receipt = pool / 'launch-logs' / (case + '.finished.json')
        finished = receipt.is_file()
        rows.append({'case': case, 'finished': finished,
                     'outcome': outcome(directory, result) if finished else
                         ('running' if directory.exists() else 'queued'),
                     'proof_checked': bool(result.get('proof_checked')),
                     'agent_seconds': result.get('agent_seconds'),
                     'check_seconds': result.get('check', {}).get('check_seconds'),
                     'stop_reason': result.get('stop_reason'), 'usage': result.get('usage', {})})
    totals = {}
    for key in FIELDS:
        values = [r['usage'].get('cumulative', {}).get(key) for r in rows
                  if isinstance(r['usage'].get('cumulative'), dict)]
        known = [v for v in values if v is not None]
        totals[key] = sum(known) if known else None
    summary = {'cases': rows, 'total': len(rows), 'finished': sum(r['finished'] for r in rows),
               'proof_checked': sum(r['proof_checked'] for r in rows),
               'outcomes': dict(Counter(r['outcome'] for r in rows)), 'observed_tokens': totals,
               'usage_coverage': dict(Counter(r['usage'].get('coverage', 'unknown') for r in rows)),
               'usage_note': 'Interrupted responses may be missing. Cached input and reasoning output '
                             'are subsets, not additional tokens. No monetary cost is estimated.'}
    # Manual status refreshes may overlap the dispatcher's refresh.
    with tempfile.NamedTemporaryFile(mode='w', prefix='.summary-', dir=pool, delete=False) as output:
        output.write(json.dumps(summary, indent=2) + '\n')
    Path(output.name).replace(pool / 'summary.json')
    fields = ['case', 'finished', 'outcome', 'proof_checked', 'agent_seconds', 'check_seconds',
              'stop_reason', 'usage_coverage', *FIELDS]
    with tempfile.NamedTemporaryFile(mode='w', newline='', prefix='.cases-', dir=pool,
                                     delete=False) as output:
        writer = csv.DictWriter(output, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            values = {key: row.get(key) for key in fields}
            values.update(row['usage'].get('cumulative') or {})
            values['usage_coverage'] = row['usage'].get('coverage', 'unknown')
            writer.writerow({key: values.get(key) for key in fields})
    Path(output.name).replace(pool / 'cases.csv')
    return summary


def dispatch(config, command_builder=case_command):
    """Refill independent slots; record failures and never retry a case."""
    pool = Path(config['out'])
    pending = iter(config['cases'])
    active = {}
    interrupted = False
    infrastructure_failed = False
    previous = {}

    def stop(_signal, _frame):
        nonlocal interrupted
        interrupted = True
        for process, _case, _stdout, _stderr in active.values():
            if process.poll() is None:
                process.terminate()  # lean_agent handles this and joins its sandbox tree.

    try:
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            previous[sig] = signal.signal(sig, stop)
        exhausted = False
        while active or (not exhausted and not interrupted and not infrastructure_failed):
            for slot in range(1, config['jobs'] + 1):
                if slot in active or exhausted or interrupted or infrastructure_failed:
                    continue
                case = next(pending, None)
                if case is None:
                    exhausted = True
                    break
                stdout = (pool / 'launch-logs' / (case + '.stdout')).open('xb')
                stderr = (pool / 'launch-logs' / (case + '.stderr')).open('xb')
                try:
                    process = subprocess.Popen(command_builder(config, slot, case), cwd=ROOT,
                                               stdout=stdout, stderr=stderr)
                except BaseException:
                    stdout.close()
                    stderr.close()
                    raise
                active[slot] = (process, case, stdout, stderr)
                save(pool / 'launch-logs' / (case + '.started.json'),
                     {'slot': slot, 'pid': process.pid, 'started_unix': time.time()})
            for slot, (process, case, stdout, stderr) in list(active.items()):
                code = process.poll()
                if code is None:
                    continue
                stdout.close()
                stderr.close()
                directory = pool / 'cases' / case
                classification = outcome(directory, read_result(directory))
                infrastructure_failed |= classification == 'infrastructure_failure'
                save(pool / 'launch-logs' / (case + '.finished.json'),
                     {'slot': slot, 'exit_code': code, 'outcome': classification,
                      'finished_unix': time.time()})
                del active[slot]
                print(f'{case}: {classification}', flush=True)
            summarize(pool)
            if active:
                time.sleep(.25)
    finally:
        # Unexpected parent exceptions must not leave paid children running.
        stop(None, None)
        for process, _case, stdout, stderr in active.values():
            process.wait()
            stdout.close()
            stderr.close()
        for sig, handler in previous.items():
            signal.signal(sig, handler)
    summary = summarize(pool)
    return 2 if infrastructure_failed or summary['finished'] != summary['total'] else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    prep = sub.add_parser('prepare', help='Export tasks and generic sources; no model calls')
    prep.add_argument('--checker', type=Path, required=True)
    prep.add_argument('--bundle', type=Path, required=True)
    prep.add_argument('--inputs', nargs='+')
    run = sub.add_parser('run', help='Dry run unless --launch is supplied')
    run.add_argument('spec', type=Path)
    for flag in ('checker', 'bundle', 'out', 'auth-root'):
        run.add_argument('--' + flag, type=Path, required=True)
    run.add_argument('--jobs', type=int, default=1)
    run.add_argument('--launch', action='store_true')
    report = sub.add_parser('summarize')
    report.add_argument('pool', type=Path)
    args = parser.parse_args()
    if args.action == 'prepare':
        prepare_bundle(args.checker, args.bundle, args.inputs)
        return 0
    if args.action == 'summarize':
        print(json.dumps(summarize(args.pool.resolve()), indent=2))
        return 0
    config = resolve_run(args)
    print(json.dumps(config, indent=2), flush=True)
    if not args.launch:
        return 0
    with (args.auth_root / '.lean-baseline-pool.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        pool = Path(config['out'])
        pool.mkdir(mode=0o700)
        (pool / 'cases').mkdir(mode=0o700)
        (pool / 'launch-logs').mkdir(mode=0o700)
        save(pool / 'run.json', config)
        preflight(config, pool / 'native-preflight')  # Fake service, no credentials/model quota.
        # Each lean_agent.prepare verifies and compiles its task before calling
        # the model, so independent slots can start without a serial corpus pass.
        return dispatch(config)


if __name__ == '__main__':
    raise SystemExit(main())
