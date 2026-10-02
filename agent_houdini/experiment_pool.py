"""GNU Parallel glue for independent, single-input search campaigns.

Only public experiment commands and their result files are used. A slot is
held until the child command exits, including its verifier's joined cleanup
and report generation. This is scheduling and reporting, not verification.
"""

from __future__ import annotations

import fcntl
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import sys

from . import experiment


ACCEPTED = {"valid_uncertified", "invalid_uncertified"}
SKILL_VARIABLES = ("WHIEL_AGENT_SKILLS_FILE", "WHIEL_AGENT_SKILLS_JSON")


def selected_inputs(resolved):
    """Enumerate input names only; the verifier still admits/checks each input."""
    benchmark = Path(resolved["repo"]) / "Benchmark"
    available = sorted(path.name for path in benchmark.iterdir()
                       if path.is_dir() and not path.is_symlink()
                       and re.fullmatch(r"Example[A-Za-z0-9_]+", path.name)
                       and (path / "Input.lean").is_file())
    inputs = available if resolved["all_inputs"] else resolved["inputs"]
    if not inputs or len(set(inputs)) != len(inputs):
        raise experiment.SpecError("pool inputs must be nonempty and unique")
    if any(identity not in available for identity in inputs):
        raise experiment.SpecError("pool inputs must use existing canonical IDs, such as Example0001")
    return inputs


def _child_spec(resolved, identity, pool_dir):
    child = dict(resolved)
    child.update(name=identity, inputs=[identity], all_inputs=False,
                 output_root=str(pool_dir / "cases" / identity))
    # Children run from the package checkout, just like experiment.run. Keep
    # generated paths relative rather than recording this machine's home path.
    for field in experiment.PATH_FIELDS:
        if child.get(field) is not None:
            base = experiment.PACKAGE_ROOT if field == "repo" else resolved["repo"]
            child[field] = os.path.relpath(child[field], base)
    if resolved["proposer"] == "replay":
        for field in experiment.AGENT_ONLY_FIELDS:
            child.pop(field, None)
    return child


def _atomic_write(path, text):
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(text, encoding="utf-8")
    temporary.replace(path)


def _save(pool_dir, record):
    _atomic_write(pool_dir / "pool.json", json.dumps(record, indent=2, sort_keys=True) + "\n")
    rows = record["cases"]
    counts = {state: sum(row["state"] == state for row in rows)
              for state in ("queued", "running", "finished", "failed", "interrupted")}
    accepted = sum(row.get("status") in ACCEPTED for row in rows)
    lines = ["# Experiment pool", "", f"State: {record['state']}; slots: {record['jobs']}.",
             f"Accepted: {accepted}/{len(rows)}; "
             + "; ".join(f"{key}: {value}" for key, value in counts.items()) + ".", "",
             "One attempt per input; no automatic retries. Slots include startup and cleanup.",
             "Search seconds come only from verifier result.json, not queue or process wall time.", ""]
    if record.get("stop_reason"):
        lines.extend([f"Stopped dispatch: {record['stop_reason']}", ""])
    lines += ["| Input | State | Result | Search seconds | Run |",
              "| --- | --- | --- | --- | --- |"]
    for row in rows:
        seconds = row.get("search_seconds")
        seconds = f"{seconds:.3f}" if isinstance(seconds, (float, int)) else "—"
        run = row.get("run_directory")
        link = f"[report]({run}/progress.md)" if run else "—"
        lines.append(f"| {row['input']} | {row['state']} | {row.get('status') or '—'} "
                     f"| {seconds} | {link} |")
    _atomic_write(pool_dir / "progress.md", "\n".join(lines) + "\n")


def _settle(pool_dir, row, returncode):
    """Read a child's public records. Return a reason to stop further dispatch."""
    row.update(exit_code=returncode, state="finished")
    runs = list((pool_dir / "cases" / row["input"]).glob("*/run.json"))
    if len(runs) != 1:
        row["state"] = "failed"
        return f"{row['input']}: missing or ambiguous child run records"
    run_dir = runs[0].parent
    row["run_directory"] = run_dir.relative_to(pool_dir).as_posix()
    summary = experiment._json(run_dir / "verifier" / "summary.json")
    result = experiment._json(run_dir / "verifier" / row["input"] / "result.json")
    if not isinstance(summary, dict) or not isinstance(result, dict):
        row["state"] = "failed"
        return f"{row['input']}: missing verifier summary or result"
    row.update(status=result.get("status"), search_seconds=result.get("search_seconds"),
               failure_kind=result.get("failure_kind"))
    if summary.get("resource_failure") or row["status"] == "resource_exhausted":
        row["state"] = "failed"
        return f"{row['input']}: verifier resource guard stopped the campaign"
    if returncode == 4 and row["status"] in ACCEPTED:
        return None
    if returncode == 3 and (row["status"] == "search_timeout" or (
            row["status"] == "incomplete" and row["failure_kind"] == "IterationLimitExhausted")):
        return None
    row["state"] = "interrupted" if returncode == 130 else "failed"
    return f"{row['input']}: unexpected campaign outcome (exit {returncode}); inspect its run"


def worker_homes(auth_root, jobs):
    """Validate metadata only; stores must come from separate native logins."""
    from . import bwrap

    if auth_root is None:
        raise experiment.SpecError("--auth-root is required; never share/copy a native login between slots")
    try:
        root = bwrap.canonical(auth_root)
        homes = [bwrap.canonical(root / f"worker-{slot}") for slot in range(1, jobs + 1)]
        identities = [bwrap.private_file(home / "auth.json") for home in homes]
        if len(set(homes)) != jobs or len(set(identities)) != jobs:
            raise experiment.SpecError("worker login stores must be distinct")
        return homes
    except (OSError, bwrap.SandboxError) as error:
        raise experiment.SpecError(f"invalid worker login store: {error}") from error


def parallel_command(executable, pool_dir, jobs):
    # GNU Parallel alone owns scheduling, slot assignment, refill and draining.
    # Auth paths are in the environment, never in joblog command strings.
    child = shlex.join([sys.executable, "-u", "-m", "agent_houdini.experiment_pool",
                        "worker", os.path.relpath(pool_dir, experiment.PACKAGE_ROOT)])
    return [executable, "--plain", "--will-cite", "--jobs", str(jobs),
            "--halt", "soon,fail=1", "--joblog", str(pool_dir / "joblog.tsv"),
            child + " {%} {}", "::::", str(pool_dir / "inputs.txt")]


def refresh(pool_dir, **updates):
    """Merge independent worker records for reporting, never to schedule work."""
    with (pool_dir / "report.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        record = experiment._json(pool_dir / "pool.json")
        for index, row in enumerate(record["cases"]):
            current = experiment._json(pool_dir / "records" / (row["input"] + ".json"))
            if current is not None:
                record["cases"][index] = current
        record.update(updates)
        _save(pool_dir, record)
        return record


def run_worker(pool_dir, slot, identity):
    pool_dir = Path(pool_dir).resolve()
    record = experiment._json(pool_dir / "pool.json")
    if not record or not 1 <= slot <= record["jobs"] or identity not in {
            row["input"] for row in record["cases"]}:
        raise experiment.SpecError("invalid pool worker assignment")
    env = dict(os.environ)
    auth_root = env.pop("WHIEL_POOL_AUTH_ROOT", None)
    for key in SKILL_VARIABLES:
        env.pop(key, None)
    if record["spec"]["proposer"] == "agent":
        env["CODEX_HOME"] = str(worker_homes(auth_root, record["jobs"])[slot - 1])
    row = {"input": identity, "slot": slot, "auth_store": f"worker-{slot}",
           "state": "running", "pid": os.getpid(), "started_at": experiment._now()}
    state_path = pool_dir / "records" / (identity + ".json")
    # A manual accidental repeat must not replace an earlier attempt.
    with state_path.open("x") as stream:
        json.dump(row, stream)
    refresh(pool_dir)
    code = 2
    try:
        with (pool_dir / "logs" / (identity + ".log")).open("xb") as log:
            # One ordinary independent campaign. It joins its native/verifier
            # children and writes its own result/report before this slot is freed.
            child = subprocess.Popen(
                [sys.executable, "-u", "-m", "agent_houdini", "experiment", "run",
                 str(pool_dir / "specs" / (identity + ".json"))],
                cwd=experiment.PACKAGE_ROOT, env=env, stdin=subprocess.DEVNULL,
                stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            previous = {}
            def forward(number, _frame):
                try:
                    child.send_signal(number)
                except ProcessLookupError:
                    pass
            for number in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
                previous[number] = signal.signal(number, forward)
            try:
                code = child.wait()
            finally:
                if child.poll() is None:
                    child.send_signal(signal.SIGINT)
                    child.wait()
                for number, handler in previous.items():
                    signal.signal(number, handler)
        reason = _settle(pool_dir, row, code)
    except OSError as error:
        row.update(state="failed", exit_code=code)
        reason = f"{identity}: worker launch/record failure ({type(error).__name__})"
    row.update(finished_at=experiment._now(), stop_reason=reason)
    _atomic_write(state_path, json.dumps(row, indent=2) + "\n")
    refresh(pool_dir)
    print(f"{identity}: {row.get('status') or row['state']} (campaign exit {code}, slot {slot})",
          flush=True)
    # Search timeouts/iteration limits and accepted-uncertified are expected
    # experiment outcomes, not GNU job failures. Infrastructure faults halt refill.
    return 1 if reason else 0


def run_pool(spec_path, *, jobs=4, dry_run=False, out=None, auth_root=None, parallel="parallel"):
    out = sys.stdout if out is None else out
    if isinstance(jobs, bool) or not isinstance(jobs, int) or jobs < 1:
        raise experiment.SpecError("--jobs must be a positive integer")
    resolved = experiment.resolve_spec(experiment.load_spec(spec_path))
    if resolved["certify"] != "never":
        raise experiment.SpecError("pool requires certify: never; certification is a separate step")
    if resolved["verifier_args"] not in ([], ["--no-tools"]) or resolved["agent_args"]:
        raise experiment.SpecError(
            "pool allows only empty verifier_args or [--no-tools], and empty agent_args")
    inputs = selected_inputs(resolved)
    print(f"GNU Parallel pool: {len(inputs)} cases, once each; up to {jobs} campaigns", file=out)
    print("queue: " + ", ".join(inputs), file=out)
    if dry_run:
        print("dry run: no files created, no processes launched", file=out)
        return 0
    executable = shutil.which(str(parallel))
    if executable is None:
        raise experiment.SpecError("GNU Parallel is required; pass --parallel /path/to/parallel")
    version = subprocess.check_output([executable, "--version"], text=True, timeout=10)
    if not version.startswith("GNU parallel "):
        raise experiment.SpecError("--parallel must name GNU Parallel")
    env = dict(os.environ)
    for key in SKILL_VARIABLES:
        env.pop(key, None)
    auth_lock = None
    if resolved["proposer"] == "agent":
        if resolved["provider"] != "codex" or resolved["isolation"] != "bwrap":
            raise experiment.SpecError("native pool currently requires Codex with bwrap isolation")
        homes = worker_homes(auth_root, jobs)
        env["WHIEL_POOL_AUTH_ROOT"] = str(homes[0].parent)
        # Refuse a second pool borrowing these stores; this lock is unrelated
        # to the native wrapper lock and never serializes slots within a pool.
        auth_lock = os.open(homes[0].parent / ".campaign-pool.lock",
                            os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
        try:
            fcntl.flock(auth_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            os.close(auth_lock)
            raise experiment.SpecError("another pool is using these worker logins") from error
    try:
        pool_dir = experiment.allocate_run_directory(
            resolved["output_root"], experiment.run_directory_name(resolved) + "-gnu-pool")
        for name in ("specs", "logs", "records"):
            (pool_dir / name).mkdir()
        record = {"schema_version": 2, "scheduler": "GNU Parallel", "jobs": jobs,
                  "scheduler_version": version.splitlines()[0], "state": "running",
                  "spec": experiment._recorded_spec(resolved),
                  "git_revision": experiment._git_revision(resolved["repo"]),
                  "started_at": experiment._now(), "finished_at": None, "stop_reason": None,
                  "skill_environment_cleared": list(SKILL_VARIABLES),
                  "cases": [{"input": identity, "state": "queued"} for identity in inputs]}
        for identity in inputs:
            experiment._write_json(pool_dir / "specs" / f"{identity}.json",
                                   _child_spec(resolved, identity, pool_dir))
        (pool_dir / "inputs.txt").write_text("\n".join(inputs) + "\n")
        _save(pool_dir, record)
        print(f"pool directory: {pool_dir}", file=out, flush=True)
        command = parallel_command(executable, pool_dir, jobs)
        interrupted = []
        with (pool_dir / "scheduler.log").open("xb") as log:
            child = subprocess.Popen(command, cwd=experiment.PACKAGE_ROOT, env=env,
                                     stdin=subprocess.DEVNULL, stdout=log,
                                     stderr=subprocess.STDOUT, start_new_session=True)
            refresh(pool_dir, scheduler_pid=child.pid)
            previous = {}
            def drain(number, _frame):
                if not interrupted:
                    interrupted.append(number)
                    try:
                        child.send_signal(signal.SIGTERM)
                    except ProcessLookupError:
                        pass
            for number in (signal.SIGINT, signal.SIGTERM):
                previous[number] = signal.signal(number, drain)
            try:
                scheduler_code = child.wait()
            finally:
                if child.poll() is None:
                    child.send_signal(signal.SIGTERM)
                    child.wait()
                for number, handler in previous.items():
                    signal.signal(number, handler)
        record = refresh(pool_dir)
        complete = all(row["state"] == "finished" for row in record["cases"])
        reason = next((row.get("stop_reason") for row in record["cases"]
                       if row.get("stop_reason")), None)
        if not complete and not reason:
            reason = "dispatch stopped; inspect scheduler.log and per-case records"
        code = 130 if interrupted else (4 if complete and scheduler_code == 0 and all(
            row.get("status") in ACCEPTED for row in record["cases"]) else 3)
        refresh(pool_dir, state="interrupted" if interrupted else (
            "finished" if complete and scheduler_code == 0 else "stopped"),
            finished_at=experiment._now(), stop_reason=reason,
            scheduler_exit_code=scheduler_code, exit_code=code)
        print(f"pool report: {pool_dir / 'progress.md'}", file=out, flush=True)
        return code
    finally:
        if auth_lock is not None:
            os.close(auth_lock)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="GNU Parallel single-job adapter")
    parser.add_argument("command", choices=["worker"])
    parser.add_argument("pool_dir", type=Path)
    parser.add_argument("slot", type=int)
    parser.add_argument("identity")
    arguments = parser.parse_args()
    raise SystemExit(run_worker(arguments.pool_dir, arguments.slot, arguments.identity))
