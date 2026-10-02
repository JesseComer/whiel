#!/usr/bin/env python3
"""Fresh sequential/Lake certification diagnostics over saved benchmark answers."""

import argparse
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import signal
import shutil
import subprocess
import time


REPO = Path(__file__).resolve().parents[1]
STD3 = {"propext", "Classical.choice", "Quot.sound"}
PORTFOLIO = {"Example5018", "Example5023", "Example5030", "Example5034", "Example5036"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def profiles(case):
    return ("casc_2025" if case in PORTFOLIO else "direct",
            120 if case in {"Example5034", "Example5036"} else 60)


def inventory(repo):
    records = {}
    for directory in sorted((repo / "Benchmark").glob("Example[0-9][0-9][0-9][0-9]")):
        found = [directory / name for name in ("Core.json", "Counterexample.json")
                 if (directory / name).is_file()]
        if len(found) != 1:
            raise ValueError(f"{directory.name}: expected exactly one saved answer")
        records[directory.name] = found[0]
    return records


def process_snapshot():
    # lstart supplies a process identity, so a recycled PID is not signalled.
    text = subprocess.check_output(
        ["ps", "-axo", "pid=,ppid=,pgid=,rss=,stat=,lstart="], text=True)
    result = {}
    for line in text.splitlines():
        fields = line.split(None, 5)
        if len(fields) == 6:
            pid, parent, group, rss = map(int, fields[:4])
            result[pid] = (parent, group, rss, fields[4], fields[5])
    return result


class ProcessTree:
    """Remember observed descendants even when their leader subsequently exits."""

    def __init__(self, pid):
        self.pid = pid
        self.identities = {}
        self.groups = {pid}  # Popen starts a fresh session.

    def refresh(self):
        table = process_snapshot()
        owned = {pid for pid, identity in self.identities.items()
                 if pid in table and table[pid][4] == identity}
        if self.pid in table and (self.pid not in self.identities or
                                  table[self.pid][4] == self.identities[self.pid]):
            owned.add(self.pid)
        while True:
            fresh = {pid for pid, info in table.items()
                     if info[0] in owned or info[1] in self.groups}
            if fresh <= owned:
                break
            owned |= fresh
            self.groups |= {table[pid][1] for pid in fresh}
        for pid in owned:
            self.identities[pid] = table[pid][4]
        return {pid: table[pid] for pid in owned if not table[pid][3].startswith("Z")}

    def stop(self):
        # Stop parents before the final discovery, preventing new children
        # while collecting compiler/solver groups; then kill the whole set.
        for _ in range(2):
            for pid in self.refresh():
                self._signal(pid, signal.SIGSTOP)
        for pid in self.refresh():
            self._signal(pid, signal.SIGKILL)
        deadline = time.monotonic() + 5
        while self.refresh() and time.monotonic() < deadline:
            for pid in self.refresh():
                self._signal(pid, signal.SIGKILL)
            time.sleep(0.05)
        return not self.refresh()

    def _signal(self, pid, sig):
        current = process_snapshot().get(pid)
        if current and current[4] == self.identities.get(pid):
            try:
                os.kill(pid, sig)
            except ProcessLookupError:
                pass


def watched_run(command, cwd, env, log, limit, memory_kb, process_memory_kb=None):
    """One attempt at a time; Lake alone schedules concurrent compilers."""
    started = time.monotonic()
    peak = 0
    process_peak = 0
    reason = None
    inspection_error = None
    with log.open("wb") as output:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdout=output,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        tree = ProcessTree(process.pid)
        cleanup = False
        try:
            while True:
                owned = tree.refresh()
                rss = sum(info[2] for info in owned.values())
                peak = max(peak, rss)
                process_rss = max((info[2] for info in owned.values()), default=0)
                process_peak = max(process_peak, process_rss)
                if process_memory_kb is not None and process_rss > process_memory_kb:
                    reason = "process_memory_limit"
                    break
                elapsed = time.monotonic() - started
                if rss > memory_kb:
                    reason = "memory_limit"
                    break
                if elapsed >= limit:
                    reason = "timeout"
                    break
                if process.poll() is not None:
                    break
                time.sleep(0.2)
        except (OSError, subprocess.SubprocessError) as error:
            reason = "infrastructure_failure"
            inspection_error = str(error)
        finally:
            # Also clean an unexpectedly surviving child after a normal exit.
            try:
                cleanup = tree.stop()
            except (OSError, subprocess.SubprocessError) as error:
                reason = "infrastructure_failure"
                inspection_error = str(error)
                # Without inspection, descendant cleanup cannot be certified.
                # At least terminate our unreaped session leader and its group;
                # cleanup_ok=False prevents starting another attempt.
                if process.returncode is None:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
            finally:
                if process.poll() is None:
                    process.kill()
                process.wait(timeout=10)
    return dict(elapsed_seconds=time.monotonic() - started, exit_code=process.returncode,
                outcome=reason or ("finished" if process.returncode == 0 else "failed"),
                peak_tree_rss_kb=peak, peak_process_rss_kb=process_peak,
                cleanup_ok=cleanup, inspection_error=inspection_error)


def validate_receipt(path, case, shape):
    receipt = json.loads(path.read_text())
    if (receipt.get("kind") != "whiel_certificate_build_receipt" or
            receipt.get("version") != 4 or receipt.get("canonical_id") != case or
            receipt.get("shape") != shape or set(receipt.get("axioms", [])) != STD3):
        raise ValueError("unexpected certificate receipt identity, shape or axioms")
    expected = f"Benchmark.{case}.Certificate.{'Valid' if shape == 'valid' else 'Invalid'}"
    if receipt.get("certificate_module") != expected:
        raise ValueError("unexpected final certificate module")
    if shape == "invalid" and set((receipt.get("revalidation") or {}).get("axioms", [])) != STD3:
        raise ValueError("missing invalidity revalidation audit")
    return receipt


def validate_settings(path, backend, shape, solver_jobs):
    settings = json.loads(path.read_text())
    if (settings.get("kind") != "whiel_certificate_build_settings" or
            settings.get("version") != 1 or settings.get("compiler") != backend or
            settings.get("solver_jobs") != (solver_jobs if shape == "valid" else 0)):
        raise ValueError("certificate settings do not match requested concurrency/backend")
    return settings


def phase_diagnostics(log):
    """Keep unfinished phases visible when the outer supervisor kills a run."""
    phases = {}
    malformed = 0
    for line in log.splitlines():
        if not line.startswith("certificate phase: "):
            continue
        try:
            event = json.loads(line.removeprefix("certificate phase: "))
            identity = event["id"]
            if (event.get("version") != 1 or type(identity) is not int or identity < 0 or
                    not isinstance(event.get("phase"), str) or
                    not isinstance(event.get("subject"), str)):
                raise ValueError("invalid phase event")
            if event["event"] == "start" and identity not in phases:
                phases[identity] = dict(id=identity, phase=event["phase"],
                                       subject=event["subject"], outcome="incomplete",
                                       elapsed_seconds=None)
            elif (event["event"] == "finish" and identity in phases and
                  phases[identity]["outcome"] == "incomplete" and
                  all(event[key] == phases[identity][key] for key in ("phase", "subject")) and
                  event["outcome"] in ("success", "failure", "cancelled") and
                  type(event["elapsed_seconds"]) in (int, float) and
                  math.isfinite(event["elapsed_seconds"]) and event["elapsed_seconds"] >= 0):
                phases[identity].update(outcome=event["outcome"],
                                        elapsed_seconds=event["elapsed_seconds"])
            else:
                raise ValueError("unpaired phase event")
        except (ValueError, KeyError, TypeError):
            malformed += 1
    values = list(phases.values())
    # Starts count managed launch attempts, including spawn failure/cancel
    # at invocation entry; only successful exits count as completions.
    return dict(phase_timings=values, malformed_phase_events=malformed,
                lake_launches=sum(p["phase"] == "lake" for p in values),
                lake_completions=sum(p["phase"] == "lake" and p["outcome"] == "success"
                                     for p in values))


def run_attempt(args, case, record, backend):
    directory = args.output / case / backend
    directory.mkdir(parents=True, exist_ok=False)
    shape = "valid" if record.name == "Core.json" else "invalid"
    profile, solver_seconds = profiles(case)
    command = [str(args.runner), "certificate", "build", "--repo", str(REPO),
               "--input", case, "--core" if shape == "valid" else "--counterexample", str(record),
               "--worker", str(args.worker), "--destination", str(directory / "Certificate"),
               "--staging", str(directory / "staging"), "--receipt", str(directory / "receipt.json")]
    if shape == "valid":
        command += ["--profile", profile, "--time-limit-seconds", str(solver_seconds)]
    solver_jobs = args.solver_jobs
    env = dict(os.environ, WHIEL_CERTIFICATE_COMPILER=backend,
               WHIEL_CERTIFICATE_CANDIDATE_TIMEOUT_SECONDS="0", LEAN_NUM_THREADS=str(args.threads),
               WHIEL_CERTIFICATE_SOLVER_JOBS=str(solver_jobs))
    # A debugging setting must not leak multi-gigabyte partial trees per case.
    env.pop("WHIEL_KEEP_CERTIFICATE_STAGE", None)
    result = dict(case=case, backend=backend, shape=shape, record_sha256=digest(record),
                  profile=profile if shape == "valid" else None,
                  solver_seconds=solver_seconds if shape == "valid" else None,
                  limit_seconds=args.limit, memory_kb=args.memory_kb, lean_threads=args.threads,
                  solver_jobs=solver_jobs, process_memory_kb=args.process_memory_kb,
                  command=command)
    result.update(watched_run(command, REPO, env, directory / "build.log", args.limit,
                              args.memory_kb, args.process_memory_kb))
    log = (directory / "build.log").read_text(errors="replace")
    result["serial_recovery"] = "certificate compiler: Lake candidate repair:" in log
    result.update(phase_diagnostics(log))
    if result["outcome"] == "finished":
        try:
            if backend == "lake" and result["lake_completions"] == 0:
                raise ValueError("missing successful Lake build: runner may not support selected backend")
            receipt = validate_receipt(directory / "receipt.json", case, shape)
            settings = validate_settings(directory / "Certificate/certificate-build-settings.json",
                                         backend, shape, solver_jobs)
            result["resolved_settings"] = settings
            final = directory / "Certificate" / ("Valid.lean" if shape == "valid" else "Invalid.lean")
            if not final.is_file():
                raise ValueError("missing final theorem source")
            result["outcome"] = "success"
            result["job_proof_digests"] = {job["id"]: {
                key: job.get(key) for key in ("canonical_sha256", "transformed_sha256", "packaged_sha256")
            } for job in receipt.get("jobs", [])}
        except (OSError, ValueError, KeyError) as error:
            result["outcome"] = "bad_receipt"
            result["receipt_error"] = str(error)
    (directory / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    if not result["cleanup_ok"]:
        raise RuntimeError(f"{case}/{backend}: process cleanup failed; refusing another attempt")
    # A hard timeout cannot run the certifier's normal staging guard.
    # Remove only this harness-owned attempt's private compilation tree.
    if (directory / "staging").exists():
        shutil.rmtree(directory / "staging")
    return result


def write_summary(output, results, backends=("sequential", "lake")):
    rows = []
    for case in sorted({case for case, _ in results}):
        sequential = results.get((case, "sequential"), {})
        lake = results.get((case, "lake"), {})
        both = sequential.get("outcome") == lake.get("outcome") == "success"
        rows.append(dict(case=case, sequential_outcome=sequential.get("outcome", "pending" if "sequential" in backends else "not_run"),
                         lake_outcome=lake.get("outcome", "pending" if "lake" in backends else "not_run"),
                         sequential_seconds=sequential.get("elapsed_seconds", ""),
                         lake_seconds=lake.get("elapsed_seconds", ""),
                         speedup=sequential["elapsed_seconds"] / lake["elapsed_seconds"] if both else "",
                         lake_serial_recovery=lake.get("serial_recovery", ""),
                         same_proofs=(sequential["job_proof_digests"] == lake["job_proof_digests"]) if both else ""))
    if rows:
        with (output / "comparison.csv").open("w", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=rows[0])
            writer.writeheader()
            writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path, help="fresh ignored artifact directory")
    parser.add_argument("--cases", nargs="+", help="default: all saved answers")
    parser.add_argument("--backends", nargs="+", choices=("sequential", "lake"),
                        default=["sequential", "lake"])
    parser.add_argument("--shape", choices=("all", "valid", "invalid"), default="all")
    parser.add_argument("--runner", type=Path, default=REPO / "whiel_runner/target/release/whiel-symbolic")
    parser.add_argument("--worker", type=Path, default=REPO / ".lake/build/bin/fixed_ambient_encoding_worker")
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--solver-jobs", type=int, default=1,
                        help="inner certificate solver jobs; harness outer concurrency is one")
    parser.add_argument("--limit", type=float, default=600)
    parser.add_argument("--memory-kb", type=int, default=12582912)
    parser.add_argument("--process-memory-kb", type=int,
                        help="optional RSS cap for each owned process, in addition to aggregate memory")
    args = parser.parse_args()
    if args.threads < 1 or args.solver_jobs < 1 or args.limit <= 0 or args.memory_kb <= 0:
        parser.error("threads, solver-jobs, limit and memory-kb must be positive")
    if args.process_memory_kb is not None and args.process_memory_kb <= 0:
        parser.error("process-memory-kb must be positive when supplied")
    args.output = args.output.resolve()
    args.runner = args.runner.resolve(strict=True)
    args.worker = args.worker.resolve(strict=True)
    records = inventory(REPO)
    if args.shape != "all":
        filename = "Core.json" if args.shape == "valid" else "Counterexample.json"
        records = {case: path for case, path in records.items() if path.name == filename}
    cases = args.cases or list(records)
    if len(set(cases)) != len(cases) or any(case not in records for case in cases):
        parser.error("cases must be distinct saved benchmark inputs")
    if len(set(args.backends)) != len(args.backends):
        parser.error("backends must be distinct")
    process_snapshot()  # Fail before launching Lean if memory inspection is denied.
    args.output.mkdir(parents=True, exist_ok=False)
    metadata = dict(kind="whiel_certificate_compilation_comparison", version=1,
                    revision=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
                    diff=subprocess.check_output(["git", "diff"], cwd=REPO, text=True),
                    runner_sha256=digest(args.runner), worker_sha256=digest(args.worker),
                    harness_sha256=digest(Path(__file__)),
                    records_sha256={case: digest(records[case]) for case in cases},
                    toolchain=(REPO / "lean-toolchain").read_text().strip(),
                    platform=platform.platform(), logical_cpus=os.cpu_count(),
                    order=args.backends, shape=args.shape, cases=cases,
                    limits=dict(seconds=args.limit, memory_kb=args.memory_kb, lean_threads=args.threads,
                                solver_jobs=args.solver_jobs, outer_jobs=1,
                                process_memory_kb=args.process_memory_kb),
                    note="Independent regeneration; fixed order; fresh certificate outputs; prebuilt dependencies")
    (args.output / "run.json").write_text(json.dumps(metadata, indent=2) + "\n")
    results = {}
    for case in cases:
        for backend in args.backends:
            if (digest(args.runner) != metadata["runner_sha256"] or
                    digest(args.worker) != metadata["worker_sha256"] or
                    digest(records[case]) != metadata["records_sha256"][case]):
                raise RuntimeError("runner, worker or saved answer changed during the comparison")
            print(f"START {case} {backend}", flush=True)
            result = run_attempt(args, case, records[case], backend)
            results[case, backend] = result
            write_summary(args.output, results, args.backends)
            print(f"DONE {case} {backend}: {result['outcome']} {result['elapsed_seconds']:.1f}s", flush=True)


if __name__ == "__main__":
    main()
