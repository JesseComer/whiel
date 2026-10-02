"""PAPER REPRODUCTION CODE: original 300-second RQ5 command supervision.

This is orchestration around campaign certify and the existing RSS watcher, not
certificate validation logic. The CLI's exact-target/axiom checks remain authority.
"""
from __future__ import annotations

from collections import Counter
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

from scripts.compare_certificate_builds import watched_run
from scripts.paper_repro_common import (
    ACCEPTED, ARMS, STD3, Context, Interrupted, ReproError, atomic_json, digest,
    now, read_json, relative, require, resolve, successful_search_cases,
)

# Fixed PAPER REPRODUCTION parameters; these are not general-purpose defaults.
CERTIFICATE_SECONDS = 300
SOLVER_SECONDS = 300
PROCESS_KIB = 10 * 1024**2
TREE_KIB = 96 * 1024**2
CORES_PER_ATTEMPT = 12
SOLVER_JOBS = 12
CONCURRENT_ATTEMPTS = 2
PARAMETERS = {"host_seconds": CERTIFICATE_SECONDS, "cli_seconds": CERTIFICATE_SECONDS,
              "vampire_seconds": SOLVER_SECONDS, "process_memory_kib": PROCESS_KIB,
              "tree_memory_kib": TREE_KIB, "cores_per_attempt": CORES_PER_ATTEMPT,
              "solver_jobs": SOLVER_JOBS, "concurrent_attempts": CONCURRENT_ATTEMPTS,
              "sampling_seconds": 0.2}
NORMAL_OUTCOMES = {"certified", "timeout", "process_memory_limit", "memory_limit"}


def select_cores(topology, allowed):
    """Select one allowed online logical CPU per physical (socket,core)."""
    physical = {}
    for line in topology.splitlines():
        if not line or line.startswith("#"):
            continue
        fields = [value.strip() for value in line.split(",")]
        require(len(fields) == 4, "Unexpected lscpu CPU,CORE,SOCKET,ONLINE output.")
        cpu, core, socket, online = fields
        require(cpu.isdigit() and core.isdigit() and socket.isdigit(), "Unknown physical CPU topology.")
        if int(cpu) in allowed and online.lower() in ("y", "yes", "1", "true"):
            physical.setdefault((int(socket), int(core)), int(cpu))
    chosen = [physical[key] for key in sorted(physical)]
    needed = CORES_PER_ATTEMPT * CONCURRENT_ATTEMPTS
    require(len(chosen) >= needed,
            f"RQ5 requires {needed} distinct physical cores within this process's CPU affinity.")
    return [chosen[i:i + CORES_PER_ATTEMPT] for i in range(0, needed, CORES_PER_ATTEMPT)]


def cpu_lanes():
    require(sys.platform.startswith("linux") and hasattr(os, "sched_getaffinity"),
            "Paper RQ5 reproduction requires Linux CPU affinity.")
    for tool in ("taskset", "lscpu", "ps"):
        require(shutil.which(tool), f"Required system tool missing: {tool}")
    topology = subprocess.check_output(["lscpu", "--parse=CPU,CORE,SOCKET,ONLINE"], text=True)
    return select_cores(topology, os.sched_getaffinity(0))


def prepare_attempt(ctx, selected, cpus):
    identity = selected["input"]
    source = ctx.path(selected["run_directory"]) / "verifier"
    case = source / identity
    summary = read_json(source / "summary.json")
    result = read_json(case / "result.json")
    require(summary.get("selected_inputs") == [identity], "Certification requires a single-input source run.")
    require(result.get("status") == selected["status"] and result["status"] in ACCEPTED,
            "Selected search answer no longer matches its accepted result.")
    require((case / "Accepted.json").is_file(), "Selected answer has no acceptance envelope.")
    shape = "valid" if result["status"] == "valid_uncertified" else "invalid"
    record = "Core.json" if shape == "valid" else "Counterexample.json"
    require((case / record).is_file(), "Selected answer record is missing.")
    require(not (case / "Certificate").exists(), "Use fresh uncertified experimental answers.")
    require(digest(ctx.repo / "Benchmark" / identity / "Input.lean") ==
            ctx.manifest["source_sha256"][f"Benchmark/{identity}/Input.lean"], "Benchmark input changed during reproduction.")
    directory = ctx.trial / "certification" / selected["arm"] / identity
    directory.mkdir(parents=True, exist_ok=False)
    copied = directory / "verifier"
    # Preserve timestamps and solver profiles; source runs are never certified in place.
    shutil.copytree(source, copied, copy_function=shutil.copy2)
    hashes = {name: digest(case / name) for name in ("Accepted.json", record)}
    job = {"schema_version": 1, "arm": selected["arm"], "input": identity,
           "model": selected["model"], "shape": shape, "record": record,
           "source_verifier": ctx.rel(source), "source_sha256": hashes,
           "directory": ctx.rel(directory), "cpus": cpus, "parameters": PARAMETERS}
    atomic_json(directory / "job.json", job)
    return {"arm": selected["arm"], "input": identity, "model": selected["model"],
            "state": "prepared", "directory": ctx.rel(directory),
            "job": ctx.rel(directory / "job.json")}


def certify_command(job):
    return ["taskset", "--cpu-list", ",".join(map(str, job["cpus"])),
            "whiel_runner/target/release/whiel-symbolic", "campaign", "certify",
            "--run", job["directory"] + "/verifier", "--jobs", "1",
            "--certification-limit", str(CERTIFICATE_SECONDS),
            "--certificate-solver-limit", str(SOLVER_SECONDS), "--retention", "all"]


def certify_env():
    env = dict(os.environ, WHIEL_CERTIFICATE_COMPILER="lake",
               WHIEL_CERTIFICATE_CANDIDATE_TIMEOUT_SECONDS="0",
               WHIEL_CERTIFICATE_SOLVER_JOBS=str(SOLVER_JOBS),
               LEAN_NUM_THREADS="12", LIMIT_KB="134217728")
    env.pop("WHIEL_KEEP_CERTIFICATE_STAGE", None)
    return env


def check_publication(repo, job):
    """Check the existing CLI's retained exact-target result, not a new proof checker."""
    directory = resolve(repo, job["directory"]) / "verifier"
    case = directory / job["input"]
    result = read_json(case / "result.json")
    summary = read_json(directory / "summary.json")
    shape = job["shape"]
    endpoint = "Valid" if shape == "valid" else "Invalid"
    expected_module = f"Benchmark.{job['input']}.Certificate.{endpoint}"
    expected_theorem = f"Whiel.Benchmark.{job['input']}.Certificate.input_hoare_triple_{shape}"
    require(result.get("input") == job["input"] and result.get("status") == shape,
            "Final campaign result does not certify the selected input/verdict.")
    axioms = result.get("axioms")
    require(isinstance(axioms, list) and len(axioms) == 3 and set(axioms) == STD3,
            "Final campaign result does not have exactly the expected three axioms.")
    require(result.get("certificate_module") == expected_module and
            result.get("certificate_theorem") == expected_theorem and
            result.get("certificate") == "Certificate", "Final certificate target differs from the original input.")
    require(summary.get("selected_inputs") == [job["input"]] and
            summary.get("all_certified") is True and summary.get("all_accepted") is True and
            summary.get("results") == [result], "Final campaign summary/result disagree.")
    require((case / "Certificate" / f"{endpoint}.lean").is_file(), "Final theorem source is missing.")
    settings = read_json(case / "Certificate" / "certificate-build-settings.json")
    require(settings.get("kind") == "whiel_certificate_build_settings" and
            settings.get("version") == 1 and settings.get("compiler") == "lake" and
            settings.get("solver_jobs") == (SOLVER_JOBS if shape == "valid" else 0) and
            settings.get("lean_num_threads") == "12", "Certificate settings disagree with the RQ5 protocol.")
    for name, sha in job["source_sha256"].items():
        require(digest(case / name) == sha and
                digest(resolve(repo, job["source_verifier"]) / job["input"] / name) == sha,
                "Frozen experimental answer changed during certification.")
    return {"campaign_result": result, "build_settings": settings}


def classify_result(repo, job, measurement):
    require(measurement.get("cleanup_ok") is True and not measurement.get("inspection_error"),
            "Process inspection/cleanup failed; stop certification dispatch.")
    outcome = measurement.get("outcome")
    if outcome == "finished":
        require(measurement.get("exit_code") == 0, "Successful supervisor result has a nonzero exit code.")
        return "certified", check_publication(repo, job)
    if outcome in ("timeout", "process_memory_limit", "memory_limit"):
        return outcome, {}
    # A CLI deadline can expire just before the outer watcher observes its own.
    result = read_json(resolve(repo, job["directory"]) / "verifier" / job["input"] / "result.json")
    if outcome == "failed" and result.get("status") == "certification_timeout":
        return "timeout", {"campaign_result": result}
    raise ReproError("Unexpected certification outcome; inspect supervisor.log and campaign result.")


def run_one(repo, job_path):
    """Internal helper: run the watcher on this process's MAIN thread for cleanup."""
    job = read_json(job_path)
    require(job.get("schema_version") == 1 and job.get("parameters") == PARAMETERS,
            "Unexpected RQ5 reproduction job parameters.")
    directory = resolve(repo, job["directory"])
    require(directory.is_relative_to((Path(repo) / "artifacts").resolve()), "Job output must be under artifacts/.")
    require(len(job.get("cpus", [])) == CORES_PER_ATTEMPT and len(set(job["cpus"])) == CORES_PER_ATTEMPT,
            "Expected twelve distinct CPU IDs.")
    receipt = {"schema_version": 1, "input": job["input"], "arm": job["arm"],
               "shape": job["shape"], "model": job["model"], "parameters": PARAMETERS,
               "cpus": job["cpus"], "started_at": now(), "outcome": "infrastructure_failure"}
    def interrupt(_number, _frame):
        raise KeyboardInterrupt

    previous = signal.signal(signal.SIGTERM, interrupt)
    try:
        receipt["command"] = certify_command(job)
        measured = watched_run(receipt["command"], Path(repo), certify_env(),
                               directory / "supervisor.log", limit=CERTIFICATE_SECONDS,
                               memory_kb=TREE_KIB, process_memory_kb=PROCESS_KIB)
        receipt["measurement"] = measured
        outcome, evidence = classify_result(repo, job, measured)
        receipt.update(outcome=outcome, **evidence)
        return 0
    except KeyboardInterrupt:
        # The watcher attempts cleanup in finally but supplies no returned measurement.
        receipt.update(outcome="interrupted", detail="Interrupted; cleanup result unavailable, so dispatch must stop.")
        return 130
    except (OSError, ValueError, TypeError, KeyError, ReproError, subprocess.SubprocessError) as error:
        receipt.update(outcome="infrastructure_failure", detail=str(error))
        return 2
    finally:
        receipt["finished_at"] = now()
        try:
            atomic_json(directory / "supervisor.json", receipt)
        finally:
            signal.signal(signal.SIGTERM, previous)


def run_certification(ctx, lanes=None):
    stage = ctx.manifest["certification"]
    require(stage["state"] == "pending", "Certification was already attempted; no implicit retry is permitted.")
    selected = successful_search_cases(ctx)
    selected.sort(key=lambda row: (ARMS.index(row["arm"]), row["input"]))
    lanes = cpu_lanes() if lanes is None else lanes
    stage.update(state="running", started_at=now(), parameters=PARAMETERS, cpu_lanes=lanes,
                 expected_pairs=[{"arm": row["arm"], "input": row["input"]} for row in selected])
    ctx.save()
    pending = iter(selected)
    active = {}
    stopped = []
    fatal = []
    previous = {}
    exhausted = False

    def stop(number, _frame):
        if not stopped:
            stopped.append(number)
            for process, _attempt, _stream in list(active.values()):
                if process.poll() is None:
                    try:
                        process.send_signal(signal.SIGINT)
                    except ProcessLookupError:
                        pass

    try:
        for sig in (signal.SIGINT, signal.SIGTERM):
            previous[sig] = signal.signal(sig, stop)
        while active or (not exhausted and not stopped and not fatal):
            if not stopped and not fatal:
                for slot in range(CONCURRENT_ATTEMPTS):
                    if slot in active or exhausted or stopped or fatal:
                        continue
                    row = next(pending, None)
                    if row is None:
                        exhausted = True
                        break
                    attempt = prepare_attempt(ctx, row, lanes[slot])
                    stage["attempts"].append(attempt)
                    attempt.update(state="starting", slot=slot, started_at=now())
                    ctx.save()
                    if stopped:
                        attempt["state"] = "interrupted_before_launch"
                        break
                    directory = ctx.path(attempt["directory"])
                    stream = (directory / "helper.log").open("x")
                    try:
                        process = subprocess.Popen(
                            [sys.executable, "scripts/reproduce_paper.py", "_certify-one", attempt["job"]],
                            cwd=ctx.repo, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                    except BaseException:
                        stream.close()
                        attempt["state"] = "launch_failed"
                        raise
                    active[slot] = (process, attempt, stream)
                    attempt.update(state="running", pid=process.pid)
                    ctx.save()
                    if stopped:
                        process.send_signal(signal.SIGINT)
            for slot, (process, attempt, stream) in list(active.items()):
                code = process.poll()
                if code is None:
                    continue
                stream.close()
                del active[slot]
                attempt.update(exit_code=code, finished_at=now(), state="failed")
                try:
                    receipt = read_json(ctx.path(attempt["directory"]) / "supervisor.json")
                    attempt["outcome"] = receipt.get("outcome")
                    require(receipt.get("input") == attempt["input"] and receipt.get("arm") == attempt["arm"],
                            "Supervisor receipt identity mismatch.")
                    require(code == 0 and receipt.get("outcome") in NORMAL_OUTCOMES,
                            "Certification helper stopped unexpectedly; no further attempts will launch.")
                    attempt["state"] = "complete"
                    print(f"RQ5 {attempt['arm']}/{attempt['input']}: {attempt['outcome']}", flush=True)
                except ReproError as error:
                    fatal.append(str(error))
                    # Stop the other active helper through its watcher cleanup.
                    stop(signal.SIGTERM, None)
                ctx.save()
            if active:
                time.sleep(0.1)
        if fatal:
            raise ReproError(fatal[0])
        if stopped:
            raise Interrupted("Certification interrupted; active helpers have exited.")
        require(len(stage["attempts"]) == len(selected), "Certification queue ended before every selected answer.")
        stage.update(state="complete", finished_at=now(),
                     outcomes=dict(Counter(row["outcome"] for row in stage["attempts"])))
    except BaseException as error:
        stage.update(state="interrupted" if isinstance(error, Interrupted) else "failed",
                     detail=str(error), finished_at=now())
        stop(signal.SIGTERM, None)
        for process, attempt, stream in list(active.values()):
            attempt["exit_code"] = process.wait()
            attempt["state"] = "interrupted"
            stream.close()
        raise
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)
        ctx.save()
