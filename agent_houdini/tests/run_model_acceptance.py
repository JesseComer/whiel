#!/usr/bin/env python3
# Author: Fangzhu Shen
"""Opt-in substitution gate using one already-built generic B integration binary.

This test driver, not production C, inventories verifier sources and selects
external test processes. B tests never import/discover the C package. No model
or native account is used; the native executable is the synthetic fixture.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time


TESTS = {
    "full": "live_generic_api_full_model_flow_publishes_a_fresh_kernel_certificate",
    "historical": "generic_historical_ledger_references_reach_saved_models_without_drop_authority",
}


def digest(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def protected(repo, binary):
    paths = []
    for name in ("Whiel", "Databases", "Benchmark", "VampLean", "whiel_runner/src", "whiel_runner/tests"):
        paths.extend(path for path in (repo / name).rglob("*") if path.is_file() and "__pycache__" not in path.parts)
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "toolchain.lock.json"):
        if (repo / name).is_file():
            paths.append(repo / name)
    return {"sources": {str(path.relative_to(repo)): digest(path) for path in sorted(paths)},
            "test_binary_sha256": digest(binary),
            "worker_sha256": digest(repo / ".lake/build/bin/fixed_ambient_encoding_worker")}


def write_executable(path, source):
    path.write_text("#!" + sys.executable + "\n" + source)
    path.chmod(0o700)


def prepare(args, case, mode, kind):
    environment = dict(os.environ, LEAN_NUM_THREADS="1")
    environment.pop("WHIEL_ACCEPTANCE_PROPOSER_COMMAND", None)
    real_lake = shutil.which("lake")
    if real_lake is None:
        raise ValueError("Lake is required")
    shim = case / "bin"
    shim.mkdir()
    original_path = environment.get("PATH", "")
    write_executable(shim / "lake", "import os,sys\n"
        + "os.environ['PATH']=" + repr(original_path) + "\n"
        + "if sys.argv[1:2]==['build']:\n"
        + " os.execv('/bin/bash',['bash'," + repr(str(args.repo / "scripts/lake_build_watched.sh")) + ",*sys.argv[2:]])\n"
        + "os.execv('/bin/bash',['bash'," + repr(str(args.repo / "scripts/watchdog.sh"))
        + ",'4194304'," + repr(real_lake) + ",*sys.argv[1:]])\n")
    environment["PATH"] = str(shim) + os.pathsep + original_path
    if kind == "c":
        native = case / "native.py"
        shutil.copyfile(args.c_root / "agent_houdini/tests/fixtures/endpoint_acceptance.py", native)
        native.chmod(0o700)
        native.with_suffix(".json").write_text(json.dumps({"synthetic_fixture": True,
            "scenario": mode, "trace": str(case / "native-trace.jsonl")}))
        (case / "claude-config").mkdir(mode=0o700)
        (case / "logs").mkdir(mode=0o700)
        environment["CLAUDE_CONFIG_DIR"] = str(case / "claude-config")
        wrapper = case / "proposer"
        arguments = ["endpoint", "--provider", "claude", "--model", "model-a",
                     "--provider-cli", str(native),
                     "--agent-scratch-parent", "/private/tmp", "--agent-log-parent", str(case / "logs")]
        write_executable(wrapper, "import sys\nsys.path.insert(0," + repr(str(args.c_root))
                         + ")\nfrom agent_houdini.launcher import main\nraise SystemExit(main(" + repr(arguments) + "))\n")
        environment["WHIEL_ACCEPTANCE_PROPOSER_COMMAND"] = json.dumps({"executable": str(wrapper), "arguments": []})
    return environment


def check_native(case, mode):
    events = [json.loads(line) for line in (case / "native-trace.jsonl").read_text().splitlines()]
    starts = [event for event in events if event["kind"] == "native_start"]
    submitted = [event for event in events if event["kind"] == "submitted"]
    assert len(starts) >= (3 if mode == "full" else 2) and len(starts) == len(submitted)
    assert any(event["correction_seen"] for event in submitted)
    if mode == "full":
        assert any(event["kind"] == "full_models" and event["refutation_seen"] for event in events)
    else:
        discoveries = [event for event in events if event["kind"] == "discovered"]
        assert len(discoveries) == 1 and discoveries[0]["pages"] > 1
        first, last = (json.loads(event["payload"]) for event in (submitted[0], submitted[-1]))
        assert first["dropped"][0]["clause"] == discoveries[0]["clause"]
        assert last["clauses"] == [] and last["dropped"] == []
    assert sum(event["kind"] == "native_closed" for event in events) == len(starts)
    for pid in {event[key] for event in events for key in ("pid", "relay_pid") if key in event}:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            continue
        raise AssertionError("native or relay survived joined test: " + str(pid))
    return {"native_requests": len(starts), "native_trace_sha256": digest(case / "native-trace.jsonl")}


def run_case(args, mode, kind):
    case = args.evidence / (mode + "-" + kind)
    case.mkdir()
    environment = prepare(args, case, mode, kind)
    before = protected(args.repo, args.test_binary)
    command = ["bash", str(args.repo / "scripts/watchdog.sh"), "4194304", str(args.test_binary),
               TESTS[mode], "--exact", "--nocapture", "--test-threads=1"]
    receipt = {"result": "FAIL", "mode": mode, "proposer": kind, "command": command, "before": before}
    started = time.monotonic()
    try:
        with (case / "test.log").open("wb") as output:
            process = subprocess.Popen(command, cwd=args.repo / "whiel_runner", env=environment,
                                       stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = process.wait(timeout=1800)
            except subprocess.TimeoutExpired:
                listing = subprocess.check_output(["ps", "-Ao", "pid=,ppid="], text=True)
                for row in listing.splitlines():
                    pid, parent = map(int, row.split())
                    if parent == process.pid:
                        try: os.kill(pid, signal.SIGINT)
                        except ProcessLookupError: pass
                try: process.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                    receipt["forced_cleanup"] = True
                raise
        receipt["returncode"] = code
        log = (case / "test.log").read_text()
        assert code == 0 and "1 passed; 0 failed" in log, "exact generic B test failed or did not run"
        if kind == "c":
            receipt["native"] = check_native(case, mode)
        if mode == "full":
            marker = "generic_api_fmb_receipt="
            line = next(line.split(marker, 1)[1] for line in log.splitlines() if marker in line)
            details = json.loads(line)
            assert details["fmb_enabled"] and details["certificate_jobs"] == 5
            assert set(details["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
            receipt["certificate"] = details
        receipt["after"] = protected(args.repo, args.test_binary)
        assert before == receipt["after"], "verifier sources, test binary or worker changed"
        receipt["result"] = "PASS"
    except BaseException as error:
        receipt["error"] = repr(error)
        raise
    finally:
        receipt["seconds"] = time.monotonic() - started
        receipt["log_sha256"] = digest(case / "test.log")
        (case / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"mode": mode, "proposer": kind, "result": "PASS", "seconds": receipt["seconds"],
                      "receipt": str(case / "receipt.json")}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--c-root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--test-binary", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--mode", choices=tuple(TESTS), action="append")
    parser.add_argument("--proposer", choices=("nonllm", "c"), action="append")
    args = parser.parse_args()
    for name in ("repo", "c_root", "test_binary", "evidence"):
        setattr(args, name, getattr(args, name).resolve())
    args.evidence.mkdir(parents=True, exist_ok=False)
    for mode in args.mode or TESTS:
        for kind in args.proposer or ("nonllm", "c"):
            run_case(args, mode, kind)


if __name__ == "__main__":
    main()
