#!/usr/bin/env python3
"""Check public CLI certification/correction with its unchanged proof-only mode.

Complete retained-model query coverage uses the existing FMB-enabled B test
configuration; this driver does not claim that the CLI enables model building.
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


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source_inventory(repo):
    names = subprocess.check_output([
        "git", "ls-files", "-z", "Databases", "Whiel", "whiel_runner/src",
        "lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json"
    ], cwd=repo).decode().split("\0")
    return {name: digest(repo / name) for name in names if name}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    args = parser.parse_args()
    repo, binary, evidence = (value.resolve() for value in
                              (args.repo, args.binary, args.evidence))
    evidence.mkdir(parents=True, exist_ok=False)
    fixture = evidence / "standalone-proposer.py"
    shutil.copyfile(Path(__file__).parent / "fixtures" / "generic_api_acceptance.py", fixture)
    trace = evidence / "proposer-api-trace.jsonl"
    output = evidence / "campaign"
    before = {"sources": source_inventory(repo), "binary_sha256": digest(binary)}
    command = ["bash", str(repo / "scripts/watchdog.sh"), "4194304", str(binary),
               "campaign", "run", "--repo", str(repo), "--input", "Example0001",
               "--destination", str(output), "--worker",
               str(repo / ".lake/build/bin/fixed_ambient_encoding_worker"),
               "--search-limit", "240", "--certification-limit", "300",
               "--consultation-limit", "60", "--iteration-limit", "5",
               "--retention", "all",
               "--proposer-executable", str(Path(sys.executable).resolve()),
               "--proposer-arg", "-I", "--proposer-arg", str(fixture),
               "--proposer-arg", "--trace", "--proposer-arg", str(trace),
               "--proposer-arg", "--mode", "--proposer-arg", "certificate"]
    env = dict(os.environ, LEAN_NUM_THREADS="2")
    started = time.monotonic()
    receipt = {"command": command, "before": before,
               "fixture_sha256": digest(fixture), "result": "FAIL",
               "coverage": "unchanged proof-only public CLI: semantic queries, correction, fresh certificate; complete retained-model flow is a separate FMB-enabled B integration test"}
    try:
        with (evidence / "stdout.log").open("wb") as stdout, \
                (evidence / "stderr.log").open("wb") as stderr:
            process = subprocess.Popen(command, cwd=repo, env=env, stdout=stdout,
                                       stderr=stderr, start_new_session=True)
            try:
                returncode = process.wait(timeout=660)
            except subprocess.TimeoutExpired:
                receipt["hard_timeout"] = True
                # Signal the command supervised by the watchdog; B owns and joins
                # its endpoint/worker cleanup. Keep the watchdog alive to join B.
                listing = subprocess.check_output(["ps", "-Ao", "pid=,ppid="],
                                                  text=True)
                children = [int(row.split()[0]) for row in listing.splitlines()
                            if int(row.split()[1]) == process.pid]
                receipt["timeout_watchdog_children"] = children
                for pid in children:
                    try:
                        os.kill(pid, signal.SIGINT)
                    except ProcessLookupError:
                        pass
                try:
                    process.wait(timeout=60)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                    receipt["forced_driver_cleanup"] = True
                raise
        receipt["returncode"] = returncode
        assert returncode == 0, "public generic campaign failed"
        after = {"sources": source_inventory(repo), "binary_sha256": digest(binary)}
        receipt["after"] = after
        assert before == after, "A/B source or built verifier changed during run"
        summary = json.loads((output / "summary.json").read_text())
        assert summary["schema_version"] == 3 and summary["all_certified"] is True
        assert len(summary["results"]) == 1
        certified = summary["results"][0]
        assert certified["status"] == "valid"
        assert set(certified["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
        certificate = Path(certified["certificate"])
        assert certificate.is_dir() and certificate.is_relative_to(output)
        assert (certificate / "Valid.lean").is_file(), "no newly generated certificate"
        events = [json.loads(line) for line in trace.read_text().splitlines()]
        requests = [event for event in events if event["kind"] == "observation"]
        assert len(requests) >= 2 and len({event["pid"] for event in requests}) == 1
        assert requests[1]["observation"]["correction"] is not None
        queries = {event["name"] for event in events if event["kind"] == "query"}
        assert {"ledger", "validate_clauses", "evaluate_clauses"} <= queries
        assert events[-1]["kind"] == "closed"
        assert events[-1]["correction_seen"] and events[-1]["mode"] == "certificate"
        assert any(event["kind"] == "read_only_ledger" for event in events)
        receipt.update(result="PASS", summary=summary, api_queries=sorted(queries),
                       request_count=len(requests), trace_sha256=digest(trace),
                       certificate_files={str(path.relative_to(certificate)): digest(path)
                                          for path in certificate.rglob("*") if path.is_file()})
    except BaseException as error:
        receipt["error"] = repr(error)
        raise
    finally:
        receipt["seconds"] = time.monotonic() - started
        (evidence / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"result": receipt["result"], "seconds": receipt["seconds"],
                      "receipt": str(evidence / "receipt.json")}))


if __name__ == "__main__":
    main()
