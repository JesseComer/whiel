#!/usr/bin/env python3
"""Deterministic protocol double for Rust certification-adapter tests."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time


mode = sys.argv[1]
if mode == "stall_before_stdin":
    time.sleep(60)
request = json.load(sys.stdin)

if mode == "sleep":
    time.sleep(60)
if mode == "hold_output_lease":
    marker = Path(request["work_directory"]) / "lease-held"
    marker.parent.mkdir(parents=True, exist_ok=True)
    marker.write_text("held\n", encoding="utf-8")
    time.sleep(60)
if mode == "nested_child":
    pid_file = Path(request["work_directory"]) / "nested-child.pid"
    pid_file.parent.mkdir(parents=True, exist_ok=True)
    child = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(60)"],
    )
    pid_file.write_text(str(child.pid), encoding="utf-8")
    time.sleep(60)

identity = dict(request["task_identity"])
if mode == "mismatched_identity":
    identity["module"] += ".Wrong"

base = {
    "format_version": request["format_version"],
    "request_id": request["request_id"],
    "operation": request["operation"],
    "task_identity": identity,
}

if mode == "transient_then_success":
    marker = Path(request["work_directory"]) / "fixture-retry-observed"
    if marker.exists():
        mode = "success"
    else:
        marker.parent.mkdir(parents=True, exist_ok=True)
        marker.touch()
        response = {
            **base,
            "status": "failed",
            "failure": {
                "kind": "check_timeout",
                "phase": "certificate",
                "message": "fixture transient timeout",
                "process_status": "timeout",
            },
        }
        json.dump(response, sys.stdout, sort_keys=True, separators=(",", ":"))
        sys.stdout.write("\n")
        sys.exit(0)

if mode == "failed":
    invocations = Path(request["work_directory"]) / "fixture-failed-invocations.log"
    invocations.parent.mkdir(parents=True, exist_ok=True)
    with invocations.open("a", encoding="utf-8") as handle:
        handle.write("invocation\n")

if mode in {
    "failed",
    "transient_timeout",
    "transient_then_infrastructure",
    "transient_then_cleanup",
    "cleanup_failure",
    "deterministic_infrastructure",
    "malformed_failure_metadata",
    "foreign_stage",
}:
    if mode == "foreign_stage":
        foreign = Path(str(request["solution_directory"]) + ".stage-" + ("f" * 64))
        foreign.mkdir(parents=True)
        (foreign / "owner").write_text("foreign\n", encoding="utf-8")
    response = {
        **base,
        "status": "failed",
        "failure": {
            "kind": "certificate_rejected",
            "phase": "certificate",
            "message": "fixture rejection",
        },
    }
    if mode == "malformed_failure_metadata":
        response["failure"]["elapsed_sec"] = -1.0
        response["failure"]["stdout_hash"] = "not-a-digest"
    elif mode in {
        "transient_timeout",
        "transient_then_infrastructure",
        "transient_then_cleanup",
    }:
        retry_marker = Path(request["work_directory"]) / "fixture-retry-observed"
        deterministic_retry = mode in {
            "transient_then_infrastructure",
            "transient_then_cleanup",
        } and retry_marker.exists()
        retry_marker.parent.mkdir(parents=True, exist_ok=True)
        retry_marker.touch()
        if deterministic_retry:
            if mode == "transient_then_cleanup":
                solution = Path(request["solution_directory"])
                solution.mkdir(parents=True, exist_ok=True)
                solution.parent.chmod(0o555)
            response["failure"].update({
                "kind": "infrastructure_failure",
                "phase": "invalidity_certification",
                "message": "fixture deterministic infrastructure failure after retry",
                "process_status": "completed",
            })
        else:
            response["failure"].update({
                "kind": "check_timeout",
                "phase": "counterexample_runtime",
                "message": "fixture timeout",
                "process_status": "timeout",
            })
    elif mode == "deterministic_infrastructure":
        response["failure"].update({
            "kind": "infrastructure_failure",
            "phase": "invalidity_certification",
            "message": "fixture deterministic infrastructure failure",
            "process_status": "completed",
        })
    elif mode == "cleanup_failure":
        solution = Path(request["solution_directory"])
        solution.mkdir(parents=True, exist_ok=True)
        solution.parent.chmod(0o555)
        response["failure"].update({
            "kind": "infrastructure_failure",
            "phase": "invalidity_certification",
            "message": "fixture forces rollback failure",
            "process_status": "completed",
        })
elif mode == "failed_with_bundle":
    bundle = Path(request["solution_directory"])
    bundle.mkdir(parents=True)
    (bundle / "Certificate.lean").write_text("must be removed\n", encoding="utf-8")
    response = {
        **base,
        "status": "failed",
        "failure": {
            "kind": "certificate_rejected",
            "phase": "certificate",
            "message": "fixture published before failure",
        },
    }
elif mode == "mismatched_identity":
    response = {
        **base,
        "status": "failed",
        "failure": {
            "kind": "certificate_rejected",
            "phase": "certificate",
            "message": "wrong task",
        },
    }
elif mode == "rejected":
    response = {
        **base,
        "status": "rejected",
        "rejection": {
            "kind": "postTrue",
            "message": "complete source check rejected the input",
        },
    }
else:
    witness = None
    if request["operation"] == "certify_valid":
        assert request["core"] == sorted(set(request["core"]))
        if mode == "expect_no_limits":
            assert request["final_search_limit_seconds"] is None
            assert request["lean_limit_seconds"] is None
        classification = "valid"
    else:
        classification = "invalid"
        witness_identity = json.dumps(
            {
                "task_identity": request["task_identity"],
                "input_instance": request["input_instance"],
            },
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
        witness_key = hashlib.sha256(witness_identity).hexdigest()
        if mode == "wrong_witness_name":
            witness_key = "f" * 64
        witness = (
            Path(request["work_directory"])
            / "required"
            / "witnesses"
            / (witness_key + ".json")
        )
        witness.parent.mkdir(parents=True, exist_ok=True)
        witness.write_text(
            json.dumps(
                {
                    "format_version": 1,
                    "task_identity": request["task_identity"],
                    "input_instance": request["input_instance"],
                    "output_instance": request["input_instance"],
                    "fuel": request["fuel"],
                    "runtime": {
                        "stdout_sha256": "2" * 64,
                        "stderr_sha256": "3" * 64,
                        "elapsed_sec": 0.1,
                        "process_status": "completed",
                    },
                },
                sort_keys=True,
                separators=(",", ":"),
            )
            + "\n",
            encoding="utf-8",
        )
        if mode == "wrong_witness_input":
            record = json.loads(witness.read_text(encoding="utf-8"))
            record["input_instance"] = {"wrong": []}
            witness.write_text(
                json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n",
                encoding="utf-8",
            )
        if mode == "symlink_witness":
            contents = witness.read_bytes()
            witness.unlink()
            external = Path(request["work_directory"]) / "external-witness.json"
            external.write_bytes(contents)
            os.symlink(external, witness)
    bundle = Path(request["solution_directory"])
    if mode == "symlink_bundle":
        external = Path(request["work_directory"]) / "external-bundle"
        external.mkdir(parents=True)
        bundle.parent.mkdir(parents=True, exist_ok=True)
        os.symlink(external, bundle)
    else:
        bundle.mkdir(parents=True)
    certificate = bundle / "Certificate.lean"
    if mode == "symlink_certificate":
        external = Path(request["work_directory"]) / "external-certificate.lean"
        external.parent.mkdir(parents=True, exist_ok=True)
        external.write_text("fixture certificate\n", encoding="utf-8")
        os.symlink(external, certificate)
    else:
        certificate.write_text("fixture certificate\n", encoding="utf-8")
    if mode == "leftover_stage":
        stage = Path(
            str(request["solution_directory"])
            + ".stage-"
            + request["output_token"]
        )
        stage.mkdir(parents=True)
        (stage / "incomplete").write_text("incomplete\n", encoding="utf-8")
    digest = hashlib.sha256(certificate.read_bytes()).hexdigest()
    if mode == "bad_hash":
        digest = "0" * 64
    response = {
        **base,
        "status": "certified",
        "classification": classification,
        "bundle": str(bundle),
        "certificate": str(certificate),
        "certificate_sha256": digest,
    }
    if witness is not None:
        response["witness"] = {
            "path": str(witness.resolve()),
            "sha256": hashlib.sha256(witness.read_bytes()).hexdigest(),
        }
        if mode == "bad_witness_hash":
            response["witness"]["sha256"] = "0" * 64
        if mode == "missing_witness":
            del response["witness"]

json.dump(response, sys.stdout, sort_keys=True, separators=(",", ":"))
sys.stdout.write("\n")
