"""Tests for the benchmark-independent Phase 4E audit runner."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys
import time

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "phase4e_enumerator_audit.py"


def load_audit():
    """Load the standalone script without requiring a package layout."""
    spec = importlib.util.spec_from_file_location("phase4e_enumerator_audit", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def trace(realization: str, waves: list[list[str]], times: list[int]) -> dict:
    """Construct one minimal valid comparison trace."""
    stages = []
    for stage, (identities, elapsed) in enumerate(zip(waves, times)):
        stages.append(
            {
                "stage": stage,
                "elapsed_nanoseconds": elapsed,
                "emitted_formulas": len(identities),
                "identities": identities,
            }
        )
    return {
        "schema_version": 1,
        "realization_id": realization,
        "realization_version": 3 if realization == "lean-reference-v3" else 1,
        "proposal_page_protocol_version": 4,
        "worker_sha256": "1" * 64,
        "task_identity": {"canonical_id": "SyntheticEnumeratorAudit"},
        "frame_bytes": 1024 * 1024,
        "runs": [{"repetition": 0, "stages": stages}],
    }


def worker_identity(audit):
    """Construct one synthetic identity accepted by a fake worker."""
    return audit.WorkerIdentity(
        semantic_version=1,
        encoding_version=1,
        canonical_id="SyntheticEnumeratorAudit",
        module="Synthetic.EnumeratorAudit",
        namespace="Whiel.Synthetic.EnumeratorAudit",
        source_sha256="0" * 64,
    )


def valid_response(audit, realization: str = "lean-fast-v1") -> tuple[dict, dict]:
    """Construct one complete response accepted by the audit boundary."""
    identity = worker_identity(audit)
    request = audit.request_envelope(
        identity,
        "phase4e-test",
        1,
        0,
        realization,
        1 if realization == "lean-fast-v1" else 3,
        audit.PROPOSAL_PAGE_PROTOCOL_VERSION,
        0,
        0,
        1024 * 1024,
    )
    response = {
        field: request[field]
        for field in (
            "format_version",
            "semantic_version",
            "encoding_version",
            "task_canonical_id",
            "task_module",
            "task_namespace",
            "task_source_sha256",
            "request_id",
            "context_id",
            "operation",
        )
    }
    response["status"] = "ok"
    response["request_name_env_revision"] = request["name_env_revision"]
    response["name_env_revision"] = request["name_env_revision"]
    response["request_proposal_revision"] = request["proposal_revision"]
    response["proposal_revision"] = request["proposal_revision"] + 1
    response["payload"] = {
        "realization_id": request["payload"]["realization_id"],
        "realization_version": request["payload"]["realization_version"],
        "version": request["payload"]["version"],
        "stage": 0,
        "cursor": 0,
        "next_cursor": 2,
        "complete": True,
        "fragment": "[]",
        "raw_occurrences": 1,
        "canonical_formulas": 1,
        "canonical_duplicates": 0,
        "emitted_formulas": 1,
    }
    if realization == "lean-fast-v1":
        response["payload"]["fast_work"] = [1, 0, 0, 0]
    return request, response


def test_comparison_reports_finite_prefix_coverage_lag() -> None:
    """Extra fast formulas may delay, but cannot hide, reference coverage."""
    audit = load_audit()
    reference = trace("lean-reference-v3", [["a"], ["b"]], [100, 200])
    fast = trace("lean-fast-v1", [["extra"], ["a"], ["b"]], [10, 20, 30])

    report = audit.compare_traces(reference, fast)

    assert report["all_observed_reference_prefixes_covered"]
    lag = report["reference_coverage_lag"]
    assert lag[0]["fast_covering_stage"] == 1
    assert lag[0]["fast_prefix_formulas"] == 2
    assert lag[1]["fast_covering_stage"] == 2
    assert lag[1]["fast_prefix_formulas"] == 3
    assert report["timing_by_stage"][0]["median_speedup"] == 10


def test_comparison_marks_an_uncovered_reference_prefix() -> None:
    """A bounded trace must not silently claim unobserved coverage."""
    audit = load_audit()
    reference = trace("lean-reference-v3", [["a"], ["b"]], [100, 200])
    fast = trace("lean-fast-v1", [["a"], ["extra"]], [50, 50])

    report = audit.compare_traces(reference, fast)

    assert not report["all_observed_reference_prefixes_covered"]
    assert report["reference_coverage_lag"][-1]["covered"] is False


def test_comparison_rejects_unrelated_traces() -> None:
    """Timing and coverage claims require one exact worker/task boundary."""
    audit = load_audit()
    reference = trace("lean-reference-v3", [["a"]], [100])
    fast = trace("lean-fast-v1", [["a"]], [50])
    fast["task_identity"] = {"canonical_id": "DifferentTask"}

    with pytest.raises(audit.AuditError, match="task_identity"):
        audit.compare_traces(reference, fast)


def test_hygiene_scan_follows_imports_and_ignores_comments(tmp_path: Path) -> None:
    """Benchmark references in code or transitive imports are rejected."""
    audit = load_audit()
    safe = tmp_path / "Safe.lean"
    safe.write_text(
        "/- Benchmark.Example0001 is prose only. -/\n"
        "def realizationId : String := \"lean-fast-v1\"\n",
        encoding="utf-8",
    )
    assert audit.hygiene_report([safe])["benchmark_blind"]

    unsafe = tmp_path / "Unsafe.lean"
    unsafe.write_text(
        "def chosen : String := \"Example0001\"\n",
        encoding="utf-8",
    )
    report = audit.hygiene_report([unsafe])
    assert not report["benchmark_blind"]
    assert report["violations"][0]["kind"] == "example identifier"

    helper = tmp_path / "Hidden.lean"
    helper.write_text('def chosen : String := "Example0002"\n', encoding="utf-8")
    importer = tmp_path / "Importer.lean"
    importer.write_text("import Safe Hidden\n", encoding="utf-8")
    previous_root = audit.ROOT
    audit.ROOT = tmp_path
    try:
        imported_report = audit.hygiene_report([importer])
    finally:
        audit.ROOT = previous_root
    assert not imported_report["benchmark_blind"]
    assert any(
        finding["kind"] == "example identifier"
        for finding in imported_report["violations"]
    )


def test_cli_compare_uses_stable_json(tmp_path: Path) -> None:
    """The standalone comparison command is automation-friendly."""
    audit = load_audit()
    reference = tmp_path / "reference.json"
    fast = tmp_path / "fast.json"
    output = tmp_path / "report.json"
    reference.write_text(
        json.dumps(trace("lean-reference-v3", [["a"]], [100])),
        encoding="utf-8",
    )
    fast.write_text(
        json.dumps(trace("lean-fast-v1", [["a"]], [25])),
        encoding="utf-8",
    )

    status = audit.main(
        [
            "compare",
            "--reference",
            str(reference),
            "--fast",
            str(fast),
            "--output",
            str(output),
        ]
    )

    assert status == 0
    report = json.loads(output.read_text(encoding="utf-8"))
    assert report["geometric_mean_median_speedup"] == 4


def test_response_rejects_missing_or_inconsistent_work_metrics() -> None:
    """Work metrics are required and obey their population invariants."""
    audit = load_audit()
    request, response = valid_response(audit)
    arguments = (
        response,
        request,
        "lean-fast-v1",
        1,
        audit.PROPOSAL_PAGE_PROTOCOL_VERSION,
        0,
        0,
    )
    audit.validate_response(*arguments)

    del response["payload"]["fast_work"]
    with pytest.raises(audit.AuditError, match="fast_work"):
        audit.validate_response(*arguments)

    request, response = valid_response(audit)
    response["payload"]["fast_work"] = [1, 1, 1, 1]
    with pytest.raises(audit.AuditError, match="population metadata"):
        audit.validate_response(
            response,
            request,
            "lean-fast-v1",
            1,
            audit.PROPOSAL_PAGE_PROTOCOL_VERSION,
            0,
            0,
        )


def test_response_rejects_malformed_revision_metadata() -> None:
    """The independent runner enforces the public page envelope."""
    audit = load_audit()
    request, response = valid_response(audit)
    response["proposal_revision"] = request["proposal_revision"]
    with pytest.raises(audit.AuditError, match="proposal_revision"):
        audit.validate_response(
            response,
            request,
            "lean-fast-v1",
            1,
            audit.PROPOSAL_PAGE_PROTOCOL_VERSION,
            0,
            0,
        )


def test_worker_runner_drains_noisy_stderr(tmp_path: Path) -> None:
    """Worker diagnostics cannot fill their pipe and deadlock a proposal."""
    audit = load_audit()
    worker = tmp_path / "fake_worker.py"
    worker.write_text(
        """\
import json
import struct
import sys

reader = sys.stdin.buffer
writer = sys.stdout.buffer
while True:
    header = reader.read(4)
    if not header:
        break
    size = struct.unpack(\">I\", header)[0]
    request = json.loads(reader.read(size))
    sys.stderr.buffer.write(b\"diagnostic-noise\\n\" * 16384)
    sys.stderr.buffer.flush()
    stage = request[\"payload\"][\"stage\"]
    entries = [{\"identity\": {\"stage\": stage, \"formula\": \"false\"}}]
    fragment = json.dumps(entries, separators=(\",\", \":\"))
    response = {
        field: request[field]
        for field in (
            \"format_version\", \"semantic_version\", \"encoding_version\",
            \"task_canonical_id\", \"task_module\", \"task_namespace\",
            \"task_source_sha256\", \"request_id\", \"context_id\", \"operation\",
        )
    }
    response[\"status\"] = \"ok\"
    response[\"request_name_env_revision\"] = request[\"name_env_revision\"]
    response[\"name_env_revision\"] = request[\"name_env_revision\"]
    response[\"request_proposal_revision\"] = request[\"proposal_revision\"]
    response[\"proposal_revision\"] = request[\"proposal_revision\"] + 1
    response[\"payload\"] = {
        \"realization_id\": request[\"payload\"][\"realization_id\"],
        \"realization_version\": request[\"payload\"][\"realization_version\"],
        \"version\": request[\"payload\"][\"version\"],
        \"stage\": stage,
        \"cursor\": request[\"payload\"][\"cursor\"],
        \"fragment\": fragment,
        \"next_cursor\": len(fragment),
        \"complete\": True,
        \"raw_occurrences\": 1,
        \"canonical_formulas\": 1,
        \"canonical_duplicates\": 0,
        \"emitted_formulas\": 1,
        \"fast_work\": [1, 0, 0, 0],
    }
    encoded = json.dumps(response, separators=(\",\", \":\")).encode()
    writer.write(struct.pack(\">I\", len(encoded)))
    writer.write(encoded)
    writer.flush()
""",
        encoding="utf-8",
    )

    result = audit.run_worker_once(
        Path(sys.executable),
        [str(worker)],
        worker_identity(audit),
        "lean-fast-v1",
        1,
        audit.PROPOSAL_PAGE_PROTOCOL_VERSION,
        2,
        1024 * 1024,
        2.0,
        0,
    )

    assert [row["emitted_formulas"] for row in result["stages"]] == [1, 1]


def test_worker_timeout_terminates_before_reader_shutdown(tmp_path: Path) -> None:
    """A blocked frame read must not trap executor shutdown forever."""
    audit = load_audit()
    worker = tmp_path / "stalled_worker.py"
    worker.write_text(
        """\
import sys
import time

sys.stdin.buffer.read(4)
time.sleep(30)
""",
        encoding="utf-8",
    )
    started = time.monotonic()

    with pytest.raises(audit.AuditError, match="response exceeded"):
        audit.run_worker_once(
            Path(sys.executable),
            [str(worker)],
            worker_identity(audit),
            "lean-fast-v1",
            1,
            audit.PROPOSAL_PAGE_PROTOCOL_VERSION,
            1,
            1024 * 1024,
            0.05,
            0,
        )

    assert time.monotonic() - started < 3
