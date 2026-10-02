#!/usr/bin/env python3
"""Benchmark and audit compiled symbolic proposal realizations.

The runner speaks the public length-framed encoding-worker protocol.  It does
not import Benchmark or know how a task was selected.  A caller supplies one
worker identity and can replay the same synthetic worker with the reference
and fast realizations.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FutureTimeout
from dataclasses import dataclass
import hashlib
import json
import math
from pathlib import Path
import re
import resource
import statistics
import struct
import subprocess
import sys
import threading
import time
from typing import Any, BinaryIO, Iterable, Sequence


ROOT = Path(__file__).resolve().parents[1]
TRACE_SCHEMA_VERSION = 1
REPORT_SCHEMA_VERSION = 1
WORKER_FORMAT_VERSION = 5
PROPOSAL_PAGE_PROTOCOL_VERSION = 4
DEFAULT_FRAME_BYTES = 64 * 1024 * 1024
DEFAULT_FAST_SOURCES = (
    ROOT / "Whiel/Synthesis/DisjunctiveClause/FastContract.lean",
    ROOT / "Whiel/Synthesis/Enumerators/Fast/Enumeration.lean",
    ROOT / "Whiel/Synthesis/Enumerators/Fast/Correctness.lean",
    ROOT / "Whiel/Synthesis/Enumerators/Fast/Freshness.lean",
    ROOT / "Whiel/Synthesis/Enumerators/Seeded/Enumeration.lean",
    ROOT / "Whiel/Synthesis/Enumerators/Seeded/Correctness.lean",
    ROOT / "Whiel/Synthesis/Enumerators/Seeded/Freshness.lean",
    ROOT / "Whiel/Synthesis/Enumerators/Capped/Enumeration.lean",
)
DEFAULT_PROVENANCE_SOURCES = (
    ROOT / "Whiel/Synthesis/Runtime/FastProposal.lean",
    ROOT / "Whiel/Synthesis/Runtime/EncodingWorker.lean",
)


class AuditError(RuntimeError):
    """A benchmark input, worker response, or hygiene condition is invalid."""


@dataclass(frozen=True)
class WorkerIdentity:
    semantic_version: int
    encoding_version: int
    canonical_id: str
    module: str
    namespace: str
    source_sha256: str


def canonical_json(value: Any) -> str:
    """Use one stable representation for formula identities and reports."""
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def sha256_file(path: Path) -> str:
    """Hash one executable or source file."""
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def peak_rss_bytes(who: int) -> int:
    """Normalize POSIX maximum resident-set units to bytes."""
    maximum = int(resource.getrusage(who).ru_maxrss)
    return maximum if sys.platform == "darwin" else maximum * 1024


def identity_key(value: Any) -> str:
    """Canonicalize one structural QF identity."""
    return canonical_json(value)


def identity_digest(identities: Iterable[str]) -> str:
    """Hash an ordered identity sequence without ambiguous concatenation."""
    digest = hashlib.sha256()
    for identity in identities:
        encoded = identity.encode("utf-8")
        digest.update(len(encoded).to_bytes(8, "big"))
        digest.update(encoded)
    return digest.hexdigest()


def write_frame(stream: BinaryIO, value: Any, maximum: int) -> None:
    """Write one public encoding-worker frame."""
    payload = canonical_json(value).encode("utf-8")
    if not payload or len(payload) > maximum or len(payload) > 0xFFFFFFFF:
        raise AuditError(f"request frame has invalid length {len(payload)}")
    stream.write(struct.pack(">I", len(payload)))
    stream.write(payload)
    stream.flush()


def read_exact(stream: BinaryIO, size: int) -> bytes:
    """Read an exact byte count or reject premature worker exit."""
    chunks: list[bytes] = []
    remaining = size
    while remaining:
        chunk = stream.read(remaining)
        if not chunk:
            raise AuditError("encoding worker closed its output early")
        chunks.append(chunk)
        remaining -= len(chunk)
    return b"".join(chunks)


def read_frame_blocking(stream: BinaryIO, maximum: int) -> Any:
    """Read one public encoding-worker frame."""
    length = struct.unpack(">I", read_exact(stream, 4))[0]
    if length == 0 or length > maximum:
        raise AuditError(f"response frame length {length} is outside 1..={maximum}")
    try:
        return json.loads(read_exact(stream, length))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AuditError(f"worker returned malformed JSON: {error}") from error


def read_frame(
    executor: ThreadPoolExecutor,
    stream: BinaryIO,
    maximum: int,
    timeout_seconds: float,
) -> Any:
    """Read one frame with a wall-clock timeout."""
    future = executor.submit(read_frame_blocking, stream, maximum)
    try:
        return future.result(timeout=timeout_seconds)
    except FutureTimeout as error:
        raise AuditError(f"worker response exceeded {timeout_seconds:g} seconds") from error


class StderrTail:
    """Drain worker stderr continuously while retaining only a bounded tail."""

    def __init__(self, maximum: int = 64 * 1024) -> None:
        self.maximum = maximum
        self._bytes = bytearray()
        self._lock = threading.Lock()

    def drain(self, stream: BinaryIO) -> None:
        """Consume stderr until EOF so a noisy worker cannot fill its pipe."""
        while True:
            chunk = stream.read(16 * 1024)
            if not chunk:
                return
            with self._lock:
                self._bytes.extend(chunk)
                excess = len(self._bytes) - self.maximum
                if excess > 0:
                    del self._bytes[:excess]

    def text(self) -> str:
        """Return the retained diagnostic tail."""
        with self._lock:
            return bytes(self._bytes).decode("utf-8", errors="replace")


def stop_process(process: subprocess.Popen[bytes]) -> None:
    """Stop one worker and wait until its pipes are closed."""
    if process.poll() is not None:
        return
    process.terminate()
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()


def request_envelope(
    identity: WorkerIdentity,
    context_id: str,
    request_id: int,
    proposal_revision: int,
    realization_id: str,
    realization_version: int,
    protocol_version: int,
    stage: int,
    cursor: int,
    frame_bytes: int,
) -> dict[str, Any]:
    """Construct one exact proposal-page request."""
    return {
        "format_version": WORKER_FORMAT_VERSION,
        "semantic_version": identity.semantic_version,
        "encoding_version": identity.encoding_version,
        "task_canonical_id": identity.canonical_id,
        "task_module": identity.module,
        "task_namespace": identity.namespace,
        "task_source_sha256": identity.source_sha256,
        "request_id": request_id,
        "context_id": context_id,
        "name_env_revision": 0,
        "proposal_revision": proposal_revision,
        "operation": "register_reference_proposal",
        "payload": {
            "realization_id": realization_id,
            "realization_version": realization_version,
            "version": protocol_version,
            "stage": stage,
            "cursor": cursor,
            "max_response_bytes": frame_bytes,
        },
    }


def validate_response(
    response: Any,
    request: dict[str, Any],
    realization_id: str,
    realization_version: int,
    protocol_version: int,
    stage: int,
    cursor: int,
) -> dict[str, Any]:
    """Validate the response fields needed by this independent runner."""
    if not isinstance(response, dict):
        raise AuditError("worker response is not an object")
    shared = (
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
    for field in shared:
        if response.get(field) != request.get(field):
            raise AuditError(f"worker response changed envelope field {field}")
    if response.get("status") != "ok":
        raise AuditError(f"worker rejected proposal request: {response.get('error')!r}")
    payload = response.get("payload")
    if not isinstance(payload, dict):
        raise AuditError("worker proposal payload is not an object")
    expected = {
        "realization_id": realization_id,
        "realization_version": realization_version,
        "version": protocol_version,
        "stage": stage,
        "cursor": cursor,
    }
    for field, value in expected.items():
        if payload.get(field) != value:
            raise AuditError(f"worker proposal payload changed {field}")
    complete = payload.get("complete")
    if type(complete) is not bool:
        raise AuditError("worker proposal payload has invalid complete flag")
    if (
        response.get("request_name_env_revision") != request.get("name_env_revision")
        or response.get("name_env_revision") != request.get("name_env_revision")
    ):
        raise AuditError("worker response changed name_env_revision")
    if response.get("request_proposal_revision") != request.get("proposal_revision"):
        raise AuditError("worker response changed request_proposal_revision")
    expected_revision = request.get("proposal_revision") + int(complete)
    if response.get("proposal_revision") != expected_revision:
        raise AuditError("worker response has invalid proposal_revision")
    count_fields = (
        "raw_occurrences",
        "canonical_formulas",
        "canonical_duplicates",
        "emitted_formulas",
    )
    for field in count_fields:
        value = payload.get(field)
        if type(value) is not int or value < 0:
            raise AuditError(f"worker proposal payload has invalid {field}")
    work = proposal_work_metrics(payload, realization_id)
    generator_work_units, fresh_traversal_nodes, no_fresh_prunes, too_short_prunes = work
    if (
        payload["canonical_formulas"] > payload["raw_occurrences"]
        or payload["canonical_duplicates"]
        != payload["raw_occurrences"] - payload["canonical_formulas"]
        or payload["emitted_formulas"] > payload["canonical_formulas"]
        or no_fresh_prunes > fresh_traversal_nodes
        or too_short_prunes > fresh_traversal_nodes
        or no_fresh_prunes + too_short_prunes > fresh_traversal_nodes
        or generator_work_units < fresh_traversal_nodes
    ):
        raise AuditError("worker proposal population metadata is inconsistent")
    return payload


def proposal_work_metrics(payload: dict[str, Any], realization_id: str) -> tuple[int, int, int, int]:
    """Decode compact fast-only work counters from one proposal page."""
    work = payload.get("fast_work")
    if realization_id == "lean-reference-v3":
        if work is not None:
            raise AuditError("reference realization reported fast-generator work")
        return (0, 0, 0, 0)
    if (
        not isinstance(work, list)
        or len(work) != 4
        or any(type(value) is not int or value < 0 for value in work)
    ):
        raise AuditError("fast realization has invalid fast_work metadata")
    return (work[0], work[1], work[2], work[3])


def run_worker_once(
    worker: Path,
    worker_args: Sequence[str],
    identity: WorkerIdentity,
    realization_id: str,
    realization_version: int,
    protocol_version: int,
    stages: int,
    frame_bytes: int,
    timeout_seconds: float,
    repetition: int,
) -> dict[str, Any]:
    """Run one fresh worker through a contiguous proposal prefix."""
    context_id = f"phase4e-audit-{repetition}-{time.monotonic_ns()}"
    process = subprocess.Popen(
        [str(worker), *worker_args, context_id],
        cwd=ROOT,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if process.stdin is None or process.stdout is None or process.stderr is None:
        process.kill()
        raise AuditError("could not open encoding-worker pipes")
    executor = ThreadPoolExecutor(max_workers=2)
    stderr_tail = StderrTail()
    stderr_future = executor.submit(stderr_tail.drain, process.stderr)
    request_id = 1
    proposal_revision = 0
    stage_rows: list[dict[str, Any]] = []
    prior_identities: set[str] = set()
    try:
        for stage in range(stages):
            cursor = 0
            fragments: list[str] = []
            page_count = 0
            started = time.perf_counter_ns()
            first_page_nanoseconds: int | None = None
            final_payload: dict[str, Any] | None = None
            stable_metadata: tuple[Any, ...] | None = None
            while True:
                request = request_envelope(
                    identity,
                    context_id,
                    request_id,
                    proposal_revision,
                    realization_id,
                    realization_version,
                    protocol_version,
                    stage,
                    cursor,
                    frame_bytes,
                )
                write_frame(process.stdin, request, frame_bytes)
                response = read_frame(
                    executor,
                    process.stdout,
                    frame_bytes,
                    timeout_seconds,
                )
                payload = validate_response(
                    response,
                    request,
                    realization_id,
                    realization_version,
                    protocol_version,
                    stage,
                    cursor,
                )
                page_count += 1
                if first_page_nanoseconds is None:
                    first_page_nanoseconds = time.perf_counter_ns() - started
                fragment = payload.get("fragment")
                next_cursor = payload.get("next_cursor")
                if not isinstance(fragment, str) or type(next_cursor) is not int:
                    raise AuditError("proposal page has invalid fragment or cursor")
                if next_cursor != cursor + len(fragment) or (
                    not payload["complete"] and not fragment
                ):
                    raise AuditError("proposal cursor did not make progress")
                page_metadata = (
                    payload["raw_occurrences"],
                    payload["canonical_formulas"],
                    payload["canonical_duplicates"],
                    payload["emitted_formulas"],
                    proposal_work_metrics(payload, realization_id),
                )
                if stable_metadata is not None and page_metadata != stable_metadata:
                    raise AuditError("proposal metadata changed between pages")
                stable_metadata = page_metadata
                fragments.append(fragment)
                cursor = next_cursor
                request_id += 1
                final_payload = payload
                if payload.get("complete"):
                    proposal_revision += 1
                    break
            elapsed_nanoseconds = time.perf_counter_ns() - started
            try:
                entries = json.loads("".join(fragments))
            except json.JSONDecodeError as error:
                raise AuditError(f"assembled proposal wave is invalid: {error}") from error
            if not isinstance(entries, list):
                raise AuditError("assembled proposal wave is not an array")
            identities: list[str] = []
            for entry in entries:
                if not isinstance(entry, dict) or "identity" not in entry:
                    raise AuditError("proposal entry has no structural identity")
                identities.append(identity_key(entry["identity"]))
            if len(identities) != len(set(identities)):
                raise AuditError("one proposal wave repeats a structural identity")
            repeated = prior_identities.intersection(identities)
            if repeated:
                raise AuditError("proposal wave repeats a prior structural identity")
            prior_identities.update(identities)
            assert final_payload is not None
            if final_payload.get("emitted_formulas") != len(entries):
                raise AuditError("worker emitted count differs from assembled entries")
            work = proposal_work_metrics(final_payload, realization_id)
            stage_rows.append(
                {
                    "stage": stage,
                    "elapsed_nanoseconds": elapsed_nanoseconds,
                    "first_page_nanoseconds": first_page_nanoseconds,
                    "page_count": page_count,
                    "raw_occurrences": final_payload.get("raw_occurrences"),
                    "canonical_formulas": final_payload.get("canonical_formulas"),
                    "canonical_duplicates": final_payload.get("canonical_duplicates"),
                    "generator_work_units": work[0],
                    "fresh_traversal_nodes": work[1],
                    "fresh_no_fresh_prunes": work[2],
                    "fresh_too_short_prunes": work[3],
                    "emitted_formulas": len(entries),
                    "serialized_fragment_bytes": len(
                        "".join(fragments).encode("utf-8")
                    ),
                    "ordered_identity_sha256": identity_digest(identities),
                    "identities": identities,
                }
            )
        process.stdin.close()
        try:
            return_code = process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            stop_process(process)
            return_code = process.returncode
        stderr_future.result(timeout=1)
        stderr = stderr_tail.text()
        if return_code != 0:
            raise AuditError(f"worker exited {return_code}: {stderr}")
    except BaseException as error:
        stop_process(process)
        if isinstance(error, AuditError) and stderr_tail.text():
            error.add_note(f"worker stderr tail: {stderr_tail.text()}")
        raise
    finally:
        stop_process(process)
        executor.shutdown(wait=True, cancel_futures=True)
    return {"repetition": repetition, "stages": stage_rows}


def run_trace(arguments: argparse.Namespace) -> dict[str, Any]:
    """Collect one versioned benchmark trace."""
    worker = arguments.worker.resolve()
    if not worker.is_file():
        raise AuditError(f"worker does not exist: {worker}")
    identity = WorkerIdentity(
        arguments.semantic_version,
        arguments.encoding_version,
        arguments.task_id,
        arguments.task_module,
        arguments.task_namespace,
        arguments.task_source_sha256,
    )
    runs = [
        run_worker_once(
            worker,
            arguments.worker_arg,
            identity,
            arguments.realization_id,
            arguments.realization_version,
            arguments.protocol_version,
            arguments.stages,
            arguments.frame_bytes,
            arguments.timeout,
            repetition,
        )
        for repetition in range(arguments.repetitions)
    ]
    return {
        "schema_version": TRACE_SCHEMA_VERSION,
        "realization_id": arguments.realization_id,
        "realization_version": arguments.realization_version,
        "proposal_page_protocol_version": arguments.protocol_version,
        "worker_sha256": sha256_file(worker),
        "task_identity": {
            "semantic_version": identity.semantic_version,
            "encoding_version": identity.encoding_version,
            "canonical_id": identity.canonical_id,
            "module": identity.module,
            "namespace": identity.namespace,
            "source_sha256": identity.source_sha256,
        },
        "frame_bytes": arguments.frame_bytes,
        "runner_peak_rss_bytes": peak_rss_bytes(resource.RUSAGE_SELF),
        "worker_peak_rss_bytes": peak_rss_bytes(resource.RUSAGE_CHILDREN),
        "runs": runs,
    }


def read_trace(path: Path) -> dict[str, Any]:
    """Read one trace produced by this tool."""
    try:
        trace = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise AuditError(f"cannot read trace {path}: {error}") from error
    if not isinstance(trace, dict) or trace.get("schema_version") != TRACE_SCHEMA_VERSION:
        raise AuditError(f"unsupported trace schema in {path}")
    return trace


def median(values: Sequence[int]) -> float:
    """Return one nonempty median."""
    if not values:
        raise AuditError("cannot summarize an empty measurement")
    return statistics.median(values)


def geometric_mean(values: Sequence[float]) -> float | None:
    """Return a positive geometric mean, or no aggregate for no values."""
    positive = [value for value in values if value > 0 and math.isfinite(value)]
    if not positive:
        return None
    return math.exp(sum(math.log(value) for value in positive) / len(positive))


def cumulative_identity_sets(run: dict[str, Any]) -> list[set[str]]:
    """Compute each completed prefix's structural identities."""
    cumulative: set[str] = set()
    prefixes: list[set[str]] = []
    for row in run.get("stages", []):
        identities = row.get("identities")
        if not isinstance(identities, list) or not all(
            isinstance(identity, str) for identity in identities
        ):
            raise AuditError("trace stage has invalid identities")
        cumulative.update(identities)
        prefixes.append(set(cumulative))
    return prefixes


def compare_traces(reference: dict[str, Any], fast: dict[str, Any]) -> dict[str, Any]:
    """Compare timings and finite-prefix reference coverage."""
    expected_metadata = (
        "worker_sha256",
        "task_identity",
        "proposal_page_protocol_version",
        "frame_bytes",
    )
    for field in expected_metadata:
        if reference.get(field) != fast.get(field):
            raise AuditError(f"reference and fast traces differ in {field}")
    if reference.get("realization_id") != "lean-reference-v3":
        raise AuditError("reference trace has the wrong realization identity")
    if fast.get("realization_id") != "lean-fast-v1":
        raise AuditError("fast trace has the wrong realization identity")
    if reference.get("realization_version") != 3:
        raise AuditError("reference trace has the wrong realization version")
    if fast.get("realization_version") != 1:
        raise AuditError("fast trace has the wrong realization version")
    reference_runs = reference.get("runs")
    fast_runs = fast.get("runs")
    if not isinstance(reference_runs, list) or not isinstance(fast_runs, list):
        raise AuditError("trace runs must be arrays")
    if len(reference_runs) != len(fast_runs) or not reference_runs:
        raise AuditError("reference and fast traces need equal nonzero repetitions")
    reference_stage_counts = [len(run.get("stages", [])) for run in reference_runs]
    fast_stage_counts = [len(run.get("stages", [])) for run in fast_runs]
    if (
        len(set(reference_stage_counts)) != 1
        or len(set(fast_stage_counts)) != 1
        or reference_stage_counts[0] == 0
        or fast_stage_counts[0] == 0
    ):
        raise AuditError("each realization needs one consistent positive stage count")
    stage_count = min(reference_stage_counts[0], fast_stage_counts[0])
    for run in reference_runs:
        stages = run.get("stages")
        expected_stages = list(range(reference_stage_counts[0]))
        if not isinstance(stages, list) or [
            row.get("stage") for row in stages
        ] != expected_stages:
            raise AuditError("trace stages must be contiguous and zero-based")
    for run in fast_runs:
        stages = run.get("stages")
        expected_stages = list(range(fast_stage_counts[0]))
        if not isinstance(stages, list) or [
            row.get("stage") for row in stages
        ] != expected_stages:
            raise AuditError("trace stages must be contiguous and zero-based")
    timing_rows: list[dict[str, Any]] = []
    speedups: list[float] = []
    for stage in range(stage_count):
        reference_times = [run["stages"][stage]["elapsed_nanoseconds"] for run in reference_runs]
        fast_times = [run["stages"][stage]["elapsed_nanoseconds"] for run in fast_runs]
        reference_median = median(reference_times)
        fast_median = median(fast_times)
        speedup = reference_median / fast_median if fast_median else math.inf
        speedups.append(speedup)
        timing_rows.append(
            {
                "stage": stage,
                "reference_median_nanoseconds": reference_median,
                "fast_median_nanoseconds": fast_median,
                "median_speedup": speedup,
            }
        )

    coverage_rows: list[dict[str, Any]] = []
    for repetition, (reference_run, fast_run) in enumerate(zip(reference_runs, fast_runs)):
        reference_prefixes = cumulative_identity_sets(reference_run)
        fast_prefixes = cumulative_identity_sets(fast_run)
        fast_rows = fast_run["stages"]
        cumulative_fast_elapsed = 0
        cumulative_fast_times: list[int] = []
        cumulative_fast_count = 0
        cumulative_fast_counts: list[int] = []
        for row in fast_rows:
            cumulative_fast_elapsed += row["elapsed_nanoseconds"]
            cumulative_fast_times.append(cumulative_fast_elapsed)
            cumulative_fast_count += row["emitted_formulas"]
            cumulative_fast_counts.append(cumulative_fast_count)
        for reference_stage, required in enumerate(reference_prefixes):
            covering_stage = next(
                (index for index, prefix in enumerate(fast_prefixes) if required <= prefix),
                None,
            )
            coverage_rows.append(
                {
                    "repetition": repetition,
                    "reference_stage": reference_stage,
                    "reference_prefix_formulas": len(required),
                    "fast_covering_stage": covering_stage,
                    "fast_prefix_formulas": (
                        cumulative_fast_counts[covering_stage]
                        if covering_stage is not None
                        else None
                    ),
                    "fast_prefix_elapsed_nanoseconds": (
                        cumulative_fast_times[covering_stage]
                        if covering_stage is not None
                        else None
                    ),
                    "covered": covering_stage is not None,
                }
            )
    return {
        "schema_version": REPORT_SCHEMA_VERSION,
        "reference_realization_id": reference.get("realization_id"),
        "fast_realization_id": fast.get("realization_id"),
        "timing_by_stage": timing_rows,
        "geometric_mean_median_speedup": geometric_mean(speedups),
        "peak_memory": {
            "reference_worker_rss_bytes": reference.get("worker_peak_rss_bytes"),
            "fast_worker_rss_bytes": fast.get("worker_peak_rss_bytes"),
            "reference_runner_rss_bytes": reference.get("runner_peak_rss_bytes"),
            "fast_runner_rss_bytes": fast.get("runner_peak_rss_bytes"),
        },
        "reference_coverage_lag": coverage_rows,
        "all_observed_reference_prefixes_covered": all(
            row["covered"] for row in coverage_rows
        ),
    }


def strip_lean_comments(source: str) -> str:
    """Remove nested Lean comments while retaining strings and code."""
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        pair = source[index : index + 2]
        character = source[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                index += 2
            elif pair == "-/":
                block_depth -= 1
                index += 2
            else:
                index += 1
            continue
        if not in_string and pair == "/-":
            block_depth = 1
            index += 2
            continue
        if not in_string and pair == "--":
            newline = source.find("\n", index + 2)
            index = len(source) if newline < 0 else newline
            continue
        output.append(character)
        if in_string:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
        elif character == '"':
            in_string = True
        index += 1
    if block_depth:
        raise AuditError("unterminated Lean block comment")
    return "".join(output)


def local_imports(path: Path) -> list[str]:
    """Read top-level Lean imports from uncommented source."""
    code = strip_lean_comments(path.read_text(encoding="utf-8"))
    modules: list[str] = []
    for imported in re.findall(r"(?m)^\s*import\s+([^\r\n]+?)\s*$", code):
        for module in imported.split():
            if re.fullmatch(r"[A-Za-z0-9_'.]+", module) is None:
                raise AuditError(f"cannot audit Lean import token {module!r} in {path}")
            modules.append(module)
    return modules


def module_path(module: str) -> Path | None:
    """Resolve one repository-local Lean module."""
    candidate = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
    return candidate if candidate.is_file() else None


def import_closure(sources: Sequence[Path]) -> set[str]:
    """Compute the repository-local import closure."""
    return import_graph(sources)[0]


def import_graph(sources: Sequence[Path]) -> tuple[set[str], set[Path]]:
    """Compute imported modules and every reachable repository-local source."""
    pending = list(sources)
    visited_paths: set[Path] = set()
    modules: set[str] = set()
    while pending:
        path = pending.pop()
        path = path.resolve()
        if path in visited_paths:
            continue
        visited_paths.add(path)
        for module in local_imports(path):
            modules.add(module)
            dependency = module_path(module)
            if dependency is not None:
                pending.append(dependency)
    return modules, visited_paths


FORBIDDEN_CODE_PATTERNS = (
    ("benchmark module", re.compile(r"\bBenchmark(?:\.|\b)")),
    ("example identifier", re.compile(r"\bExample[0-9]{4}\b")),
    ("catalog dependency", re.compile(r"\bCatalog(?:\.json|Path|Entry|Case)?\b")),
    ("task canonical identity", re.compile(r"\btaskCanonicalId\b|\bcanonical_?id\b", re.I)),
    ("task source metadata", re.compile(r"\btask(?:Module|Namespace|Source)\b|sourceSha256")),
    ("known result metadata", re.compile(r"\bknown_?(?:status|result|classification)\b", re.I)),
    ("embedded SHA-256", re.compile(r'"[0-9a-fA-F]{64}"')),
    ("absolute local path", re.compile(r'"/(?:Users|home|workspace|tmp)/')),
)


def hygiene_report(
    sources: Sequence[Path], *, allow_task_provenance: bool = False
) -> dict[str, Any]:
    """Audit generic fast-enumerator sources for benchmark specialization."""
    resolved = [path.resolve() for path in sources]
    violations: list[dict[str, Any]] = []
    existing = [path for path in resolved if path.is_file()]
    modules, reachable = import_graph(existing)
    for path in resolved:
        if not path.is_file():
            violations.append({"source": str(path), "kind": "missing source", "match": None})
    for path in sorted(reachable):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        for label, pattern in FORBIDDEN_CODE_PATTERNS:
            if allow_task_provenance and label in {
                "task canonical identity",
                "task source metadata",
            }:
                continue
            match = pattern.search(code)
            if match is not None:
                violations.append(
                    {"source": str(path), "kind": label, "match": match.group(0)}
                )
    imports = sorted(modules)
    for module in imports:
        if module == "Benchmark" or module.startswith("Benchmark."):
            violations.append(
                {"source": "import closure", "kind": "benchmark import", "match": module}
            )
    return {
        "schema_version": REPORT_SCHEMA_VERSION,
        "sources": [str(path) for path in resolved],
        "scanned_sources": [str(path) for path in sorted(reachable)],
        "repository_local_imports": imports,
        "violations": violations,
        "benchmark_blind": not violations,
    }


def complete_hygiene_report() -> dict[str, Any]:
    """Audit generation strictly and the provenance adapter separately."""
    generator = hygiene_report(DEFAULT_FAST_SOURCES)
    provenance = hygiene_report(
        DEFAULT_PROVENANCE_SOURCES, allow_task_provenance=True
    )
    return {
        "schema_version": REPORT_SCHEMA_VERSION,
        "generator": generator,
        "provenance_adapter": provenance,
        "violations": [*generator["violations"], *provenance["violations"]],
        "benchmark_blind": generator["benchmark_blind"]
        and provenance["benchmark_blind"],
    }


def write_output(value: Any, output: Path | None) -> None:
    """Write stable JSON to stdout or one requested file."""
    rendered = json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    if output is None:
        sys.stdout.write(rendered)
    else:
        output.write_text(rendered, encoding="utf-8")


def add_output(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--output", type=Path, help="write JSON here instead of stdout")


def parser() -> argparse.ArgumentParser:
    """Construct the command-line parser."""
    root = argparse.ArgumentParser(description=__doc__)
    commands = root.add_subparsers(dest="command", required=True)

    run = commands.add_parser("run", help="collect one worker proposal trace")
    run.add_argument("--worker", type=Path, required=True)
    run.add_argument("--worker-arg", action="append", default=[])
    run.add_argument("--realization-id", required=True)
    run.add_argument("--realization-version", type=int, required=True)
    run.add_argument(
        "--protocol-version",
        type=int,
        default=PROPOSAL_PAGE_PROTOCOL_VERSION,
    )
    run.add_argument("--stages", type=int, default=2)
    run.add_argument("--repetitions", type=int, default=5)
    run.add_argument("--frame-bytes", type=int, default=DEFAULT_FRAME_BYTES)
    run.add_argument("--timeout", type=float, default=60.0)
    run.add_argument("--semantic-version", type=int, required=True)
    run.add_argument("--encoding-version", type=int, required=True)
    run.add_argument("--task-id", required=True)
    run.add_argument("--task-module", required=True)
    run.add_argument("--task-namespace", required=True)
    run.add_argument("--task-source-sha256", required=True)
    add_output(run)

    compare = commands.add_parser("compare", help="compare reference and fast traces")
    compare.add_argument("--reference", type=Path, required=True)
    compare.add_argument("--fast", type=Path, required=True)
    add_output(compare)

    static = commands.add_parser("static", help="scan generic Lean sources")
    static.add_argument("--source", type=Path, action="append")
    add_output(static)
    return root


def main(argv: Sequence[str] | None = None) -> int:
    """Run one audit command."""
    arguments = parser().parse_args(argv)
    try:
        if arguments.command == "run":
            if arguments.stages <= 0 or arguments.repetitions <= 0:
                raise AuditError("stages and repetitions must be positive")
            if arguments.frame_bytes <= 0 or arguments.frame_bytes > DEFAULT_FRAME_BYTES:
                raise AuditError("frame bytes are outside the worker protocol limit")
            value = run_trace(arguments)
            status = 0
        elif arguments.command == "compare":
            value = compare_traces(
                read_trace(arguments.reference), read_trace(arguments.fast)
            )
            status = 0 if value["all_observed_reference_prefixes_covered"] else 2
        else:
            value = (
                hygiene_report(arguments.source)
                if arguments.source
                else complete_hygiene_report()
            )
            status = 0 if value["benchmark_blind"] else 1
        write_output(value, arguments.output)
        return status
    except (AuditError, OSError, ValueError) as error:
        print(f"phase4e enumerator audit: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
