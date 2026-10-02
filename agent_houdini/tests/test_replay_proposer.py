"""The replay proposer: the recorded answer, and the wire it goes out on."""

import contextlib
import io
import json
import os
from pathlib import Path
import socket
import struct
import subprocess
import sys
import tempfile
import unittest

from agent_houdini.tests import replay_proposer
from agent_houdini.tests.replay_proposer import (
    ReplayError, RecordSource, TranscriptSource, build_response, core_clauses,
    counterexample_instance, live_pending_drop_references, push_identity, read_record,
    recorded_pending_sources, remap_drops,
)


REPOSITORY = Path(__file__).resolve().parents[2]
TOOL = Path(replay_proposer.__file__).resolve()
BINDING = {"consultation_digest": "a" * 64, "request_digest": "b" * 64,
           "run_digest": "c" * 64, "scope_digest": "d" * 64,
           "state_snapshot_digest": "e" * 64, "task_digest": "f" * 64,
           "validation_manifest_digest": "0" * 64, "validation_ordinal": 0}
EXAMPLE = {"kind": "candidate_clauses", "schema_version": 4, "binding": BINDING,
           "clauses": [], "dropped": []}
CORE = {"kind": "whiel_framework_ii_core_rows", "version": 1, "rows": [
    {"level": 1, "source": "(second ⊆ later)"},
    {"level": 0, "source": "(first = ∅[2])"}]}
COUNTEREXAMPLE = {"kind": "whiel_framework_ii_counterexample", "version": 1, "instance": {
    "relations": [{"name": "p::E", "rows": [["num:0", "num:1"]]},
                  {"name": "p::S", "rows": []}]}}


def observation(identity):
    return {"feedback": {"presentation": {"task": {"canonical_id": identity}}}}


def write_benchmark(root, identity, name, document):
    directory = Path(root) / "Benchmark" / identity
    directory.mkdir(parents=True, exist_ok=True)
    (directory / name).write_text(json.dumps(document), encoding="utf-8")


def write_transcript_request(run_dir, identity, request_id, payload=None, *, pending=()):
    """One `agent/<ID>/request-N/` directory of a retained run, minimally: a
    `submissions.jsonl` with one submission (or none, for a consultation the
    original proposer never answered) and a `prompt.txt` whose "Pending
    clauses" section names `pending`'s `(clause_id, source, display)` rows,
    in the exact shape the real harness renders (`prompt.py`'s
    `_pending_section`), so `recorded_pending_sources` reads it the same way
    it would read a real one.
    """
    directory = Path(run_dir) / "agent" / identity / f"request-{request_id}"
    directory.mkdir(parents=True, exist_ok=True)
    if payload is not None:
        (directory / "submissions.jsonl").write_text(json.dumps({
            "submission": 1, "payload": json.dumps(payload, ensure_ascii=False)}) + "\n",
            encoding="utf-8")
    lines = [f"# Pending clauses ({len(pending)})", ""]
    for identifier, source, display in pending:
        lines.append(f"    clause {identifier}  minimum level 1  current level 1  "
                     "origin submitted  drop_reference: yes")
        lines.append(f"        {source}")
        if display and display != source:
            lines.append(f"        displayed: {display}")
    lines += ["", "# Last round (0 clauses)", ""]
    (directory / "prompt.txt").write_text("\n".join(lines), encoding="utf-8")
    return directory


def observation_with_pending(identity, entries):
    """A push naming `identity`, with a pending list built from
    `(clause_id, source, display, drop_reference)` rows.
    """
    pending = [{"clause": {"clause_id": identifier, "canonical_source": source, "display": display},
               "drop_reference": reference} for identifier, source, display, reference in entries]
    return {"feedback": {"presentation": {"task": {"canonical_id": identity}}, "pending": pending}}


def drop_reference(clause_id, tag):
    return {"clause": {"clause_id": clause_id, "record_digest": tag + "-r", "formula_digest": tag + "-f"},
            "consultation_digest": tag + "-c", "authorization_digest": tag + "-a"}


def write_transcript_json(path, inputs):
    """A minimal `export-transcript`-shaped file: `inputs` maps identity ->
    a list of `(number, submission_or_None)` pairs, `submission` already in
    the frozen shape (`dropped` as text/`None`, no `binding`).
    """
    document = {"kind": "whiel_transcript_replay", "version": 1, "controls": {}, "provider": None,
               "model": None, "reasoning_effort": None,
               "inputs": {identity: {"requests": [{"number": number, "submission": submission}
                                                   for number, submission in requests],
                                     "expected": {"status": None, "verdict_class": "not_accepted",
                                                 "core": None, "counterexample": None, "ledger": []}}
                         for identity, requests in inputs.items()}}
    Path(path).write_text(json.dumps(document, ensure_ascii=False), encoding="utf-8")
    return document


class RecordTests(unittest.TestCase):
    def test_core_rows_are_replayed_weakest_level_first(self):
        self.assertEqual(core_clauses(CORE, "Example0001"),
                         ["(first = ∅[2])", "(second ⊆ later)"])

    def test_rows_of_one_level_keep_the_order_the_record_wrote_them_in(self):
        document = dict(CORE, rows=[{"level": 0, "source": "b"}, {"level": 0, "source": "a"}])
        self.assertEqual(core_clauses(document, "Example0001"), ["b", "a"])

    def test_a_record_that_is_not_a_core_record_is_refused(self):
        for document in (dict(CORE, kind="something_else"), dict(CORE, rows=[]),
                         dict(CORE, rows=[{"level": 0}]),
                         dict(CORE, rows=[{"level": True, "source": "a"}])):
            with self.assertRaises(ReplayError):
                core_clauses(document, "Example0001")

    def test_the_counterexample_instance_is_replayed_as_recorded(self):
        self.assertEqual(counterexample_instance(COUNTEREXAMPLE, "Example0013"),
                         COUNTEREXAMPLE["instance"])

    def test_a_malformed_counterexample_record_is_refused(self):
        for document in (dict(COUNTEREXAMPLE, kind="other"),
                         dict(COUNTEREXAMPLE, instance={}),
                         dict(COUNTEREXAMPLE, instance={"relations": [{"name": "p::E"}]})):
            with self.assertRaises(ReplayError):
                counterexample_instance(document, "Example0013")

    def test_each_kind_of_record_is_found_and_a_missing_one_declines(self):
        with tempfile.TemporaryDirectory() as root:
            write_benchmark(root, "Example0001", "Core.json", CORE)
            write_benchmark(root, "Example0013", "Counterexample.json", COUNTEREXAMPLE)
            (Path(root) / "Benchmark" / "Example9999").mkdir(parents=True)
            self.assertEqual(read_record(root, "Example0001"),
                             ("candidate_clauses", ["(first = ∅[2])", "(second ⊆ later)"]))
            self.assertEqual(read_record(root, "Example0013"),
                             ("candidate_counterexample", COUNTEREXAMPLE["instance"]))
            self.assertIsNone(read_record(root, "Example9999"))
            self.assertIsNone(read_record(root, "Example4242"))

    def test_answers_names_another_directory_of_the_same_shape(self):
        with tempfile.TemporaryDirectory() as root, tempfile.TemporaryDirectory() as run:
            write_benchmark(root, "Example0001", "Core.json", CORE)
            # A verifier destination holds <ID>/Counterexample.json directly,
            # and a harness run directory holds the same one level down.
            destination = Path(run) / "verifier" / "Example0013"
            destination.mkdir(parents=True)
            (destination / "Counterexample.json").write_text(
                json.dumps(COUNTEREXAMPLE), encoding="utf-8")
            expected = ("candidate_counterexample", COUNTEREXAMPLE["instance"])
            self.assertEqual(read_record(root, "Example0013", Path(run) / "verifier"), expected)
            self.assertEqual(read_record(root, "Example0013", run), expected)
            # The named directory replaces the repository's own records.
            self.assertIsNone(read_record(root, "Example0001", run))
            self.assertIsNone(read_record(root, "Example0013"))

    def test_an_identity_that_could_escape_the_benchmark_tree_is_refused(self):
        for identity in ("..", "../Example0001", "", "a/b"):
            with self.assertRaises(ReplayError):
                read_record("/nonexistent", identity)

    def test_the_proposal_is_bound_by_the_push_s_own_response_example(self):
        clauses = build_response(EXAMPLE, "candidate_clauses", ["x", "y"])
        self.assertEqual(clauses, {"kind": "candidate_clauses", "schema_version": 4,
                                   "binding": BINDING, "clauses": ["x", "y"], "dropped": []})
        instance = COUNTEREXAMPLE["instance"]
        self.assertEqual(build_response(EXAMPLE, "candidate_counterexample", instance),
                         {"kind": "candidate_counterexample", "schema_version": 4,
                          "binding": BINDING, "input": instance})

    def test_a_response_example_without_a_binding_is_refused(self):
        for example in ({"schema_version": 4}, {"binding": BINDING}, []):
            with self.assertRaises(ReplayError):
                build_response(example, "candidate_clauses", [])

    def test_the_push_identity_is_read_from_the_task(self):
        self.assertEqual(push_identity(observation("Example0001")), "Example0001")
        with self.assertRaises(ReplayError):
            push_identity({"feedback": {}})

    def test_the_repository_s_own_records_replay(self):
        """The two inputs the pipeline check is verified on, read for real."""
        kind, clauses = read_record(REPOSITORY, "Example0001")
        self.assertEqual(kind, "candidate_clauses")
        self.assertTrue(clauses and all(isinstance(item, str) for item in clauses))
        kind, instance = read_record(REPOSITORY, "Example0013")
        self.assertEqual(kind, "candidate_counterexample")
        self.assertTrue(instance["relations"])


class RecordSourceTests(unittest.TestCase):
    """The default source, refactored behind the same interface `serve` uses."""

    def test_replays_the_same_recorded_answer_for_every_request(self):
        with tempfile.TemporaryDirectory() as root:
            write_benchmark(root, "Example0001", "Core.json", CORE)
            source = RecordSource(root)
            first, reason = source.response(observation("Example0001"), EXAMPLE, 1)
            self.assertIsNone(reason)
            self.assertEqual(first["clauses"], ["(first = ∅[2])", "(second ⊆ later)"])
            second, _ = source.response(observation("Example0001"), EXAMPLE, 2)
            self.assertEqual(second["clauses"], first["clauses"])

    def test_declines_once_for_an_input_with_no_recorded_answer(self):
        source = RecordSource("/nonexistent")
        response, reason = source.response(observation("Example9999"), EXAMPLE, 1)
        self.assertIsNone(response)
        self.assertEqual(reason, "no recorded answer")


class PendingIdentityTableTests(unittest.TestCase):
    """Reading a recorded prompt's own "Pending clauses" section, and a live
    push's pending list, into the two tables a drop is remapped through.
    """

    def test_recorded_pending_sources_reads_clause_text_by_id(self):
        with tempfile.TemporaryDirectory() as root:
            directory = write_transcript_request(
                root, "Example0134", 4, pending=[
                    (0, "(oa_zTaX ⊆ yp_zTaX)", "(TaX_aux ⊆ TaX∞)"),
                    (1, "(op_zTaX ⊆ yp_zTaX)", "(op_zTaX ⊆ yp_zTaX)")])
            sources = recorded_pending_sources((directory / "prompt.txt").read_text())
            self.assertEqual(sources[0], "(oa_zTaX ⊆ yp_zTaX)")
            self.assertEqual(sources[1], "(op_zTaX ⊆ yp_zTaX)")
            self.assertEqual(set(sources), {0, 1})

    def test_live_pending_drop_references_key_by_the_clauses_own_text(self):
        reference = drop_reference(7, "live")
        push = observation_with_pending("Example0134", [
            (7, "(oa_zTaX ⊆ yp_zTaX)", "(TaX_aux ⊆ TaX∞)", reference),
            (8, "(op_zTaX ⊆ yp_zTaX)", None, None)])
        found = live_pending_drop_references(push)
        self.assertEqual(found, {"(oa_zTaX ⊆ yp_zTaX)": reference})

    def test_remap_drops_matches_by_text_and_omits_what_it_cannot_map(self):
        recorded_sources = {0: "(oa_zTaX ⊆ yp_zTaX)", 1: "(op_zTbY ⊆ yp_zTbY)"}
        live_reference = drop_reference(3, "live")
        live_sources = {"(oa_zTaX ⊆ yp_zTaX)": live_reference}
        omitted = []
        dropped = [{"clause": {"clause_id": 0}}, {"clause": {"clause_id": 1}},
                  {"clause": {"clause_id": 99}}]
        remapped = remap_drops(dropped, recorded_sources, live_sources, on_omit=omitted.append)
        self.assertEqual(remapped, [live_reference])
        self.assertEqual(omitted, [1, 99])


class TranscriptSourceTests(unittest.TestCase):
    """Replaying a retained run directory's own recorded responses."""

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def test_replays_each_request_s_own_recorded_content_rebound(self):
        write_transcript_request(self.root, "Example0001", 1,
                                 {"kind": "candidate_clauses", "schema_version": 4,
                                  "binding": {"stale": True}, "clauses": ["(a = b)"], "dropped": []})
        write_transcript_request(self.root, "Example0001", 2,
                                 {"kind": "candidate_clauses", "schema_version": 4,
                                  "binding": {"stale": True}, "clauses": ["(c = d)"], "dropped": []})
        source = TranscriptSource(self.root)
        push = observation("Example0001")
        first, reason = source.response(push, EXAMPLE, 1)
        self.assertIsNone(reason)
        self.assertEqual(first, {"kind": "candidate_clauses", "schema_version": 4,
                                 "binding": BINDING, "clauses": ["(a = b)"], "dropped": []})
        second, _ = source.response(push, EXAMPLE, 2)
        self.assertEqual(second["clauses"], ["(c = d)"])
        self.assertEqual(second["binding"], BINDING)

    def test_a_malformed_recorded_response_replays_unchanged_apart_from_binding(self):
        """A response that carried both `clauses`/`dropped` and `input` in the
        original run -- refused there as an envelope error -- reaches the live
        verifier the same way, so its refusal is exercised again.
        """
        malformed = {"kind": "candidate_counterexample", "schema_version": 4,
                    "binding": {"stale": True}, "clauses": [], "dropped": [],
                    "input": {"relations": []}}
        write_transcript_request(self.root, "Example4002", 2, malformed)
        source = TranscriptSource(self.root)
        response, reason = source.response(observation("Example4002"), EXAMPLE, 2)
        self.assertIsNone(reason)
        self.assertEqual(response, dict(malformed, binding=BINDING))

    def test_declines_when_a_consultation_recorded_no_submission(self):
        write_transcript_request(self.root, "Example0134", 5, payload=None)
        source = TranscriptSource(self.root)
        response, reason = source.response(observation("Example0134"), EXAMPLE, 5)
        self.assertIsNone(response)
        self.assertEqual(reason, "the recorded transcript has no submission for this consultation")

    def test_declines_at_the_end_of_the_transcript(self):
        write_transcript_request(self.root, "Example0162", 1,
                                 {"kind": "candidate_clauses", "schema_version": 4,
                                  "binding": {}, "clauses": [], "dropped": []})
        source = TranscriptSource(self.root)
        response, reason = source.response(observation("Example0162"), EXAMPLE, 2)
        self.assertIsNone(response)
        self.assertEqual(reason, "end of the recorded transcript")

    def test_a_dropped_clause_is_remapped_to_the_live_pushs_own_reference(self):
        write_transcript_request(
            self.root, "Example0134", 4,
            {"kind": "candidate_clauses", "schema_version": 4, "binding": {"stale": True},
             "clauses": [], "dropped": [drop_reference(0, "recorded")]},
            pending=[(0, "(oa_zTaX ⊆ yp_zTaX)", "(TaX_aux ⊆ TaX∞)")])
        live_reference = drop_reference(9, "live")
        push = observation_with_pending("Example0134",
                                        [(9, "(oa_zTaX ⊆ yp_zTaX)", "(TaX_aux ⊆ TaX∞)", live_reference)])
        source = TranscriptSource(self.root)
        response, reason = source.response(push, EXAMPLE, 4)
        self.assertIsNone(reason)
        self.assertEqual(response["dropped"], [live_reference])

    def test_an_unmappable_drop_is_omitted_and_reported(self):
        write_transcript_request(
            self.root, "Example0134", 4,
            {"kind": "candidate_clauses", "schema_version": 4, "binding": {"stale": True},
             "clauses": [], "dropped": [drop_reference(0, "recorded")]},
            pending=[(0, "(oa_zTaX ⊆ yp_zTaX)", "(TaX_aux ⊆ TaX∞)")])
        # The live push is not currently offering a drop for that clause's text.
        push = observation_with_pending("Example0134", [(9, "(oa_zTaX ⊆ yp_zTaX)", None, None)])
        source = TranscriptSource(self.root)
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            response, reason = source.response(push, EXAMPLE, 4)
        self.assertIsNone(reason)
        self.assertEqual(response["dropped"], [])
        self.assertIn("cannot map recorded drop (clause 0)", stderr.getvalue())


class FrozenTranscriptSourceTests(unittest.TestCase):
    """`TranscriptSource` reading a single `export-transcript` JSON file
    instead of a retained run directory -- the same public behavior, from a
    file whose `dropped` entries are already resolved to clause text.
    """

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / "transcript.json"

    def test_a_directory_and_a_file_are_told_apart_by_path_kind(self):
        write_transcript_json(self.path, {})
        self.assertIsNotNone(TranscriptSource(self.path)._file)
        self.assertIsNone(TranscriptSource(Path(self.directory.name))._file)

    def test_replays_each_request_s_own_recorded_content_rebound(self):
        write_transcript_json(self.path, {"Example0001": [
            (1, {"kind": "candidate_clauses", "schema_version": 4, "clauses": ["(a = b)"], "dropped": []}),
            (2, {"kind": "candidate_clauses", "schema_version": 4, "clauses": ["(c = d)"], "dropped": []})]})
        source = TranscriptSource(self.path)
        push = observation("Example0001")
        first, reason = source.response(push, EXAMPLE, 1)
        self.assertIsNone(reason)
        self.assertEqual(first, {"kind": "candidate_clauses", "schema_version": 4,
                                 "binding": BINDING, "clauses": ["(a = b)"], "dropped": []})
        second, _ = source.response(push, EXAMPLE, 2)
        self.assertEqual(second["clauses"], ["(c = d)"])

    def test_a_malformed_recorded_response_replays_unchanged_apart_from_binding(self):
        malformed = {"kind": "candidate_counterexample", "schema_version": 4, "clauses": [],
                    "dropped": [], "input": {"relations": []}}
        write_transcript_json(self.path, {"Example4002": [(2, malformed)]})
        source = TranscriptSource(self.path)
        response, reason = source.response(observation("Example4002"), EXAMPLE, 2)
        self.assertIsNone(reason)
        self.assertEqual(response, dict(malformed, binding=BINDING))

    def test_declines_when_a_consultation_recorded_no_submission(self):
        write_transcript_json(self.path, {"Example0134": [(5, None)]})
        source = TranscriptSource(self.path)
        response, reason = source.response(observation("Example0134"), EXAMPLE, 5)
        self.assertIsNone(response)
        self.assertEqual(reason, "the recorded transcript has no submission for this consultation")

    def test_declines_at_the_end_of_the_transcript(self):
        write_transcript_json(self.path, {"Example0162": [
            (1, {"kind": "candidate_clauses", "schema_version": 4, "clauses": [], "dropped": []})]})
        source = TranscriptSource(self.path)
        response, reason = source.response(observation("Example0162"), EXAMPLE, 2)
        self.assertIsNone(response)
        self.assertEqual(reason, "end of the recorded transcript")

    def test_a_dropped_clause_is_remapped_to_the_live_pushs_own_reference_by_text(self):
        write_transcript_json(self.path, {"Example0134": [
            (4, {"kind": "candidate_clauses", "schema_version": 4, "clauses": [],
                "dropped": ["(oa_zTaX ⊆ yp_zTaX)"]})]})
        live_reference = drop_reference(9, "live")
        push = observation_with_pending("Example0134",
                                        [(9, "(oa_zTaX ⊆ yp_zTaX)", "(TaX_aux ⊆ TaX∞)", live_reference)])
        source = TranscriptSource(self.path)
        response, reason = source.response(push, EXAMPLE, 4)
        self.assertIsNone(reason)
        self.assertEqual(response["dropped"], [live_reference])

    def test_an_unresolved_drop_null_is_omitted_and_reported(self):
        write_transcript_json(self.path, {"Example0134": [
            (4, {"kind": "candidate_clauses", "schema_version": 4, "clauses": [], "dropped": [None]})]})
        push = observation_with_pending("Example0134", [])
        source = TranscriptSource(self.path)
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            response, reason = source.response(push, EXAMPLE, 4)
        self.assertIsNone(reason)
        self.assertEqual(response["dropped"], [])
        self.assertIn("cannot map recorded drop", stderr.getvalue())

    def test_a_non_object_document_is_refused(self):
        Path(self.path).write_text("[]", encoding="utf-8")
        with self.assertRaises(ReplayError):
            TranscriptSource(self.path)

    def test_the_wrong_kind_is_refused(self):
        Path(self.path).write_text(json.dumps({"kind": "something_else"}), encoding="utf-8")
        with self.assertRaises(ReplayError):
            TranscriptSource(self.path)


class FakeHost:
    """Just enough of B to drive one endpoint over the real socket."""

    def __init__(self, directory):
        self.path = str(Path(directory) / "endpoint.sock")
        self.token = "9" * 64
        self.listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.listener.bind(self.path)
        self.listener.listen(1)
        self.listener.settimeout(60)
        self.stream = None
        self.sent = self.received = 0
        self.request_id = None

    def start(self, repository, *arguments):
        environment = dict(os.environ, WHIEL_PROPOSER_SOCKET=self.path,
                           WHIEL_PROPOSER_TOKEN=self.token)
        self.child = subprocess.Popen(
            [sys.executable, str(TOOL), "--repo", str(repository), *arguments],
            env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.stream, _ = self.listener.accept()
        self.stream.settimeout(60)
        return self.child

    def close(self):
        for stream in (self.stream, self.listener):
            if stream is not None:
                stream.close()

    def _exact(self, length):
        value = bytearray()
        while len(value) < length:
            part = self.stream.recv(min(length - len(value), 65536))
            if not part:
                raise EOFError("the endpoint closed")
            value.extend(part)
        return bytes(value)

    def send(self, kind, attachments=(), **fields):
        header = json.dumps({"wire_version": 3, "endpoint_token": self.token,
                             "sequence": self.sent, "request_id": self.request_id,
                             "operation": {"kind": kind, **fields}},
                            ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        self.stream.sendall(struct.pack(">I", len(header)) + header + b"".join(attachments))
        self.sent += 1

    def receive(self):
        size, = struct.unpack(">I", self._exact(4))
        frame = json.loads(self._exact(size))
        assert frame["wire_version"] == 3 and frame["endpoint_token"] == self.token
        assert frame["sequence"] == self.received, frame
        self.received += 1
        operation = frame["operation"]
        attachment = None
        if operation["kind"] == "submit":
            attachment = self._exact(operation["bytes"])
        return frame, attachment

    def handshake(self):
        frame, _ = self.receive()
        assert frame["operation"]["kind"] == "hello", frame
        assert frame["request_id"] is None
        self.send("ready", api={"version": "3.0.0", "operations": []})
        return frame["operation"]["capabilities"]

    def request(self, request_id, identity, example=EXAMPLE):
        self.request_id = request_id
        push = json.dumps(observation(identity)).encode("utf-8")
        reply = json.dumps(example).encode("utf-8")
        self.send("request", (push, reply), observation_bytes=len(push),
                  response_example_bytes=len(reply), remaining_request_budget_ns=None)


class ExchangeTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.host = FakeHost(self.root)
        self.addCleanup(self.host.close)

    def finish(self, child, expected=0):
        stdout, stderr = child.communicate(timeout=60)
        self.assertEqual(child.returncode, expected, stderr.decode())
        return stderr.decode()

    def close_endpoint(self):
        self.host.request_id = None
        self.host.send("shutdown", reason="complete")
        frame, _ = self.host.receive()
        self.assertEqual(frame["operation"]["kind"], "closed")

    def answer(self, request_id, identity):
        """One full request: return the proposal the endpoint submitted."""
        self.host.request(request_id, identity)
        frame, payload = self.host.receive()
        self.assertEqual(frame["operation"]["kind"], "submit", frame)
        self.assertEqual(frame["request_id"], request_id)
        self.assertEqual(frame["operation"]["bytes"], len(payload))
        self.host.send("submitted")
        closing, _ = self.host.receive()
        self.assertEqual(closing["operation"]["kind"], "complete")
        self.assertEqual(closing["operation"]["outcome"], "response")
        self.host.send("request_closed")
        return json.loads(payload)

    def test_a_valid_case_submits_its_recorded_core_and_completes(self):
        write_benchmark(self.root, "Example0001", "Core.json", CORE)
        log = self.root / "replay.jsonl"
        child = self.host.start(self.root, "--log", str(log))
        capabilities = self.host.handshake()
        self.assertEqual(capabilities["version"], "3.0.0")
        self.assertIn("validate_clauses", capabilities["supported_operations"])
        proposal = self.answer(1, "Example0001")
        self.assertEqual(proposal, {"kind": "candidate_clauses", "schema_version": 4,
                                    "binding": BINDING, "dropped": [],
                                    "clauses": ["(first = ∅[2])", "(second ⊆ later)"]})
        self.close_endpoint()
        self.finish(child)
        kinds = [json.loads(line)["kind"] for line in log.read_bytes().splitlines()]
        self.assertEqual(kinds, ["ready", "request", "submitted", "complete", "closed"])

    def test_an_invalid_case_submits_its_recorded_counterexample(self):
        write_benchmark(self.root, "Example0013", "Counterexample.json", COUNTEREXAMPLE)
        child = self.host.start(self.root)
        self.host.handshake()
        proposal = self.answer(1, "Example0013")
        self.assertEqual(proposal, {"kind": "candidate_counterexample", "schema_version": 4,
                                    "binding": BINDING, "input": COUNTEREXAMPLE["instance"]})
        self.close_endpoint()
        self.finish(child)

    def test_a_correction_round_replays_the_same_answer_on_a_new_binding(self):
        write_benchmark(self.root, "Example0001", "Core.json", CORE)
        child = self.host.start(self.root)
        self.host.handshake()
        first = self.answer(1, "Example0001")
        second_binding = dict(BINDING, request_digest="1" * 64, validation_ordinal=1)
        self.host.request(2, "Example0001", dict(EXAMPLE, binding=second_binding))
        frame, payload = self.host.receive()
        self.assertEqual(frame["operation"]["kind"], "submit")
        second = json.loads(payload)
        self.assertEqual(second["binding"], second_binding)
        self.assertEqual(second["clauses"], first["clauses"])
        self.host.send("submitted")
        closing, _ = self.host.receive()
        self.assertEqual(closing["operation"]["kind"], "complete")
        self.host.send("request_closed")
        self.close_endpoint()
        self.finish(child)

    def test_a_repeated_request_after_a_decline_is_declined_again_not_a_crash(self):
        """B is not required to close right after `source_exhausted`; a
        further push for the same exhausted input is declined the same way,
        rather than treated as a protocol violation.
        """
        (self.root / "Benchmark" / "Example9999").mkdir(parents=True)
        child = self.host.start(self.root)
        self.host.handshake()
        self.host.request(1, "Example9999")
        frame, _ = self.host.receive()
        self.assertEqual(frame["operation"]["outcome"], "source_exhausted")
        self.host.send("request_closed")
        self.host.request(2, "Example9999")
        frame, _ = self.host.receive()
        self.assertEqual(frame["operation"]["kind"], "complete")
        self.assertEqual(frame["operation"]["outcome"], "source_exhausted")
        self.host.send("request_closed")
        self.close_endpoint()
        self.finish(child)

    def test_an_input_with_no_recorded_answer_declines_and_releases_the_endpoint(self):
        (self.root / "Benchmark" / "Example9999").mkdir(parents=True)
        child = self.host.start(self.root)
        self.host.handshake()
        self.host.request(1, "Example9999")
        frame, _ = self.host.receive()
        self.assertEqual(frame["operation"]["kind"], "complete")
        self.assertEqual(frame["operation"]["outcome"], "source_exhausted")
        self.host.send("request_closed")
        # A decline is exhaustion, not a reason to hang up before B says to:
        # the endpoint waits for the same `shutdown` an accepted input gets.
        self.close_endpoint()
        stderr = self.finish(child)
        self.assertIn("no recorded answer", stderr)

    def test_the_request_bound_stops_a_run_that_never_settles(self):
        write_benchmark(self.root, "Example0001", "Core.json", CORE)
        child = self.host.start(self.root, "--max-requests", "1")
        self.host.handshake()
        self.answer(1, "Example0001")
        self.host.request(2, "Example0001")
        # Not a completed decline, which the verifier would reopen as a fresh
        # consultation: the connection closes, and that ends the input.
        with self.assertRaises(EOFError):
            self.host.receive()
        stderr = self.finish(child)
        self.assertIn("more than 1 requests", stderr)
        self.assertIn("ending the search", stderr)

    def test_a_cancelled_request_is_completed_as_a_failure(self):
        write_benchmark(self.root, "Example0001", "Core.json", CORE)
        child = self.host.start(self.root)
        self.host.handshake()
        self.host.request(1, "Example0001")
        frame, _ = self.host.receive()
        self.assertEqual(frame["operation"]["kind"], "submit")
        self.host.send("cancel", reason="deadline")
        closing, _ = self.host.receive()
        self.assertEqual(closing["operation"]["kind"], "complete")
        self.assertEqual(closing["operation"]["outcome"], "failure")
        self.host.send("request_closed")
        self.close_endpoint()
        self.finish(child)

    def test_a_wrong_endpoint_token_fails_the_proposer_rather_than_answering(self):
        write_benchmark(self.root, "Example0001", "Core.json", CORE)
        child = self.host.start(self.root)
        self.host.handshake()
        self.host.token = "7" * 64
        self.host.request(1, "Example0001")
        self.assertIn("wrong API identity", self.finish(child, expected=1))

    def test_transcript_mode_replays_a_retained_runs_own_response_over_the_wire(self):
        transcript = self.root / "transcript"
        write_transcript_request(transcript, "Example0001", 1,
                                 {"kind": "candidate_clauses", "schema_version": 4,
                                  "binding": {"stale": True}, "clauses": ["(a = b)"], "dropped": []})
        child = self.host.start(self.root, "--transcript", str(transcript))
        self.host.handshake()
        proposal = self.answer(1, "Example0001")
        self.assertEqual(proposal, {"kind": "candidate_clauses", "schema_version": 4,
                                    "binding": BINDING, "clauses": ["(a = b)"], "dropped": []})
        self.close_endpoint()
        self.finish(child)

    def test_transcript_mode_replays_a_frozen_transcript_file_over_the_wire(self):
        transcript = self.root / "transcript.json"
        write_transcript_json(transcript, {"Example0001": [
            (1, {"kind": "candidate_clauses", "schema_version": 4, "clauses": ["(a = b)"], "dropped": []})]})
        child = self.host.start(self.root, "--transcript", str(transcript))
        self.host.handshake()
        proposal = self.answer(1, "Example0001")
        self.assertEqual(proposal, {"kind": "candidate_clauses", "schema_version": 4,
                                    "binding": BINDING, "clauses": ["(a = b)"], "dropped": []})
        self.close_endpoint()
        self.finish(child)

    def test_transcript_mode_closes_the_connection_past_the_end_of_the_transcript(self):
        """Past the end of the transcript the proposer neither declines nor
        holds the request open: it closes the connection at once, so the
        verifier reads its endpoint as having exited rather than republishing
        a completed decline to a fresh consultation on the same exhausted
        input (the loop `serve`'s docstring measures and describes). The exit
        is clean (status 0); nothing further arrives on the wire.
        """
        transcript = self.root / "transcript2"
        write_transcript_request(transcript, "Example0001", 1,
                                 {"kind": "candidate_clauses", "schema_version": 4,
                                  "binding": {}, "clauses": [], "dropped": []})
        child = self.host.start(self.root, "--transcript", str(transcript), "--max-requests", "5")
        self.host.handshake()
        self.answer(1, "Example0001")
        self.host.request(2, "Example0001")
        with self.assertRaises(EOFError):
            self.host.receive()
        self.assertIn("ending the search", self.finish(child))

    def test_a_transcript_longer_than_the_answer_replay_cap_is_replayed_whole(self):
        """The few-requests cap belongs to an answer replay. A transcript says
        how many rounds it has, so every one of them is answered; stopping at
        the cap would replay a shorter search than the one recorded.
        """
        transcript = self.root / "transcript-long"
        rounds = 6
        for number in range(1, rounds + 1):
            write_transcript_request(transcript, "Example0001", number,
                                     {"kind": "candidate_clauses", "schema_version": 4,
                                      "binding": {}, "clauses": [], "dropped": []})
        child = self.host.start(self.root, "--transcript", str(transcript))
        self.host.handshake()
        for number in range(1, rounds + 1):
            self.answer(number, "Example0001")
        self.host.request(rounds + 1, "Example0001")
        with self.assertRaises(EOFError):
            self.host.receive()
        self.assertIn("ending the search", self.finish(child))

    def test_transcript_mode_closes_the_connection_when_the_original_recorded_no_submission(self):
        """The other decline reason -- a consultation the original proposer
        timed out or crashed on -- ends the search the same way as the end of
        the transcript; both are `TranscriptSource` declines.
        """
        transcript = self.root / "transcript3"
        write_transcript_request(transcript, "Example0134", 1,
                                 {"kind": "candidate_clauses", "schema_version": 4,
                                  "binding": {}, "clauses": [], "dropped": []})
        write_transcript_request(transcript, "Example0134", 2, payload=None)
        child = self.host.start(self.root, "--transcript", str(transcript), "--max-requests", "5")
        self.host.handshake()
        self.answer(1, "Example0134")
        self.host.request(2, "Example0134")
        with self.assertRaises(EOFError):
            self.host.receive()
        stderr = self.finish(child)
        self.assertIn("ending the search", stderr)
        self.assertIn("no submission for this consultation", stderr)

    def test_the_proposer_refuses_to_start_without_b_s_environment(self):
        child = subprocess.run([sys.executable, str(TOOL), "--repo", str(self.root)],
                               capture_output=True,
                               env={key: value for key, value in os.environ.items()
                                    if not key.startswith("WHIEL_PROPOSER_")})
        self.assertEqual(child.returncode, 2)
        self.assertIn("WHIEL_PROPOSER_SOCKET", child.stderr.decode())


if __name__ == "__main__":
    unittest.main()
