# Author: Fangzhu Shen
"""Freezing a run directory's transcript into one small, publishable file."""

import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest

from agent_houdini.export_run import find_hits
from agent_houdini.export_transcript import (
    ExportTranscriptError, build_transcript, export_transcript,
)


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False), encoding="utf-8")


def _frame_bytes(event):
    """One `consultation-records` artifact, in the shape `experiment.py`'s
    `_frame_payload` reads: a JSON object whose `payload` is the event's own
    JSON, re-encoded as a list of byte values.
    """
    return json.dumps({"payload": list(json.dumps(event).encode("utf-8"))}).encode("utf-8")


def write_verifier_records(run_dir, identity, *, status, core_rows=None,
                           counterexample_instance=None, final_state=None,
                           attempt_history=None, failure_kind=None):
    directory = Path(run_dir) / "verifier" / identity
    result = {"status": status, "input": identity}
    if failure_kind is not None:
        result["failure_kind"] = failure_kind
    write_json(directory / "result.json", result)
    if core_rows is not None:
        write_json(directory / "Core.json",
                  {"kind": "whiel_framework_ii_core_rows", "version": 1, "rows": core_rows})
    if counterexample_instance is not None:
        write_json(directory / "Counterexample.json",
                  {"kind": "whiel_framework_ii_counterexample", "version": 1,
                   "instance": counterexample_instance})
    artifacts_dir = directory / "artifacts" / "run-test"
    artifacts_dir.mkdir(parents=True, exist_ok=True)
    artifacts = []
    if attempt_history is not None:
        write_json(artifacts_dir / "attempt-history.json", attempt_history)
        artifacts.append({"scope": ["root", "attempt-history"], "relative_path": "attempt-history.json"})
    if final_state is not None:
        event = {"event": {"kind": "final_owner_projection", "projection": {"state": final_state}}}
        (artifacts_dir / "frame-0.json").write_bytes(_frame_bytes(event))
        artifacts.append({"scope": ["root", "consultation-records"], "relative_path": "frame-0.json"})
    write_json(artifacts_dir / "manifest.json", {"artifacts": artifacts})
    return directory


def write_request(run_dir, identity, number, *, payload=None, pending=(), consultation=None):
    """One `agent/<identity>/request-N/`: a `submissions.jsonl` (or none,
    for a consultation the original proposer never answered) and, when
    `pending` names clauses, a `prompt.txt` whose "Pending clauses" section
    shows them, the shape `export_transcript.py`'s own drop resolution reads.
    `consultation`, when given, is this request's own consultation number
    (`export_transcript.py`'s `_consultation_number` reads it from the same
    task header a real prompt carries); omitted, the request is read as its
    own single-request round, matching a prompt with no task header at all.
    """
    directory = Path(run_dir) / "agent" / identity / f"request-{number}"
    directory.mkdir(parents=True, exist_ok=True)
    (Path(run_dir) / "agent" / identity / "events.jsonl").touch()
    if payload is not None:
        (directory / "submissions.jsonl").write_text(
            json.dumps({"submission": 1, "payload": json.dumps(payload, ensure_ascii=False)}) + "\n",
            encoding="utf-8")
    lines = []
    if consultation is not None:
        lines.append(f"# Task {identity} — consultation {consultation}")
        lines.append("")
    lines.append(f"# Pending clauses ({len(pending)})")
    lines.append("")
    for identifier, source in pending:
        lines.append(f"    clause {identifier}  minimum level 1  current level 1  "
                     "origin submitted  drop_reference: yes")
        lines.append(f"        {source}")
    lines += ["", "# Last round (0 clauses)", ""]
    (directory / "prompt.txt").write_text("\n".join(lines), encoding="utf-8")
    return directory


def write_run(run_dir, *, provider="claude", model="m1", reasoning_effort="low",
             controls=None):
    (Path(run_dir) / "agent").mkdir(parents=True, exist_ok=True)
    (Path(run_dir) / "verifier").mkdir(parents=True, exist_ok=True)
    write_json(Path(run_dir) / "run.json",
              {"spec": {"provider": provider, "model": model, "reasoning_effort": reasoning_effort,
                       "verifier": "/abs/should/not/appear/whiel-symbolic"}})
    write_json(Path(run_dir) / "verifier" / "campaign-settings.json",
              {"schema_version": 3, "inputs": ["Example0001"],
               "controls": controls if controls is not None else {"search_limit_seconds": 90, "workers": 4},
               "proposer": {"executable": "/abs/should/not/appear/python3",
                            "arguments": ["--agent-log-parent", "/abs/should/not/appear/agent"]}})


CATALOG = {"catalog": {"records": [
    {"id": 0, "canonical_source": "(a = b)"},
    {"id": 1, "canonical_source": "(c ⊆ d)"},
]}}


class BuildTranscriptTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def test_refuses_a_directory_that_is_not_a_harness_run(self):
        with self.assertRaises(ExportTranscriptError):
            build_transcript(self.root)

    def test_reads_provider_model_and_effort_from_run_json(self):
        write_run(self.root, provider="codex", model="gpt-x", reasoning_effort="high")
        write_verifier_records(self.root, "Example0001", status="search_timeout")
        document = build_transcript(self.root)
        self.assertEqual(document["provider"], "codex")
        self.assertEqual(document["model"], "gpt-x")
        self.assertEqual(document["reasoning_effort"], "high")
        self.assertEqual(document["kind"], "whiel_transcript_replay")

    def test_controls_are_kept_but_the_proposer_selection_and_input_list_are_not(self):
        write_run(self.root, controls={"search_limit_seconds": 42, "workers": 2})
        write_verifier_records(self.root, "Example0001", status="search_timeout")
        document = build_transcript(self.root)
        self.assertEqual(document["controls"], {"search_limit_seconds": 42, "workers": 2})

    def test_an_accepted_valid_input_carries_its_core_with_levels(self):
        write_run(self.root)
        write_verifier_records(
            self.root, "Example0001", status="valid_uncertified",
            core_rows=[{"level": 1, "source": "(c ⊆ d)"}, {"level": 0, "source": "(a = b)"}],
            final_state=CATALOG,
            attempt_history={"ledger": [
                {"row": "attempt", "clause": 0, "role": "initialization", "level": 0,
                 "outcome": {"kind": "proved"}}]})
        document = build_transcript(self.root)
        expected = document["inputs"]["Example0001"]["expected"]
        self.assertEqual(expected["verdict_class"], "accepted_valid")
        self.assertEqual({row["source"]: row["level"] for row in expected["core"]},
                         {"(c ⊆ d)": 1, "(a = b)": 0})
        self.assertIsNone(expected["counterexample"])
        self.assertEqual(expected["ledger"], [["(a = b)", "initialization", 0, "proved"]])

    def test_an_accepted_invalid_input_carries_its_counterexample_instance(self):
        write_run(self.root)
        instance = {"relations": [{"name": "p::E", "rows": [["num:0", "num:1"]]}]}
        write_verifier_records(self.root, "Example0001", status="invalid_uncertified",
                               counterexample_instance=instance)
        document = build_transcript(self.root)
        expected = document["inputs"]["Example0001"]["expected"]
        self.assertEqual(expected["verdict_class"], "accepted_invalid")
        self.assertIsNone(expected["core"])
        self.assertEqual(expected["counterexample"],
                         {"relations": [{"name": "p::E", "rows": [["num:0", "num:1"]]}]})

    def test_a_non_accepted_input_carries_neither_core_nor_counterexample(self):
        write_run(self.root)
        write_verifier_records(self.root, "Example0001", status="search_timeout")
        document = build_transcript(self.root)
        expected = document["inputs"]["Example0001"]["expected"]
        self.assertEqual(expected["verdict_class"], "not_accepted")
        self.assertIsNone(expected["core"])
        self.assertIsNone(expected["counterexample"])

    def test_requests_are_read_in_round_order_with_binding_removed(self):
        write_run(self.root)
        write_verifier_records(self.root, "Example0001", status="search_timeout")
        write_request(self.root, "Example0001", 2,
                      payload={"kind": "candidate_clauses", "schema_version": 4,
                              "binding": {"stale": True}, "clauses": ["(c = d)"], "dropped": []})
        write_request(self.root, "Example0001", 1,
                      payload={"kind": "candidate_clauses", "schema_version": 4,
                              "binding": {"stale": True}, "clauses": ["(a = b)"], "dropped": []})
        document = build_transcript(self.root)
        requests = document["inputs"]["Example0001"]["requests"]
        self.assertEqual([item["number"] for item in requests], [1, 2])
        self.assertNotIn("binding", requests[0]["submission"])
        self.assertEqual(requests[0]["submission"]["clauses"], ["(a = b)"])
        self.assertEqual(requests[1]["submission"]["clauses"], ["(c = d)"])

    def test_a_consultation_with_no_submission_is_null(self):
        write_run(self.root)
        write_verifier_records(self.root, "Example0001", status="search_timeout")
        write_request(self.root, "Example0001", 1, payload=None)
        document = build_transcript(self.root)
        self.assertIsNone(document["inputs"]["Example0001"]["requests"][0]["submission"])
        self.assertTrue(document["inputs"]["Example0001"]["requests"][0]["cut_off"])

    def test_a_corrected_consultation_exports_only_its_final_uncorrected_submission(self):
        """A correction never runs a round (B's own prompt says so verbatim),
        so the earlier, corrected-away attempt must not become a replayable
        round: only request 2 -- the same consultation's final content --
        should survive into the transcript's one round for it.
        """
        write_run(self.root)
        write_verifier_records(self.root, "Example0001", status="search_timeout")
        write_request(self.root, "Example0001", 1, consultation=1,
                      payload={"kind": "candidate_clauses", "schema_version": 4, "binding": {},
                              "clauses": ["(never checked)"], "dropped": []})
        write_request(self.root, "Example0001", 2, consultation=1,
                      payload={"kind": "candidate_clauses", "schema_version": 4, "binding": {},
                              "clauses": ["(a = b)"], "dropped": []})
        write_request(self.root, "Example0001", 3, consultation=2,
                      payload={"kind": "candidate_clauses", "schema_version": 4, "binding": {},
                              "clauses": ["(c = d)"], "dropped": []})
        document = build_transcript(self.root)
        requests = document["inputs"]["Example0001"]["requests"]
        self.assertEqual(len(requests), 2)
        self.assertEqual(requests[0]["submission"]["clauses"], ["(a = b)"])
        self.assertEqual(requests[1]["submission"]["clauses"], ["(c = d)"])
        self.assertFalse(requests[0]["cut_off"])
        self.assertFalse(requests[1]["cut_off"])

    def test_a_correction_cycle_cut_off_before_a_final_resubmission_is_one_cut_off_round(self):
        write_run(self.root)
        write_verifier_records(self.root, "Example0001", status="search_timeout")
        write_request(self.root, "Example0001", 1, consultation=1,
                      payload={"kind": "candidate_clauses", "schema_version": 4, "binding": {},
                              "clauses": ["(a = b)"], "dropped": []})
        write_request(self.root, "Example0001", 2, consultation=1, payload=None)
        document = build_transcript(self.root)
        requests = document["inputs"]["Example0001"]["requests"]
        self.assertEqual(len(requests), 1)
        self.assertIsNone(requests[0]["submission"])
        self.assertTrue(requests[0]["cut_off"])

    def test_the_expected_ledger_keeps_every_entry_a_cut_off_round_never_touches(self):
        """A cut-off round is never replayed (`_input_requests`), and B never
        admits a clause on a round it cancels, so the expected ledger needs
        no per-clause filtering of its own: every entry the original's own
        ledger records -- whether or not any round explicitly proposed its
        clause (the task's own ambient/precondition clauses never are) --
        already belongs to a round that completed.
        """
        write_run(self.root)
        write_verifier_records(
            self.root, "Example0001", status="search_timeout", failure_kind="OverallTimeout",
            final_state=CATALOG,
            attempt_history={"consultations": [{"outcome": "accepted"}, {"outcome": "cancelled"}],
                             "ledger": [
                {"row": "attempt", "clause": 0, "role": "initialization", "level": 0,
                 "outcome": {"kind": "proved"}},
                {"row": "attempt", "clause": 1, "role": "initialization", "level": 0,
                 "outcome": {"kind": "proved"}}]})
        write_request(self.root, "Example0001", 1, consultation=1,
                      payload={"kind": "candidate_clauses", "schema_version": 4, "binding": {},
                              "clauses": ["(a = b)"], "dropped": []})
        write_request(self.root, "Example0001", 2, consultation=2, payload=None)
        document = build_transcript(self.root)
        expected = document["inputs"]["Example0001"]["expected"]
        self.assertEqual(expected["ledger"], [["(a = b)", "initialization", 0, "proved"],
                                              ["(c ⊆ d)", "initialization", 0, "proved"]])
        self.assertEqual(expected["completed_rounds"], 1)

    def test_the_ledger_reads_a_clause_with_a_shorter_display_spelling_by_its_canonical_text(self):
        """A submitted clause is always canonical text (`(op_zT ⊆ op_zS)`);
        the catalog can additionally carry a shorter `display` spelling
        (`(T ⊆ S)`) for the same clause. The ledger must be read at the
        canonical spelling, matching `Core.json` and a submitted proposal,
        not the display text `experiment.py`'s own digest prefers -- a real
        mismatch first seen comparing a real weak-model run's own replay.
        """
        write_run(self.root)
        write_verifier_records(
            self.root, "Example0001", status="search_timeout", failure_kind="OverallTimeout",
            final_state={"catalog": {"records": [
                {"id": 0, "canonical_source": "(op_zT ⊆ op_zS)", "display": "(T ⊆ S)"}]}},
            attempt_history={"consultations": [{"outcome": "accepted"}],
                             "ledger": [
                {"row": "attempt", "clause": 0, "role": "initialization", "level": 0,
                 "outcome": {"kind": "proved"}}]})
        write_request(self.root, "Example0001", 1, consultation=1,
                      payload={"kind": "candidate_clauses", "schema_version": 4, "binding": {},
                              "clauses": ["(op_zT ⊆ op_zS)"], "dropped": []})
        document = build_transcript(self.root)
        expected = document["inputs"]["Example0001"]["expected"]
        self.assertEqual(expected["ledger"], [["(op_zT ⊆ op_zS)", "initialization", 0, "proved"]])

    def test_a_ledger_entry_falls_back_to_an_id_label_without_a_resolvable_catalog(self):
        """A deadline that lands before any `final_owner_projection` leaves
        every ledger row with a run-local `#<id>` fallback label instead of
        real clause text (no `final_state` to read it from); this is
        reported on stderr rather than silently producing an unreadable file.
        """
        write_run(self.root)
        write_verifier_records(
            self.root, "Example0001", status="search_timeout", failure_kind="OverallTimeout",
            final_state=None,
            attempt_history={"consultations": [{"outcome": "accepted"}],
                             "ledger": [
                {"row": "attempt", "clause": 0, "role": "initialization", "level": 0,
                 "outcome": {"kind": "proved"}}]})
        write_request(self.root, "Example0001", 1, consultation=1,
                      payload={"kind": "candidate_clauses", "schema_version": 4, "binding": {},
                              "clauses": ["(a = b)"], "dropped": []})
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            document = build_transcript(self.root)
        expected = document["inputs"]["Example0001"]["expected"]
        self.assertEqual(expected["ledger"], [["#0", "initialization", 0, "proved"]])
        self.assertIn("no catalog was published", stderr.getvalue())

    def test_completed_rounds_counts_only_accepted_consultations(self):
        write_run(self.root)
        write_verifier_records(
            self.root, "Example0001", status="search_timeout", failure_kind="OverallTimeout",
            attempt_history={"consultations": [
                {"outcome": "accepted"}, {"outcome": "accepted"}, {"outcome": "cancelled"}]})
        document = build_transcript(self.root)
        self.assertEqual(document["inputs"]["Example0001"]["expected"]["completed_rounds"], 2)

    def test_zero_completed_rounds_when_the_limit_expired_before_any_consultation_finished(self):
        write_run(self.root)
        write_verifier_records(
            self.root, "Example0001", status="search_timeout", failure_kind="OverallTimeout",
            attempt_history={"consultations": [{"outcome": "cancelled"}]})
        document = build_transcript(self.root)
        self.assertEqual(document["inputs"]["Example0001"]["expected"]["completed_rounds"], 0)

    def test_a_malformed_submission_is_preserved_apart_from_binding(self):
        write_run(self.root)
        write_verifier_records(self.root, "Example0001", status="search_timeout")
        malformed = {"kind": "candidate_counterexample", "schema_version": 4, "binding": {"x": 1},
                    "clauses": [], "dropped": [], "input": {"relations": []}}
        write_request(self.root, "Example0001", 1, payload=malformed)
        document = build_transcript(self.root)
        submission = document["inputs"]["Example0001"]["requests"][0]["submission"]
        self.assertEqual(submission, {key: value for key, value in malformed.items() if key != "binding"})

    def test_a_dropped_clause_is_resolved_to_its_recorded_text(self):
        write_run(self.root)
        write_verifier_records(self.root, "Example0001", status="search_timeout")
        write_request(self.root, "Example0001", 1,
                      payload={"kind": "candidate_clauses", "schema_version": 4, "binding": {},
                              "clauses": [], "dropped": [
                                  {"clause": {"clause_id": 3, "record_digest": "r", "formula_digest": "f"},
                                   "consultation_digest": "c", "authorization_digest": "a"}]},
                      pending=[(3, "(e ⊆ f)")])
        document = build_transcript(self.root)
        submission = document["inputs"]["Example0001"]["requests"][0]["submission"]
        self.assertEqual(submission["dropped"], ["(e ⊆ f)"])
        # No digest of the original run survives into the frozen file.
        self.assertNotIn("record_digest", json.dumps(document))
        self.assertNotIn("consultation_digest", json.dumps(document))

    def test_an_unresolvable_dropped_clause_becomes_null_not_a_digest(self):
        write_run(self.root)
        write_verifier_records(self.root, "Example0001", status="search_timeout")
        write_request(self.root, "Example0001", 1,
                      payload={"kind": "candidate_clauses", "schema_version": 4, "binding": {},
                              "clauses": [], "dropped": [
                                  {"clause": {"clause_id": 9, "record_digest": "r", "formula_digest": "f"},
                                   "consultation_digest": "c", "authorization_digest": "a"}]})
        document = build_transcript(self.root)
        submission = document["inputs"]["Example0001"]["requests"][0]["submission"]
        self.assertEqual(submission["dropped"], [None])


class ExportTranscriptCommandTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name) / "run"
        write_run(self.root)
        write_verifier_records(self.root, "Example0001", status="valid_uncertified",
                               core_rows=[{"level": 0, "source": "(a = b)"}])
        self.out_path = Path(self.directory.name) / "transcript.json"

    def test_writes_a_scanned_transcript_file(self):
        status = export_transcript(self.root, self.out_path)
        self.assertEqual(status, 0)
        document = json.loads(self.out_path.read_text(encoding="utf-8"))
        self.assertEqual(document["kind"], "whiel_transcript_replay")
        # The recorded absolute paths this checkout would carry never reach
        # the frozen file -- the same check a collaborator export uses.
        self.assertEqual(find_hits(self.out_path.parent, skip_excluded=False), [])

    def test_refuses_an_existing_destination(self):
        self.out_path.write_text("{}", encoding="utf-8")
        status = export_transcript(self.root, self.out_path)
        self.assertEqual(status, 2)

    def test_refuses_a_non_run_directory(self):
        status = export_transcript(Path(self.directory.name), self.out_path)
        self.assertEqual(status, 2)
        self.assertFalse(self.out_path.exists())


if __name__ == "__main__":
    unittest.main()
