# Author: Fangzhu Shen
"""The three replay fidelity checks, against small synthetic run trees."""

import json
from pathlib import Path
import tempfile
import unittest

from agent_houdini.compare_runs import (
    CompareError, catalog_canonical_texts, check_accepted_records, check_ledgers, check_verdicts,
    compare, ledger_entries, read_side, render_report, verdict_class,
)
from agent_houdini.tests.test_export_transcript import write_json, write_verifier_records


class VerdictClassTests(unittest.TestCase):
    def test_valid_statuses_are_accepted_valid(self):
        self.assertEqual(verdict_class("valid"), "accepted_valid")
        self.assertEqual(verdict_class("valid_uncertified"), "accepted_valid")

    def test_invalid_statuses_are_accepted_invalid(self):
        self.assertEqual(verdict_class("invalid"), "accepted_invalid")
        self.assertEqual(verdict_class("invalid_uncertified"), "accepted_invalid")

    def test_everything_else_is_not_accepted(self):
        for status in ("search_timeout", "incomplete", "resource_exhausted",
                      "certification_failed", "input_changed", None, "made_up_status"):
            self.assertEqual(verdict_class(status), "not_accepted")


class CatalogCanonicalTextsTests(unittest.TestCase):
    def test_prefers_canonical_source_over_the_shorter_display_spelling(self):
        """The ledger's clause text must match what `Core.json` and a
        submitted `candidate_clauses` proposal both use -- canonical text --
        not the shorter `display` form `experiment.py`'s own digest prefers;
        an export-transcript filter that compared the two forms directly
        would never match anything (the bug this regression test catches).
        """
        state = {"catalog": {"records": [
            {"id": 0, "canonical_source": "(op_zT ⊆ op_zS)", "display": "(T ⊆ S)"},
            {"id": 1, "canonical_source": "(op_zE ⊆ op_zS)"}]}}
        self.assertEqual(catalog_canonical_texts(state),
                         {0: "(op_zT ⊆ op_zS)", 1: "(op_zE ⊆ op_zS)"})


class LedgerEntriesTests(unittest.TestCase):
    def test_only_attempt_rows_become_entries(self):
        rows = [
            {"row": "attempt", "clause": 0, "role": "initialization", "level": 0,
             "outcome": {"kind": "proved"}},
            {"row": "invalidation", "target": 0},
            {"row": "attempt", "clause": 1, "role": "maintenance", "level": 1,
             "outcome": {"kind": "inconclusive", "reason": "timed_out"}},
        ]
        entries = ledger_entries(rows, {0: "(a = b)", 1: "(c ⊆ d)"})
        self.assertEqual(entries, [("(a = b)", "initialization", 0, "proved"),
                                   ("(c ⊆ d)", "maintenance", 1, "inconclusive")])

    def test_a_clause_missing_from_the_catalog_falls_back_to_a_label(self):
        entries = ledger_entries([{"row": "attempt", "clause": 7, "role": "initialization",
                                   "level": 0, "outcome": {"kind": "proved"}}], {})
        self.assertEqual(entries, [("#7", "initialization", 0, "proved")])


def write_verifier_tree(root, inputs):
    """`inputs` maps identity -> kwargs for `write_verifier_records`."""
    for identity, kwargs in inputs.items():
        write_verifier_records(root, identity, **kwargs)


CATALOG = {"catalog": {"records": [{"id": 0, "canonical_source": "(a = b)"},
                                   {"id": 1, "canonical_source": "(c ⊆ d)"}]}}
# One completed consultation, so `completed_rounds` is 1 and these fixtures
# exercise the ordinary comparison path rather than "no completed round".
PROVED_LEDGER = {"consultations": [{"outcome": "accepted"}],
                 "ledger": [{"row": "attempt", "clause": 0, "role": "initialization", "level": 0,
                             "outcome": {"kind": "proved"}}]}


class ReadSideTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def test_a_harness_run_directory_is_read_through_its_verifier_subdirectory(self):
        run = self.root / "run"
        (run / "agent").mkdir(parents=True)
        write_verifier_tree(run, {"Example0001": {"status": "valid_uncertified"}})
        inputs, label = read_side(run)
        self.assertEqual(set(inputs), {"Example0001"})
        self.assertIn(str(run), label)

    def test_a_bare_verifier_destination_is_read_directly(self):
        bare = self.root / "bare"
        write_verifier_tree(bare, {"Example0001": {"status": "search_timeout"}})
        inputs, _ = read_side(bare)
        self.assertEqual(set(inputs), {"Example0001"})

    def test_a_transcript_file_is_read_as_the_original_side(self):
        transcript = self.root / "transcript.json"
        write_json(transcript, {"kind": "whiel_transcript_replay", "version": 1,
                                "inputs": {"Example0001": {"requests": [],
                                                          "expected": {"status": "valid_uncertified",
                                                                      "verdict_class": "accepted_valid",
                                                                      "core": [{"source": "(a = b)", "level": 0}],
                                                                      "counterexample": None, "ledger": []}}}})
        inputs, label = read_side(transcript)
        self.assertEqual(inputs["Example0001"]["verdict_class"], "accepted_valid")
        self.assertEqual(inputs["Example0001"]["core"], {"(a = b)": 0})
        self.assertIn("transcript", label)

    def test_an_unreadable_path_is_a_compare_error(self):
        with self.assertRaises(CompareError):
            read_side(self.root / "does-not-exist")

    def test_a_json_file_of_the_wrong_kind_is_refused(self):
        bad = self.root / "bad.json"
        write_json(bad, {"kind": "something_else"})
        with self.assertRaises(CompareError):
            read_side(bad)


class CheckVerdictsTests(unittest.TestCase):
    def test_matching_verdicts_pass(self):
        original = {"Example0001": {"status": "valid", "verdict_class": "accepted_valid"}}
        replay = {"Example0001": {"status": "valid_uncertified", "verdict_class": "accepted_valid"}}
        result = check_verdicts(original, replay, expect_different=set(), require_all=False)
        self.assertTrue(result["passed"])
        self.assertEqual(result["differences"], [])

    def test_a_mismatch_fails_unless_expected(self):
        original = {"Example0001": {"status": "valid", "verdict_class": "accepted_valid"}}
        replay = {"Example0001": {"status": "search_timeout", "verdict_class": "not_accepted"}}
        failing = check_verdicts(original, replay, expect_different=set(), require_all=False)
        self.assertFalse(failing["passed"])
        self.assertEqual(len(failing["differences"]), 1)
        passing = check_verdicts(original, replay, expect_different={"Example0001"}, require_all=False)
        self.assertTrue(passing["passed"])
        self.assertEqual(len(passing["differences"]), 1)  # still reported

    def test_an_input_in_only_one_run_is_reported_and_ignored_by_default(self):
        original = {"Example0001": {"status": "valid", "verdict_class": "accepted_valid"},
                   "Example0002": {"status": "valid", "verdict_class": "accepted_valid"}}
        replay = {"Example0001": {"status": "valid", "verdict_class": "accepted_valid"}}
        result = check_verdicts(original, replay, expect_different=set(), require_all=False)
        self.assertTrue(result["passed"])
        self.assertEqual(result["only_in_original"], ["Example0002"])

    def test_require_all_fails_on_a_missing_input(self):
        original = {"Example0001": {"status": "valid", "verdict_class": "accepted_valid"},
                   "Example0002": {"status": "valid", "verdict_class": "accepted_valid"}}
        replay = {"Example0001": {"status": "valid", "verdict_class": "accepted_valid"}}
        result = check_verdicts(original, replay, expect_different=set(), require_all=True)
        self.assertFalse(result["passed"])


class CheckAcceptedRecordsTests(unittest.TestCase):
    def test_the_same_core_as_a_set_with_levels_passes(self):
        original = {"Example0001": {"verdict_class": "accepted_valid",
                                    "core": {"(a = b)": 0, "(c ⊆ d)": 1}}}
        replay = {"Example0001": {"verdict_class": "accepted_valid",
                                  "core": {"(c ⊆ d)": 1, "(a = b)": 0}}}
        result = check_accepted_records(original, replay, expect_different=set(), require_all=False)
        self.assertTrue(result["passed"])

    def test_a_different_level_for_the_same_clause_fails(self):
        original = {"Example0001": {"verdict_class": "accepted_valid", "core": {"(a = b)": 0}}}
        replay = {"Example0001": {"verdict_class": "accepted_valid", "core": {"(a = b)": 1}}}
        result = check_accepted_records(original, replay, expect_different=set(), require_all=False)
        self.assertFalse(result["passed"])

    def test_a_different_clause_set_fails(self):
        original = {"Example0001": {"verdict_class": "accepted_valid", "core": {"(a = b)": 0}}}
        replay = {"Example0001": {"verdict_class": "accepted_valid",
                                  "core": {"(a = b)": 0, "(c ⊆ d)": 0}}}
        result = check_accepted_records(original, replay, expect_different=set(), require_all=False)
        self.assertFalse(result["passed"])

    def test_the_same_counterexample_instance_passes_row_order_ignored(self):
        original = {"Example0001": {"verdict_class": "accepted_invalid",
                                    "counterexample": {"p::E": frozenset({(1, 2), (0, 1)})}}}
        replay = {"Example0001": {"verdict_class": "accepted_invalid",
                                  "counterexample": {"p::E": frozenset({(0, 1), (1, 2)})}}}
        result = check_accepted_records(original, replay, expect_different=set(), require_all=False)
        self.assertTrue(result["passed"])

    def test_a_mismatched_verdict_class_is_left_to_the_first_check(self):
        original = {"Example0001": {"verdict_class": "accepted_valid", "core": {"(a = b)": 0}}}
        replay = {"Example0001": {"verdict_class": "not_accepted", "core": None,
                                  "counterexample": None}}
        result = check_accepted_records(original, replay, expect_different=set(), require_all=False)
        self.assertTrue(result["passed"])
        self.assertEqual(result["differences"], [])


class CheckLedgersTests(unittest.TestCase):
    def test_the_same_ledger_set_passes_ignoring_duplicates(self):
        original = {"Example0001": {"ledger": [("(a = b)", "initialization", 0, "proved"),
                                               ("(a = b)", "initialization", 0, "proved")]}}
        replay = {"Example0001": {"ledger": [("(a = b)", "initialization", 0, "proved")]}}
        result = check_ledgers(original, replay, expect_different=set(), require_all=False)
        self.assertTrue(result["passed"])

    def test_a_genuinely_different_outcome_fails(self):
        original = {"Example0001": {"ledger": [("(a = b)", "initialization", 0, "proved")]}}
        replay = {"Example0001": {"ledger": [("(a = b)", "initialization", 0, "refuted")]}}
        result = check_ledgers(original, replay, expect_different=set(), require_all=False)
        self.assertFalse(result["passed"])

    def test_an_inconclusive_entry_on_either_side_is_a_timing_difference_not_a_failure(self):
        original = {"Example0001": {"ledger": [("(a = b)", "initialization", 0, "inconclusive")]}}
        replay = {"Example0001": {"ledger": [("(a = b)", "initialization", 0, "proved")]}}
        result = check_ledgers(original, replay, expect_different=set(), require_all=False)
        self.assertTrue(result["passed"])
        self.assertEqual(result["differences"], [])
        self.assertEqual(len(result["timing_differences"]), 1)
        self.assertEqual(result["timing_differences"][0]["input"], "Example0001")

    def test_expect_different_reports_but_does_not_fail(self):
        original = {"Example0001": {"ledger": [("(a = b)", "initialization", 0, "proved")]}}
        replay = {"Example0001": {"ledger": [("(a = b)", "initialization", 0, "refuted")]}}
        result = check_ledgers(original, replay, expect_different={"Example0001"}, require_all=False)
        self.assertTrue(result["passed"])
        self.assertEqual(len(result["differences"]), 1)


class CompareEndToEndTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def test_an_identical_pair_of_synthetic_runs_passes_all_three_checks(self):
        original = self.root / "original"
        replay = self.root / "replay"
        for run in (original, replay):
            (run / "agent").mkdir(parents=True)
            write_verifier_records(run, "Example0001", status="valid_uncertified",
                                   core_rows=[{"level": 0, "source": "(a = b)"}],
                                   final_state=CATALOG, attempt_history=PROVED_LEDGER)
        report = compare(original, replay)
        self.assertTrue(report["passed"])
        for check in report["checks"]:
            self.assertTrue(check["passed"], check)

    def test_a_diverging_core_fails_only_the_second_check(self):
        original = self.root / "original"
        replay = self.root / "replay"
        (original / "agent").mkdir(parents=True)
        (replay / "agent").mkdir(parents=True)
        write_verifier_records(original, "Example0001", status="valid_uncertified",
                               core_rows=[{"level": 0, "source": "(a = b)"}],
                               final_state=CATALOG, attempt_history=PROVED_LEDGER)
        write_verifier_records(replay, "Example0001", status="valid_uncertified",
                               core_rows=[{"level": 0, "source": "(c ⊆ d)"}],
                               final_state=CATALOG, attempt_history=PROVED_LEDGER)
        report = compare(original, replay)
        self.assertFalse(report["passed"])
        names = {check["name"]: check["passed"] for check in report["checks"]}
        self.assertTrue(names["1st replay fidelity check"])
        self.assertFalse(names["2nd replay fidelity check"])

    def test_an_input_with_no_completed_round_is_reported_and_never_fails(self):
        """The search's own limit can expire before a single consultation
        finished (no `consultations` entry has `outcome: accepted`). All
        three checks then have nothing to compare this input against, so
        they report it under its own heading and never fail on its account
        -- even though its (empty) ledgers technically "match".
        """
        original = self.root / "original"
        replay = self.root / "replay"
        (original / "agent").mkdir(parents=True)
        (replay / "agent").mkdir(parents=True)
        never_completed = {"consultations": [{"outcome": "cancelled"}], "ledger": []}
        write_verifier_records(original, "Example0001", status="search_timeout",
                               failure_kind="OverallTimeout", attempt_history=never_completed)
        write_verifier_records(replay, "Example0001", status="incomplete",
                               attempt_history=never_completed)
        report = compare(original, replay)
        self.assertTrue(report["passed"])
        for check in report["checks"]:
            self.assertTrue(check["passed"])
            self.assertEqual(check["no_completed_round"], ["Example0001"])
            self.assertEqual(check["differences"], [])

    def test_a_real_difference_in_a_completed_round_still_fails(self):
        """The "no completed round" carve-out must not swallow a genuine
        difference in a round that DID complete: an input with at least one
        completed round is compared normally, in full.
        """
        original = self.root / "original"
        replay = self.root / "replay"
        (original / "agent").mkdir(parents=True)
        (replay / "agent").mkdir(parents=True)
        write_verifier_records(original, "Example0001", status="search_timeout",
                               failure_kind="OverallTimeout", final_state=CATALOG,
                               attempt_history=PROVED_LEDGER)
        refuted = {"consultations": [{"outcome": "accepted"}],
                  "ledger": [{"row": "attempt", "clause": 0, "role": "initialization", "level": 0,
                             "outcome": {"kind": "refuted"}}]}
        write_verifier_records(replay, "Example0001", status="search_timeout",
                               failure_kind="OverallTimeout", final_state=CATALOG,
                               attempt_history=refuted)
        report = compare(original, replay)
        self.assertFalse(report["passed"])
        ledger_check = report["checks"][2]
        self.assertFalse(ledger_check["passed"])
        self.assertEqual(ledger_check["no_completed_round"], [])

    def test_render_report_reads_as_text_with_pass_fail_per_check(self):
        original = self.root / "original"
        replay = self.root / "replay"
        (original / "agent").mkdir(parents=True)
        (replay / "agent").mkdir(parents=True)
        write_verifier_records(original, "Example0001", status="valid_uncertified")
        write_verifier_records(replay, "Example0001", status="valid_uncertified")
        report = compare(original, replay)
        text = render_report(report)
        self.assertIn("1st replay fidelity check: PASS", text)
        self.assertIn("2nd replay fidelity check: PASS", text)
        self.assertIn("3rd replay fidelity check: PASS", text)
        self.assertIn("overall: PASS", text)


if __name__ == "__main__":
    unittest.main()
