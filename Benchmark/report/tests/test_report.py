#!/usr/bin/env python3
"""Tests for Benchmark/report/build_report.py.

Run them with `python3 -m unittest discover -s Benchmark/report/tests`.

Six properties are covered: the input parser reads the five declarations of a case; the
automatic tags follow from the rules and the command; the status follows from the case
folder — its emitter-written certificate, else its frozen record, else neither — and not
from a metadata claim; a build in a copy that holds nothing but
`Benchmark/` produces the same bytes as a build in the repository (isolation); two builds
produce the same bytes (determinism); and a case folder can be added and removed with no
other edit anywhere (add-a-case).
"""
from __future__ import annotations

import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPORT_DIR = Path(__file__).resolve().parents[1]
CASES_DIR = REPORT_DIR.parent
SCRIPT = REPORT_DIR / "build_report.py"
# The files a build writes that must be byte-stable.
TRACKED_OUTPUTS = ["inventory.json", "benchmark_report.html", "benchmark_report.tex", "benchmark_tags.csv"]


def load_module():
    spec = importlib.util.spec_from_file_location("build_report_under_test", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


BR = load_module()


FIXTURE_INPUT = """-- Author: A. Collaborator
import Whiel.Concrete.Notation

/-
  A fixture input: the right-linear closure of the edge relation.

  Expected verdict: valid.
-/

namespace Whiel
namespace Benchmark
namespace Example9001

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, T, S} (arity: 2)
    {Seen} (arity: 1)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      T := ∅;
      S := (E ∪ (π[0, 3] (σ[#1 = #2] (E × T))));
      WHILE (S ≠ T) DO
        T := S;
        S := (E ∪ (π[0, 3] (σ[#1 = #2] (E × T))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (T ⊆ E)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

#eval inputPreproc.display

end Example9001
end Benchmark
end Whiel
"""

MINIMAL_INPUT = FIXTURE_INPUT.replace("Example9001", "Example9999")

EMITTED = BR.EMITTER_MARKER + "\n-- Do not edit by hand.\ntheorem placeholder : True := trivial\n"
HAND_WRITTEN = "-- Written by hand while the witness was being extracted.\ntheorem placeholder : True := trivial\n"
# A frozen record stands beside the input, not under Certificate/; only its presence is read.
RECORD = '{"kind": "fixture", "version": 1}\n'


class ParsingTest(unittest.TestCase):
    """The five declarations of a case are read out of its input file."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp)
        self.path = self.tmp / "Input.lean"
        self.path.write_text(FIXTURE_INPUT, encoding="utf-8")

    def test_parses_schema_pre_cmd_post(self):
        p = BR.parse_input(self.path)
        self.assertEqual(p["notation"], "canonical")
        self.assertEqual(p["arities"], {"E": 2, "T": 2, "S": 2, "Seen": 1})
        self.assertEqual(p["pre"].strip(), "true")
        self.assertEqual(p["post"], "(T ⊆ E)")
        self.assertTrue(p["cmd"].startswith("T := ∅;"))
        self.assertTrue(p["cmd"].rstrip().endswith("END"))
        self.assertIn("WHILE (S ≠ T) DO", p["cmd"])
        self.assertIn("right-linear closure", p["header"])

    def test_preproc_declaration_is_not_part_of_the_triple(self):
        p = BR.parse_input(self.path)
        self.assertNotIn("preprocess", p["cmd"])
        self.assertNotIn("display", p["post"])

    def test_summary_is_the_first_paragraph_of_the_header(self):
        p = BR.parse_input(self.path)
        self.assertEqual(BR.summary_of(p["header"], {}),
                         "A fixture input: the right-linear closure of the edge relation.")

    def test_command_analysis(self):
        p = BR.parse_input(self.path)
        info = BR.analyze_cmd(p["cmd"], p["arities"])
        self.assertEqual(info["top_loops"], 1)
        self.assertFalse(info["nested"])
        self.assertEqual(sorted(set(info["assigned"])), ["S", "T"])


class AutomaticTagTest(unittest.TestCase):
    """The three rule tags are computed, never read from curated.json."""

    def _tags(self, rules, case="Example9001", pre="true", post="(T ⊆ E)"):
        blocks = [{"label": "program", "text": "\n".join(rules), "provenance": "fixture"}]
        parsed = {"pre": pre, "cmd": "T := ∅", "post": post}
        cmdinfo = {"nonlinear_ra": False, "frontier": False}
        tags, _ = BR.compute_tags(case, parsed, cmdinfo, {}, blocks, set())
        return tags

    def test_linear_recursion_carries_no_rule_tag(self):
        tags = self._tags(["T(x, y) :- E(x, y).", "T(x, y) :- E(x, z), T(z, y)."])
        self.assertNotIn("nonlinear-recursion", tags)
        self.assertNotIn("mutual-recursion", tags)
        self.assertNotIn("negation", tags)

    def test_nonlinear_recursion_is_detected(self):
        tags = self._tags(["T(x, y) :- E(x, y).", "T(x, y) :- T(x, z), T(z, y)."])
        self.assertIn("nonlinear-recursion", tags)

    def test_mutual_recursion_is_detected(self):
        tags = self._tags(["Odd(x, y) :- E(x, y).",
                           "Odd(x, y) :- Even(x, z), E(z, y).",
                           "Even(x, y) :- Odd(x, z), E(z, y)."])
        self.assertIn("mutual-recursion", tags)

    def test_negated_body_atom_is_detected(self):
        tags = self._tags(["Win(x) :- Move(x, y), !Win(y)."])
        self.assertIn("negation", tags)

    def test_set_difference_in_the_claim_is_negation(self):
        tags = self._tags(["T(x, y) :- E(x, y)."], post="((T ∖ E) ⊆ S)")
        self.assertIn("negation", tags)

    def test_a_fixpoint_witness_is_tagged(self):
        blocks = [{"label": "p", "text": "T(x, y) :- E(x, y).", "provenance": "fixture"}]
        parsed = {"pre": "true", "cmd": "T := ∅", "post": "(T ⊆ R)"}
        tags, _ = BR.compute_tags("Example9001", parsed, {"nonlinear_ra": False, "frontier": False},
                                  {}, blocks, {"R"})
        self.assertIn("fixpoint-witness", tags)


class StatusTest(unittest.TestCase):
    """Status comes from the tree: an emitter-written certificate, a frozen record, or nothing."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp)
        self._orig = BR.CASES_DIR
        BR.CASES_DIR = self.tmp
        self.addCleanup(setattr, BR, "CASES_DIR", self._orig)

    def _case(self, name, certificates: dict[str, str], records: tuple[str, ...] = ()):
        d = self.tmp / name
        (d / "Certificate").mkdir(parents=True, exist_ok=True)
        (d / "Input.lean").write_text(FIXTURE_INPUT, encoding="utf-8")
        (d / "Metadata.json").write_text("{}", encoding="utf-8")
        for fname, text in certificates.items():
            (d / "Certificate" / fname).write_text(text, encoding="utf-8")
        for fname in records:
            (d / fname).write_text(RECORD, encoding="utf-8")
        return name

    def test_emitted_valid_certificate_is_certified_valid(self):
        self.assertEqual(BR.status_of(self._case("Example9001", {"Valid.lean": EMITTED})), "certified valid")

    def test_v2_marker_is_accepted_but_unknown_or_extended_markers_are_not(self):
        v2 = "-- Generated by the Lean-owned fixed-ambient certificate-emitter-v2."
        for marker, expected in ((v2, "certified valid"), (v2 + " extra", BR.SOLVED_VALID),
                                 (v2.replace("v2", "v3"), BR.SOLVED_VALID), ("", BR.SOLVED_VALID)):
            with self.subTest(marker=marker):
                name = self._case("Example9014", {"Valid.lean": marker}, ("Core.json",))
                self.assertEqual(BR.status_of(name), expected)

    def test_emitted_invalid_certificate_is_certified_invalid(self):
        self.assertEqual(BR.status_of(self._case("Example9002", {"Invalid.lean": EMITTED})), "certified invalid")

    def test_hand_written_certificate_is_open(self):
        self.assertEqual(BR.status_of(self._case("Example9003", {"Invalid.lean": HAND_WRITTEN})), "open")
        self.assertEqual(BR.status_of(self._case("Example9004", {"Valid.lean": HAND_WRITTEN})), "open")

    def test_no_certificate_and_no_record_is_open(self):
        self.assertEqual(BR.status_of(self._case("Example9005", {})), "open")

    def test_a_core_record_without_a_certificate_is_solved_valid(self):
        name = self._case("Example9007", {}, ("Core.json",))
        self.assertEqual(BR.status_of(name), BR.SOLVED_VALID)

    def test_a_counterexample_record_without_a_certificate_is_solved_invalid(self):
        name = self._case("Example9008", {}, ("Counterexample.json",))
        self.assertEqual(BR.status_of(name), BR.SOLVED_INVALID)

    def test_a_certificate_outranks_the_record_it_was_built_from(self):
        self.assertEqual(
            BR.status_of(self._case("Example9009", {"Valid.lean": EMITTED}, ("Core.json",))),
            "certified valid")
        self.assertEqual(
            BR.status_of(self._case("Example9010", {"Invalid.lean": EMITTED}, ("Counterexample.json",))),
            "certified invalid")

    def test_a_hand_written_certificate_leaves_a_recorded_case_solved(self):
        """A hand-written file certifies nothing, so the record alone decides the status."""
        self.assertEqual(
            BR.status_of(self._case("Example9011", {"Valid.lean": HAND_WRITTEN}, ("Core.json",))),
            BR.SOLVED_VALID)
        self.assertEqual(
            BR.status_of(self._case("Example9012", {"Invalid.lean": HAND_WRITTEN}, ("Counterexample.json",))),
            BR.SOLVED_INVALID)

    def test_every_status_the_tree_can_show_is_counted_and_explained(self):
        for status in BR.STATUS_ORDER:
            self.assertIn(status, BR.STATUS_EVIDENCE)
        records = [{"status": s} for s in
                   ["certified valid", "certified invalid", BR.SOLVED_VALID, BR.SOLVED_VALID,
                    BR.SOLVED_INVALID, "open"]]
        self.assertEqual(BR.status_counts(records),
                         [("certified valid", 1), ("certified invalid", 1), (BR.SOLVED_VALID, 2),
                          (BR.SOLVED_INVALID, 1), ("open", 1)])

    def test_expectation_reads_either_field_name(self):
        self.assertEqual(BR.expectation_of({"expectedVerdict": "valid"}), "valid")
        self.assertEqual(BR.expectation_of({"currentClassification": "invalid"}), "invalid")
        self.assertEqual(BR.expectation_of({}), "none recorded")

    def test_a_metadata_claim_never_produces_a_certified_or_solved_status(self):
        name = self._case("Example9006", {})
        (self.tmp / name / "Metadata.json").write_text(
            json.dumps({"currentClassification": "valid", "currentEvidence": "certificate"}), encoding="utf-8")
        self.assertEqual(BR.status_of(name), "open")

    def test_a_metadata_claim_never_upgrades_a_solved_case_to_certified(self):
        name = self._case("Example9013", {}, ("Core.json",))
        (self.tmp / name / "Metadata.json").write_text(
            json.dumps({"currentClassification": "valid", "currentEvidence": "certificate"}), encoding="utf-8")
        self.assertEqual(BR.status_of(name), BR.SOLVED_VALID)


def run_build(cases_dir: Path) -> None:
    """Run the copied generator against the copied corpus, with no PDF."""
    p = subprocess.run([sys.executable, str(cases_dir / "report" / "build_report.py"), "--no-pdf"],
                       capture_output=True, text=True)
    if p.returncode != 0:
        raise AssertionError(f"build failed in {cases_dir}:\n{p.stdout}\n{p.stderr}")


def outputs_of(cases_dir: Path) -> dict[str, bytes]:
    return {name: (cases_dir / "report" / name).read_bytes() for name in TRACKED_OUTPUTS}


def copy_corpus(dest: Path) -> Path:
    """Copy Benchmark/ and nothing else; the copy has no repository around it."""
    shutil.copytree(CASES_DIR, dest, symlinks=True)
    return dest


class IsolationTest(unittest.TestCase):
    """The build reads nothing outside Benchmark/."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp)

    def test_build_in_a_bare_copy_matches_the_build_in_the_repository(self):
        copy = copy_corpus(self.tmp / "Benchmark")
        run_build(copy)
        got = outputs_of(copy)
        want = outputs_of(CASES_DIR)
        for name in TRACKED_OUTPUTS:
            self.assertEqual(got[name], want[name],
                             f"{name} differs between a bare copy of Benchmark/ and the repository. "
                             "If the corpus changed, rerun `python3 Benchmark/report/build_report.py`.")

    def test_decoy_neighbours_do_not_change_the_build(self):
        """The same corpus inside a tree that carries the retired folders builds identically."""
        bare = copy_corpus(self.tmp / "bare" / "Benchmark")
        embedded = copy_corpus(self.tmp / "embedded" / "Benchmark")
        root = self.tmp / "embedded"
        for rel, text in [
            ("reports/benchmark_report/inventory.json", '{"entries": [{"id": "Example0106", "datalog": ["-- decoy"]}]}'),
            ("benchmark_new/tools/prodchecks/Prod1061.lean", "def decoy := datalog![ D(x) :- E(x) ]\n"),
            ("Examples/souffle/datalog/tc.naive.dl", ".decl decoy(x: number)\ndecoy(x) :- edge(x, x).\n"),
            ("Legacy/Benchmark2/Tools/decoy.dl", "decoy(x) :- edge(x, x).\n"),
        ]:
            p = root / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text, encoding="utf-8")
        run_build(bare)
        run_build(embedded)
        self.assertEqual(outputs_of(bare), outputs_of(embedded))


class DeterminismTest(unittest.TestCase):
    """Two builds of the same corpus produce the same bytes."""

    def test_two_builds_are_byte_identical(self):
        with tempfile.TemporaryDirectory() as t:
            copy = copy_corpus(Path(t) / "Benchmark")
            run_build(copy)
            first = outputs_of(copy)
            run_build(copy)
            self.assertEqual(outputs_of(copy), first)


class AddACaseTest(unittest.TestCase):
    """A case folder with an input and metadata is all a new case needs."""

    NEW = "Example9999"

    def setUp(self):
        self.tmpdir = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmpdir.cleanup)
        self.copy = copy_corpus(Path(self.tmpdir.name) / "Benchmark")
        run_build(self.copy)
        self.before = outputs_of(self.copy)

    def _add(self):
        d = self.copy / self.NEW
        d.mkdir()
        (d / "Input.lean").write_text(MINIMAL_INPUT, encoding="utf-8")
        (d / "Metadata.json").write_text(
            json.dumps({"canonicalId": self.NEW, "title": "A case added with nothing but its folder"},
                       indent=2) + "\n", encoding="utf-8")
        return d

    def test_a_new_case_appears_with_no_other_edit(self):
        d = self._add()
        run_build(self.copy)
        inv = json.loads((self.copy / "report" / "inventory.json").read_text(encoding="utf-8"))
        entry = {e["id"]: e for e in inv["entries"]}.get(self.NEW)
        self.assertIsNotNone(entry, "the new case is missing from inventory.json")
        self.assertEqual(entry["title"], "A case added with nothing but its folder")
        self.assertEqual(entry["number"], "9999")
        self.assertEqual(entry["status"], "open")
        self.assertEqual(entry["category_key"], BR.UNCATEGORIZED[0])
        self.assertEqual(entry["input_path"], f"Benchmark/{self.NEW}/Input.lean")
        self.assertEqual(entry["schema"], {"E": 2, "T": 2, "S": 2, "Seen": 1})
        self.assertEqual(inv["count"], json.loads(self.before["inventory.json"])["count"] + 1)
        # automatic tags only: nothing was added to curated.json
        self.assertEqual(entry["tags"], [])
        self.assertIn(self.NEW, (self.copy / "report" / "benchmark_report.html").read_text(encoding="utf-8"))
        # and removing the folder again restores the original bytes
        shutil.rmtree(d)
        run_build(self.copy)
        self.assertEqual(outputs_of(self.copy), self.before)


if __name__ == "__main__":
    unittest.main()
