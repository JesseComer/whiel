#!/usr/bin/env python3
"""A certificate kept outside the library build must be visible in the report.

Run them with `python3 -m unittest discover -s Benchmark/report/tests`.

Where a certificate's kernel check runs is measured, not curated: `scripts/place_certificates.py`
elaborates every emitter-written certificate under the watched build's memory limit and records
the outcome per case in `Benchmark/CertificatePlacement.json`. The report reads that ledger and
nothing else on the question — no metadata key decides placement — and a case with no entry, or a
missing ledger, is checked inside the library build like any other.

What is checked here: a case the ledger records with `"fits": false` counts as certified in the
status summary exactly as before, the line under that table says how many such cases there are,
the case's own section widens the status to `certified … (certificate checked outside the library
build)` and prints the ledger's note beside it under its own lead-in, with the peak resident
memory the placement measured, and `inventory.json` carries the flag, the note and that peak. The
property is exercised by building a copy of the corpus with a ledger written into it, so it holds
whatever the committed corpus currently looks like; the committed outputs are then checked against
the committed ledger, which may still be of the older version that recorded no peak.
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
PEAK_KB = 6942000
FITTING_PEAK_KB = 1802240
NOTE = (f"peak resident memory {PEAK_KB} KB while checking Certificate/Invalid.lean exceeds "
        "the library build's 4194304 KB limit")


def load_module():
    spec = importlib.util.spec_from_file_location("build_report_outside_library", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


BR = load_module()


def plain_fragment(note: str) -> str:
    """The longest run of words of `note` that both output formats carry through unchanged.

    Paths are set with \\path{} in the PDF and the special characters of either format are
    escaped, so only a run free of them can be looked for verbatim in both files.
    """
    runs, cur = [], []
    for word in note.split():
        if any(c in word for c in "/\\&%$#_{}~^<>\"'") or not word.isascii():
            runs.append(cur)
            cur = []
        else:
            cur.append(word)
    runs.append(cur)
    best = max(runs, key=len)
    assert len(best) >= 3, f"no plain run of words in the note: {note!r}"
    return " ".join(best)


def certified_cases(cases_dir: Path) -> list[str]:
    """Every case folder the emitter wrote a certificate for, in directory order.

    Read off the given folder, so it answers for a copy as well as for the repository.
    """
    return [d.name for d in sorted(cases_dir.iterdir())
            if BR.is_case_dir(d) and any(BR.emitter_wrote(d / "Certificate" / f"{name}.lean")
                                         for name in ("Valid", "Invalid"))]


def write_ledger(cases_dir: Path, outside: dict[str, str], version: int = BR.PLACEMENT_VERSION,
                 peaks: bool = True) -> None:
    """Write a placement ledger keeping the named cases outside the library build.

    `peaks` writes the measured peak the current ledger version records; a ledger of the older
    version carries none, which is what the report has to tolerate on a checkout whose placement
    has not been run again yet.
    """
    certificates = {}
    for case in sorted(certified_cases(cases_dir)):
        entry = {"treeSha256": "0" * 64, "fits": case not in outside}
        if peaks:
            entry["peakKb"] = PEAK_KB if case in outside else FITTING_PEAK_KB
        if case in outside:
            entry["note"] = outside[case]
        certificates[case] = entry
    (cases_dir / BR.PLACEMENT_FILE).write_text(
        json.dumps({"version": version, "limitKb": 4194304,
                    "certificates": certificates}, indent=2) + "\n", encoding="utf-8")


def run_build(cases_dir: Path) -> None:
    done = subprocess.run([sys.executable, str(cases_dir / "report" / "build_report.py"), "--no-pdf"],
                          capture_output=True, text=True)
    if done.returncode != 0:
        raise AssertionError(f"build failed:\n{done.stdout}\n{done.stderr}")


class LedgerReadingTest(unittest.TestCase):
    """The placement of one case, computed from a ledger alone."""

    LEDGER = {"Example0013": {"treeSha256": "ab", "fits": True, "peakKb": FITTING_PEAK_KB},
              "Example5013": {"treeSha256": "cd", "fits": False, "peakKb": PEAK_KB,
                              "note": NOTE},
              "Example0001": {"treeSha256": "ef", "fits": True}}

    def test_a_case_that_fits_is_inside_with_no_note(self):
        self.assertEqual(BR.placement_of("Example0013", self.LEDGER), (False, ""))

    def test_a_case_that_does_not_fit_is_outside_with_the_ledgers_note(self):
        self.assertEqual(BR.placement_of("Example5013", self.LEDGER), (True, NOTE))

    def test_a_case_with_no_entry_is_inside(self):
        self.assertEqual(BR.placement_of("Example9999", self.LEDGER), (False, ""))
        self.assertEqual(BR.placement_of("Example9999", {}), (False, ""))

    def test_the_measured_peak_is_read_off_the_ledger(self):
        self.assertEqual(BR.placement_peak_kb("Example5013", self.LEDGER), PEAK_KB)
        self.assertEqual(BR.placement_peak_kb("Example0013", self.LEDGER), FITTING_PEAK_KB)

    def test_a_ledger_of_the_older_version_records_no_peak(self):
        """An entry written before the peak was measured carries none, and that is not an error."""
        self.assertIsNone(BR.placement_peak_kb("Example0001", self.LEDGER))
        self.assertIsNone(BR.placement_peak_kb("Example9999", self.LEDGER))
        self.assertIsNone(BR.placement_peak_kb("Example9999", {}))
        for bad in (True, -1, "6942000", None):
            self.assertIsNone(BR.placement_peak_kb("X", {"X": {"fits": True, "peakKb": bad}}), bad)

    def test_the_peak_is_printed_in_whole_megabytes_or_not_at_all(self):
        self.assertEqual(BR.placement_peak_text(PEAK_KB), " (peak 6779 MB)")
        self.assertEqual(BR.placement_peak_text(None), "")
        self.assertEqual(BR.placement_peak_text(0), "")

    def test_no_metadata_key_can_place_a_certificate(self):
        """Placement is machine state; a metadata claim must not reach the report."""
        self.assertFalse(hasattr(BR, "certificate_outside_library"))
        source = SCRIPT.read_text(encoding="utf-8")
        self.assertNotIn("certificateOutsideLibrary", source)
        self.assertNotIn("certificateNote", source)


class StatusTextTest(unittest.TestCase):
    """The per-case status text, computed from a record alone."""

    def test_a_plain_case_keeps_its_status(self):
        self.assertEqual(BR.case_status_text({"status": "certified invalid"}), "certified invalid")
        self.assertEqual(
            BR.case_status_text({"status": "certified valid", "certificate_outside_library": False}),
            "certified valid")

    def test_a_certificate_outside_the_library_is_named_in_the_status(self):
        rec = {"status": "certified invalid", "certificate_outside_library": True}
        self.assertEqual(BR.case_status_text(rec),
                         "certified invalid (certificate checked outside the library build)")

    def test_the_line_under_the_status_table_counts_the_cases_kept_outside(self):
        records = [{"certificate_outside_library": True}, {"certificate_outside_library": False}, {}]
        self.assertEqual(BR.outside_library_count(records), 1)
        self.assertTrue(BR.outside_library_line(records).startswith(
            f"{BR.OUTSIDE_LIBRARY_LINE}: 1"))
        self.assertTrue(BR.outside_library_line([]).startswith(f"{BR.OUTSIDE_LIBRARY_LINE}: 0"))


class LedgerBuildTest(unittest.TestCase):
    """A report built over a copy of the corpus with a ledger written into it."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp())
        cls.copy = cls.tmp / "Benchmark"
        shutil.copytree(CASES_DIR, cls.copy, symlinks=True)
        (cls.copy / BR.PLACEMENT_FILE).unlink(missing_ok=True)
        cls.certified = certified_cases(cls.copy)
        assert cls.certified, "the corpus holds no emitter-written certificate"
        cls.outside = cls.certified[0]
        write_ledger(cls.copy, {cls.outside: NOTE})
        run_build(cls.copy)
        cls.inventory = json.loads((cls.copy / "report" / "inventory.json").read_text(encoding="utf-8"))
        cls.entries = {e["id"]: e for e in cls.inventory["entries"]}
        cls.tex = (cls.copy / "report" / "benchmark_report.tex").read_text(encoding="utf-8")
        cls.html = (cls.copy / "report" / "benchmark_report.html").read_text(encoding="utf-8")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp)

    def test_the_inventory_carries_the_flag_the_note_and_the_measured_peak(self):
        entry = self.entries[self.outside]
        self.assertTrue(entry["certificate_outside_library"])
        self.assertEqual(entry["certificate_note"], NOTE)
        self.assertEqual(entry["certificate_peak_kb"], PEAK_KB)
        self.assertTrue(entry["status"].startswith("certified"),
                        "a certificate outside the library build is still a certificate")

    def test_every_other_case_carries_the_flag_unset_and_no_note(self):
        for case, entry in self.entries.items():
            if case == self.outside:
                continue
            self.assertFalse(entry["certificate_outside_library"], case)
            self.assertEqual(entry["certificate_note"], "", case)
            self.assertIn(entry["certificate_peak_kb"], (None, FITTING_PEAK_KB), case)

    def test_the_status_summary_counts_it_as_certified(self):
        """The front table counts the plain status, so the totals are unchanged by the ledger."""
        records = [{"status": e["status"]} for e in self.inventory["entries"]]
        counts = dict(BR.status_counts(records))
        certified = sum(1 for e in self.inventory["entries"] if e["status"].startswith("certified"))
        self.assertEqual(counts["certified valid"] + counts["certified invalid"], certified)
        self.assertEqual(certified, len(self.certified))
        self.assertIn(self.entries[self.outside]["status"], ("certified valid", "certified invalid"))

    def test_the_status_table_gains_one_line_with_the_count(self):
        line = f"{BR.OUTSIDE_LIBRARY_LINE}: 1"
        self.assertIn(line, self.tex)
        self.assertIn(line, self.html)

    def test_the_pdf_source_and_the_html_print_the_widened_status_and_the_note(self):
        fragment = plain_fragment(NOTE)
        for text, where in ((self.tex, "the PDF source"), (self.html, "the HTML")):
            self.assertIn(BR.OUTSIDE_LIBRARY_SUFFIX, text, where)
            self.assertIn(fragment, text, f"the note is missing from {where}")

    def test_the_note_is_printed_under_its_own_lead_in_with_the_measured_peak(self):
        """Unlabelled, the note reads as a verdict on the certificate rather than on its size."""
        lead = f"{BR.PLACEMENT_NOTE_LEAD}: {NOTE.split()[0]}"
        for text, where in ((self.tex, "the PDF source"), (self.html, "the HTML")):
            self.assertIn(lead, text, f"the note has no lead-in in {where}")
            self.assertIn(BR.placement_peak_text(PEAK_KB).strip(), text,
                          f"the measured peak is missing from {where}")

    def test_a_ledger_without_a_measured_peak_still_builds_and_prints_the_note(self):
        """A checkout whose placement has not been run again carries a version-1 ledger."""
        write_ledger(self.copy, {self.outside: NOTE}, version=1, peaks=False)
        try:
            run_build(self.copy)
            inventory = json.loads(
                (self.copy / "report" / "inventory.json").read_text(encoding="utf-8"))
            entry = {e["id"]: e for e in inventory["entries"]}[self.outside]
            self.assertTrue(entry["certificate_outside_library"])
            self.assertIsNone(entry["certificate_peak_kb"])
            tex = (self.copy / "report" / "benchmark_report.tex").read_text(encoding="utf-8")
            self.assertIn(f"{BR.PLACEMENT_NOTE_LEAD}: ", tex)
            self.assertNotIn("(peak ", tex)
        finally:
            # restore what the other tests of this class were built with
            write_ledger(self.copy, {self.outside: NOTE})
            run_build(self.copy)

    def test_a_case_that_now_fits_returns_inside_with_no_other_edit(self):
        """Re-measured lighter, the same corpus reports the case inside the library build."""
        write_ledger(self.copy, {})
        run_build(self.copy)
        inventory = json.loads((self.copy / "report" / "inventory.json").read_text(encoding="utf-8"))
        entry = {e["id"]: e for e in inventory["entries"]}[self.outside]
        self.assertFalse(entry["certificate_outside_library"])
        self.assertEqual(entry["certificate_note"], "")
        tex = (self.copy / "report" / "benchmark_report.tex").read_text(encoding="utf-8")
        self.assertNotIn(BR.OUTSIDE_LIBRARY_SUFFIX, tex)
        self.assertIn(f"{BR.OUTSIDE_LIBRARY_LINE}: 0", tex)
        # and with no ledger at all, every certificate is inside
        (self.copy / BR.PLACEMENT_FILE).unlink()
        run_build(self.copy)
        inventory = json.loads((self.copy / "report" / "inventory.json").read_text(encoding="utf-8"))
        self.assertEqual([e["id"] for e in inventory["entries"] if e["certificate_outside_library"]], [])
        # restore what the other tests of this class were built with
        write_ledger(self.copy, {self.outside: NOTE})
        run_build(self.copy)


class CommittedOutputsTest(unittest.TestCase):
    """The committed report agrees with the committed ledger, whatever it currently says."""

    @classmethod
    def setUpClass(cls):
        cls.placement = BR.load_placement()
        cls.entries = {e["id"]: e for e in json.loads(
            (REPORT_DIR / "inventory.json").read_text(encoding="utf-8"))["entries"]}

    def test_the_inventory_matches_the_ledger_case_by_case(self):
        for case, entry in self.entries.items():
            outside, note = BR.placement_of(case, self.placement)
            self.assertEqual(entry["certificate_outside_library"], outside, case)
            self.assertEqual(entry["certificate_note"], note, case)
            self.assertEqual(entry["certificate_peak_kb"],
                             BR.placement_peak_kb(case, self.placement), case)

    def test_the_ledger_only_places_certificates(self):
        for case, entry in self.placement.items():
            if entry["fits"]:
                continue
            self.assertTrue(str(entry.get("note") or "").strip(),
                            f"{case}: kept outside the library build with no note")
            self.assertIn(case, self.entries, f"{case}: placed by the ledger but not a case")
            self.assertTrue(self.entries[case]["status"].startswith("certified"),
                            f"{case}: placed by the ledger but not certified")

    def test_the_status_line_of_the_committed_report_counts_the_ledger(self):
        n = sum(1 for e in self.entries.values() if e["certificate_outside_library"])
        line = f"{BR.OUTSIDE_LIBRARY_LINE}: {n}"
        for name in ("benchmark_report.tex", "benchmark_report.html"):
            self.assertIn(line, (REPORT_DIR / name).read_text(encoding="utf-8"),
                          f"{name} is stale; rerun python3 Benchmark/report/build_report.py")


if __name__ == "__main__":
    unittest.main()
