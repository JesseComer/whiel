"""Automatic certificate placement, measured with a fake builder.

Run them with `python3 -m unittest tests/test_place_certificates.py`.

Every test builds a small tree of case folders in a temporary directory and hands
`place_certificates.main` a builder that answers each command from a table, so no Lean, lake
or watchdog process is ever started here. What is checked is the whole decision: which cases
are measured, what the two watched scripts are asked to do, how a peak resident memory over
the library build's limit is told apart from a certificate that does not check at all, and the
exact bytes of the ledger that results.

The placement decision rests on a measured peak and on nothing else. A failure of any kind —
whatever status it carries, whatever it printed — is an error, so the tests below spend most of
their effort on the ways a failure used to be mistaken for a certificate that is merely too
heavy for the library build.
"""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "certificate_placement", REPO / "scripts/place_certificates.py")
placement = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = placement
SPEC.loader.exec_module(placement)

MARK = placement.EMITTER_MARK
LIMIT = placement.DEFAULT_LIMIT_KB
KILL_TEXT = "WATCHDOG KILL pid=51 rss=5000000KB (limit 4194304 KB)\n"


def certificate_text(case: str, marked: bool = True) -> str:
    """A stand-in certificate root: the emitter's marker, imports, and a placeholder theorem."""
    first = MARK if marked else "-- Written by hand while the witness was being extracted."
    return (f"{first}\n-- Do not edit by hand.\n"
            f"import Benchmark.{case}.Input\n"
            "import Whiel.Synthesis.Certificate.Support\n\n"
            "theorem placeholder : True := trivial\n")


class FakeBuilder:
    """Answers each command from a table keyed by a substring of one of its arguments."""

    def __init__(self, default: tuple[int, str, int] = (0, "build exit 0\n", 1024)):
        self.calls: list[tuple[list[str], dict]] = []
        self.answers: dict[str, tuple[int, str, int]] = {}
        self.default = default

    def answer(self, key: str, status: int, output: str = "", peak_kb: int = 1024) -> None:
        self.answers[key] = (status, output, peak_kb)

    def __call__(self, command, env):
        self.calls.append((list(command), dict(env)))
        for key, reply in self.answers.items():
            if any(key in part for part in command):
                return placement.Run(*reply)
        return placement.Run(*self.default)

    def commands_mentioning(self, key: str) -> list[list[str]]:
        return [command for command, _ in self.calls if any(key in part for part in command)]


class PlacementTest(unittest.TestCase):
    """One temporary corpus per test; the ledger is the only thing the run writes."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "Benchmark").mkdir()
        self.builder = FakeBuilder()

    # -- fixture helpers ---------------------------------------------------------------

    def add_case(self, case: str, certificate: str | None = "Invalid",
                 marked: bool = True, extra: dict[str, str] | None = None) -> Path:
        directory = self.root / "Benchmark" / case
        (directory).mkdir()
        (directory / "Input.lean").write_text(f"-- {case}\n", encoding="utf-8")
        (directory / "Metadata.json").write_text(
            json.dumps({"canonicalId": case}, indent=2) + "\n", encoding="utf-8")
        if certificate is not None:
            cert = directory / "Certificate"
            cert.mkdir()
            (cert / f"{certificate}.lean").write_text(certificate_text(case, marked),
                                                      encoding="utf-8")
            for name, text in (extra or {}).items():
                (cert / name).write_text(text, encoding="utf-8")
        return directory

    def run_main(self, *argv: str, builder: FakeBuilder | None = None) -> int:
        """Run the script, keeping what it printed in self.out and self.err."""
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = placement.main(list(argv), builder=builder or self.builder, root=self.root)
        self.out, self.err = out.getvalue(), err.getvalue()
        return status

    def ledger(self) -> dict:
        return json.loads((self.root / "Benchmark" / "CertificatePlacement.json")
                          .read_text(encoding="utf-8"))

    def peak_of(self, case: str, peak_kb: int) -> None:
        """Make the fake measurement report that peak for the case's certificate root."""
        self.builder.answer(f"Benchmark/{case}/Certificate/", 0, "", peak_kb)

    def too_heavy(self, case: str) -> None:
        """Make the case's certificate check succeed, one kilobyte over the library's limit."""
        self.peak_of(case, LIMIT + 1)

    def write_ledger(self, text: str) -> None:
        (self.root / "Benchmark" / "CertificatePlacement.json").write_text(text, encoding="utf-8")

    def test_v2_certificate_resources_are_placed_and_bound_to_ledger(self):
        case = self.add_case("Example5018", "Valid")
        cert = case / "Certificate"
        root = cert / "Valid.lean"
        root.write_text(root.read_text().replace(MARK,
            "-- Generated by the Lean-owned fixed-ambient certificate-emitter-v2."))
        resource = cert / "Resources" / "proof.lrat"
        resource.parent.mkdir()
        resource.write_text("original proof resource\n")
        self.assertEqual(self.run_main(), 0)
        self.assertIn("Example5018", self.ledger()["certificates"])
        resource.write_text("changed proof resource\n")
        self.assertNotEqual(self.run_main("--check"), 0)

    def test_unknown_or_extended_emitter_markers_are_not_certificates(self):
        case = self.add_case("Example5018", "Valid")
        root = case / "Certificate" / "Valid.lean"
        for marker in ("", MARK + " extra",
                       "-- Generated by the Lean-owned fixed-ambient certificate-emitter-v3."):
            with self.subTest(marker=marker):
                root.write_text(marker)
                self.assertEqual(placement.certificate_roots(case), [])

    # -- first placement ---------------------------------------------------------------

    def test_a_light_certificate_is_inside_and_a_heavy_one_is_outside(self):
        self.add_case("Example0013")
        self.add_case("Example5013")
        self.too_heavy("Example5013")
        self.assertEqual(self.run_main(), 0)
        ledger = self.ledger()
        self.assertEqual(ledger["version"], 2)
        self.assertEqual(ledger["limitKb"], LIMIT)
        light = ledger["certificates"]["Example0013"]
        self.assertTrue(light["fits"])
        self.assertNotIn("note", light)
        self.assertEqual(light["peakKb"], 1024)
        heavy = ledger["certificates"]["Example5013"]
        self.assertFalse(heavy["fits"])
        self.assertEqual(heavy["peakKb"], LIMIT + 1)
        self.assertIn(str(LIMIT), heavy["note"])
        self.assertIn(str(LIMIT + 1), heavy["note"])
        self.assertIn("peak resident memory", heavy["note"])
        self.assertIn("Certificate/Invalid.lean", heavy["note"])
        self.assertEqual(heavy["treeSha256"],
                         placement.tree_digest(self.root / "Benchmark" / "Example5013"))
        # The summary says where every case landed and what has to be regenerated next.
        self.assertIn("inside the library build: 1", self.out)
        self.assertIn("outside the library build: 1: Example5013", self.out)
        self.assertIn("generate_fixed_ambient_registry.py", self.out)
        self.assertIn("build_report.py", self.out)

    def test_the_imports_are_built_first_and_then_the_root_is_elaborated(self):
        self.add_case("Example0013")
        self.run_main("--jobs", "1")
        build, elaborate = [command for command, _ in self.builder.calls]
        self.assertEqual(build, [placement.BUILD_SCRIPT, "Benchmark.Example0013.Input",
                                 "Whiel.Synthesis.Certificate.Support"])
        self.assertEqual(elaborate, [placement.WATCHDOG_SCRIPT,
                                     str(placement.DEFAULT_HARD_LIMIT_KB),
                                     "lake", "env", "lean",
                                     "Benchmark/Example0013/Certificate/Invalid.lean"])
        environments = [env for _, env in self.builder.calls]
        self.assertEqual(environments[0]["LIMIT_KB"], str(LIMIT))
        for env in environments:
            self.assertEqual(env["LEAN_NUM_THREADS"], "1")

    def test_jobs_bounds_the_import_build_but_not_the_root_elaboration(self):
        """`--jobs` only widens how many of a root's own leaf imports build at once."""
        self.add_case("Example0013")
        self.run_main("--jobs", "3")
        build, elaborate = [env for _, env in self.builder.calls]
        self.assertEqual(build["LEAN_NUM_THREADS"], "3")
        self.assertEqual(elaborate["LEAN_NUM_THREADS"], "1")

    def test_jobs_one_reproduces_the_hardcoded_single_thread_behaviour(self):
        self.add_case("Example0013")
        self.run_main("--jobs", "1")
        for _, env in self.builder.calls:
            self.assertEqual(env["LEAN_NUM_THREADS"], "1")

    def test_the_hard_limit_retry_for_a_heavy_import_stays_single_threaded(self):
        """The safety-net retry is rare; `jobs` copies of a 12 GiB cap would not be safe."""
        self.add_case("Example5013")

        class LimitSensitive(FakeBuilder):
            def __call__(inner, command, env):
                inner.calls.append((list(command), dict(env)))
                if command[0] == placement.BUILD_SCRIPT:
                    heavy = env["LIMIT_KB"] == str(LIMIT)
                    return placement.Run(1 if heavy else 0, KILL_TEXT if heavy else "", 0)
                return placement.Run(0, "", 2048)

        self.builder = LimitSensitive()
        self.assertEqual(self.run_main("--jobs", "4"), 0)
        builds = [env for command, env in self.builder.calls if command[0] == placement.BUILD_SCRIPT]
        self.assertEqual(builds[0]["LEAN_NUM_THREADS"], "4")
        self.assertEqual(builds[1]["LEAN_NUM_THREADS"], "1")

    def test_a_non_positive_jobs_is_refused(self):
        self.add_case("Example0013")
        self.assertEqual(self.run_main("--jobs", "0"), 2)
        self.assertIn("--jobs must be positive", self.err)

    def test_a_progress_line_is_printed_and_flushed_per_case(self):
        self.add_case("Example0013")
        self.assertEqual(self.run_main("--jobs", "1"), 0)
        self.assertIn("measuring Example0013", self.out)
        self.assertIn("Example0013: inside the library build", self.out)

    def test_default_jobs_arithmetic(self):
        gib = placement.KB_PER_GIB
        self.assertEqual(placement.default_jobs(10, 24 * gib), 4, "capped at DEFAULT_JOBS_CAP")
        self.assertEqual(placement.default_jobs(2, 100 * gib), 1, "capped by cores // 2")
        self.assertEqual(placement.default_jobs(20, 2 * gib), 1, "capped by memory, floored at 1")
        self.assertEqual(placement.default_jobs(8, 16 * gib), 4, "cores and memory agree at 4")
        self.assertEqual(placement.default_jobs(1, 1), 1)

    def test_resolved_default_jobs_falls_back_to_one_without_a_memory_reading(self):
        original = placement.detected_memory_kb
        placement.detected_memory_kb = lambda: None
        try:
            self.assertEqual(placement.resolved_default_jobs(), 1)
        finally:
            placement.detected_memory_kb = original

    def test_an_unspecified_jobs_uses_the_resolved_default(self):
        original = placement.resolved_default_jobs
        placement.resolved_default_jobs = lambda: 2
        try:
            self.add_case("Example0013")
            self.assertEqual(self.run_main(), 0)
            build, _ = [env for _, env in self.builder.calls]
            self.assertEqual(build["LEAN_NUM_THREADS"], "2")
        finally:
            placement.resolved_default_jobs = original

    def test_the_root_is_checked_under_the_safety_cap_not_under_the_library_limit(self):
        """The cap only stops a runaway check; the placement is decided by the measured peak."""
        self.add_case("Example0013")
        self.run_main("--hard-limit-kb", "16777216")
        elaborate = self.builder.commands_mentioning("Certificate/Invalid.lean")[0]
        self.assertEqual(elaborate[1], "16777216")
        self.assertNotIn(str(LIMIT), elaborate)

    def test_every_certificate_root_of_a_case_is_measured_in_order(self):
        directory = self.add_case("Example0001", certificate="Valid")
        (directory / "Certificate" / "ProposalBinding.lean").write_text(
            certificate_text("Example0001"), encoding="utf-8")
        self.run_main()
        checked = [command[-1] for command, _ in self.builder.calls
                   if command[0] == placement.WATCHDOG_SCRIPT]
        self.assertEqual(checked, ["Benchmark/Example0001/Certificate/Valid.lean",
                                   "Benchmark/Example0001/Certificate/ProposalBinding.lean"])

    def test_the_recorded_peak_is_the_heaviest_root_of_the_case(self):
        directory = self.add_case("Example0001", certificate="Valid")
        (directory / "Certificate" / "ProposalBinding.lean").write_text(
            certificate_text("Example0001"), encoding="utf-8")
        self.builder.answer("Certificate/Valid.lean", 0, "", 2000)
        self.builder.answer("Certificate/ProposalBinding.lean", 0, "", 9000)
        self.run_main()
        entry = self.ledger()["certificates"]["Example0001"]
        self.assertEqual(entry["peakKb"], 9000)
        self.assertTrue(entry["fits"])

    def test_the_note_names_the_root_that_reached_the_peak(self):
        directory = self.add_case("Example0001", certificate="Valid")
        (directory / "Certificate" / "ProposalBinding.lean").write_text(
            certificate_text("Example0001"), encoding="utf-8")
        self.builder.answer("Certificate/Valid.lean", 0, "", 2000)
        self.builder.answer("Certificate/ProposalBinding.lean", 0, "", LIMIT + 5)
        self.run_main()
        entry = self.ledger()["certificates"]["Example0001"]
        self.assertFalse(entry["fits"])
        self.assertIn("Certificate/ProposalBinding.lean", entry["note"])
        self.assertEqual(entry["peakKb"], LIMIT + 5)

    # -- the measured peak against the limit -------------------------------------------

    def test_a_peak_just_under_the_limit_fits(self):
        self.add_case("Example0013")
        self.peak_of("Example0013", LIMIT - 1)
        self.assertEqual(self.run_main(), 0)
        entry = self.ledger()["certificates"]["Example0013"]
        self.assertTrue(entry["fits"])
        self.assertEqual(entry["peakKb"], LIMIT - 1)

    def test_a_peak_exactly_at_the_limit_fits(self):
        """The limit is what the library build tolerates, so reaching it is not exceeding it."""
        self.add_case("Example0013")
        self.peak_of("Example0013", LIMIT)
        self.assertEqual(self.run_main(), 0)
        entry = self.ledger()["certificates"]["Example0013"]
        self.assertTrue(entry["fits"])
        self.assertEqual(entry["peakKb"], LIMIT)

    def test_a_peak_just_over_the_limit_does_not_fit(self):
        self.add_case("Example0013")
        self.peak_of("Example0013", LIMIT + 1)
        self.assertEqual(self.run_main(), 0)
        self.assertFalse(self.ledger()["certificates"]["Example0013"]["fits"])

    # -- failures are never placements --------------------------------------------------

    def test_no_kill_heuristic_survives(self):
        """Nothing reads a status or a line of output to guess that a limit was reached."""
        self.assertFalse(hasattr(placement, "was_killed"))
        self.assertFalse(hasattr(placement, "KILL_LINE"))
        self.assertFalse(hasattr(placement, "KILL_STATUS"))
        source = (REPO / "scripts/place_certificates.py").read_text(encoding="utf-8")
        for signature in ("WATCHDOG KILL", "WATCHDOG:", "killing"):
            self.assertNotIn(signature, source)

    def test_a_failing_import_build_that_mentions_a_kill_is_an_error(self):
        """A machine-wide watchdog can kill a foreign process while the imports are building."""
        self.add_case("Example0013")
        self.builder.answer("Benchmark.Example0013.Input", 1, KILL_TEXT)
        self.assertEqual(self.run_main(), 1)
        self.assertEqual(self.ledger()["certificates"], {})
        self.assertIn("Benchmark.Example0013.Input", self.err)
        self.assertIn("status 1", self.err)

    def test_a_killed_import_build_is_an_error_not_a_placement(self):
        self.add_case("Example5013")
        self.builder.answer("Benchmark.Example5013.Input", 137, KILL_TEXT)
        self.assertEqual(self.run_main(), 1)
        self.assertEqual(self.ledger()["certificates"], {})
        self.assertIn("building the modules imported by", self.err)
        self.assertIn("status 137", self.err)

    def test_a_heavy_imported_proof_module_places_the_case_outside(self):
        """The imports fail at the library limit and build cleanly under the hard cap."""
        self.add_case("Example5013")

        class LimitSensitive(FakeBuilder):
            def __call__(inner, command, env):
                inner.calls.append((list(command), dict(env)))
                if command[0] == placement.BUILD_SCRIPT:
                    heavy = env["LIMIT_KB"] == str(LIMIT)
                    return placement.Run(1 if heavy else 0, KILL_TEXT if heavy else "", 0)
                return placement.Run(0, "", 2048)

        self.builder = LimitSensitive()
        self.assertEqual(self.run_main(), 0)
        entry = self.ledger()["certificates"]["Example5013"]
        self.assertIs(entry["fits"], False)
        self.assertIn("imported by Certificate/Invalid.lean", entry["note"])
        self.assertIn(str(placement.DEFAULT_HARD_LIMIT_KB), entry["note"])

    def test_a_silent_kill_of_the_root_check_is_an_error_naming_the_safety_cap(self):
        self.add_case("Example5013")
        self.builder.answer("Benchmark/Example5013/Certificate/", 137, "")
        self.assertEqual(self.run_main(), 1)
        self.assertEqual(self.ledger()["certificates"], {})
        self.assertIn(f"exceeded the hard safety cap of {placement.DEFAULT_HARD_LIMIT_KB} KB",
                      self.err)
        self.assertIn("--hard-limit-kb", self.err)

    def test_a_failing_root_check_that_mentions_a_kill_is_an_error(self):
        """An error message may well contain the watchdog's own words; it is still an error."""
        self.add_case("Example5013")
        self.builder.answer("Benchmark/Example5013/Certificate/", 1,
                            KILL_TEXT + "error: unknown identifier 'foo'\n")
        self.assertEqual(self.run_main(), 1)
        self.assertEqual(self.ledger()["certificates"], {})
        self.assertIn("unknown identifier", self.err)

    def test_a_broken_certificate_is_an_error_and_writes_no_entry(self):
        self.add_case("Example0013")
        self.add_case("Example3001")
        self.builder.answer("Benchmark/Example3001/Certificate/", 1,
                            "error: unknown identifier 'foo'\n")
        self.assertEqual(self.run_main(), 1)
        certificates = self.ledger()["certificates"]
        self.assertIn("Example0013", certificates)
        self.assertNotIn("Example3001", certificates,
                         "a certificate that does not check was recorded as merely too heavy")
        self.assertIn("Example3001", self.err)
        self.assertIn("unknown identifier", self.err)

    def test_a_broken_certificate_loses_the_entry_it_had(self):
        self.add_case("Example3001")
        self.run_main()
        self.assertTrue(self.ledger()["certificates"]["Example3001"]["fits"])
        certificate = self.root / "Benchmark" / "Example3001" / "Certificate" / "Invalid.lean"
        certificate.write_text(certificate_text("Example3001") + "-- re-emitted\n",
                               encoding="utf-8")
        broken = FakeBuilder()
        broken.answer("Benchmark/Example3001/Certificate/", 1, "error: type mismatch\n")
        self.assertEqual(self.run_main(builder=broken), 1)
        self.assertEqual(self.ledger()["certificates"], {})

    def test_a_failing_import_build_is_an_error_not_a_placement(self):
        self.add_case("Example0013")
        self.builder.answer("Benchmark.Example0013.Input", 1, "error: unknown module\n")
        self.assertEqual(self.run_main(), 1)
        self.assertEqual(self.ledger()["certificates"], {})

    # -- re-measurement ----------------------------------------------------------------

    def test_an_unchanged_certificate_is_not_measured_again(self):
        self.add_case("Example0013")
        self.run_main()
        before = self.builder.calls.copy()
        second = FakeBuilder()
        self.assertEqual(self.run_main(builder=second), 0)
        self.assertEqual(second.calls, [], "an unchanged digest was measured again")
        self.assertTrue(before, "the first run measured nothing")

    def test_force_measures_an_unchanged_certificate_again(self):
        self.add_case("Example0013")
        self.run_main()
        second = FakeBuilder()
        self.assertEqual(self.run_main("--force", builder=second), 0)
        self.assertTrue(second.calls, "--force measured nothing")

    def test_a_re_emitted_heavy_certificate_that_now_fits_returns_inside(self):
        self.add_case("Example5013")
        self.too_heavy("Example5013")
        self.run_main()
        self.assertFalse(self.ledger()["certificates"]["Example5013"]["fits"])
        # The replay is re-emitted: a lighter witness, same case, no hand edit anywhere.
        certificate = self.root / "Benchmark" / "Example5013" / "Certificate" / "Invalid.lean"
        certificate.write_text(certificate_text("Example5013")
                               + "-- a lighter witness\n", encoding="utf-8")
        light = FakeBuilder()
        self.assertEqual(self.run_main(builder=light), 0)
        entry = self.ledger()["certificates"]["Example5013"]
        self.assertTrue(entry["fits"], "a certificate that now fits is still recorded as too heavy")
        self.assertNotIn("note", entry)
        self.assertEqual(entry["treeSha256"],
                         placement.tree_digest(self.root / "Benchmark" / "Example5013"))

    def test_a_new_file_beside_the_certificate_changes_the_digest(self):
        self.add_case("Example5013")
        self.run_main()
        first = self.ledger()["certificates"]["Example5013"]["treeSha256"]
        (self.root / "Benchmark" / "Example5013" / "Certificate" / "InitClause0.lean").write_text(
            "theorem clause : True := trivial\n", encoding="utf-8")
        second = FakeBuilder()
        self.run_main(builder=second)
        self.assertTrue(second.calls, "a re-emitted certificate tree was not measured again")
        self.assertNotEqual(self.ledger()["certificates"]["Example5013"]["treeSha256"], first)

    # -- the digest ignores what the emitter did not write --------------------------------

    def test_a_hidden_file_beside_the_certificate_leaves_the_digest_alone(self):
        """A folder view's state file or a tool's lock file is not part of the certificate."""
        self.add_case("Example5013")
        case = self.root / "Benchmark" / "Example5013"
        before = placement.tree_digest(case)
        (case / "Certificate" / ".DS_Store").write_bytes(b"\x00\x01machine litter")
        (case / "Certificate" / ".whiel-output-4711.lock").write_text("4711\n", encoding="utf-8")
        hidden = case / "Certificate" / ".cache"
        hidden.mkdir()
        (hidden / "leancheck.log").write_text("noise\n", encoding="utf-8")
        self.assertEqual(placement.tree_digest(case), before)

    def test_a_hidden_file_does_not_make_a_measured_certificate_stale(self):
        self.add_case("Example5013")
        self.run_main()
        (self.root / "Benchmark" / "Example5013" / "Certificate" / ".DS_Store").write_bytes(b"x")
        second = FakeBuilder()
        self.assertEqual(self.run_main(builder=second), 0)
        self.assertEqual(second.calls, [], "a dotfile forced a re-measurement")
        self.assertEqual(self.run_main("--check", builder=FakeBuilder()), 0)

    def test_a_visible_file_still_changes_the_digest(self):
        self.add_case("Example5013")
        case = self.root / "Benchmark" / "Example5013"
        before = placement.tree_digest(case)
        (case / "Certificate" / "InitClause0.lean").write_text("-- x\n", encoding="utf-8")
        self.assertNotEqual(placement.tree_digest(case), before)

    # -- the units of the operating system's peak ------------------------------------------

    def test_the_peak_is_normalised_from_bytes_on_macos_and_kilobytes_on_linux(self):
        """`ru_maxrss` counts bytes on macOS and kilobytes on Linux; the ledger holds KB."""
        self.assertEqual(placement.maxrss_kb(6_942_000 * 1024, "darwin"), 6_942_000)
        self.assertEqual(placement.maxrss_kb(6_942_000, "linux"), 6_942_000)
        self.assertEqual(placement.maxrss_kb(0, "darwin"), 0)
        self.assertEqual(placement.maxrss_kb(2047, "darwin"), 1)

    def test_the_helper_process_reports_a_status_and_a_peak_for_a_real_child(self):
        """The `--measure-one` helper is what makes the peak the child's own and nothing else's."""
        out = io.StringIO()
        request = json.dumps({"command": [sys.executable, "-c",
                                          "import sys; sys.stderr.write('done\\n')"],
                              "env": {}})
        with contextlib.redirect_stdout(out):
            self.assertEqual(placement.main([placement.MEASURE_FLAG, request]), 0)
        reported = json.loads(out.getvalue().strip().splitlines()[-1])
        self.assertEqual(reported["status"], 0)
        self.assertIn("done", reported["output"])
        self.assertGreater(reported["peakKb"], 0)

    # -- what is a certificate ----------------------------------------------------------

    def test_a_hand_written_certificate_is_not_placed(self):
        self.add_case("Example0106", marked=False)
        self.add_case("Example0107", certificate=None)
        self.assertEqual(self.run_main(), 0)
        self.assertEqual(self.ledger()["certificates"], {})
        self.assertEqual(self.builder.calls, [])

    def test_a_stale_entry_for_a_removed_case_is_dropped(self):
        self.add_case("Example0013")
        self.add_case("Example3001")
        self.run_main()
        self.assertIn("Example3001", self.ledger()["certificates"])
        (self.root / "Benchmark" / "Example3001" / "Certificate" / "Invalid.lean").unlink()
        second = FakeBuilder()
        self.assertEqual(self.run_main(builder=second), 0)
        self.assertEqual(sorted(self.ledger()["certificates"]), ["Example0013"])
        self.assertEqual(second.calls, [])

    # -- --ids ---------------------------------------------------------------------------

    def test_ids_measures_only_the_named_cases(self):
        self.add_case("Example0013")
        self.add_case("Example5013")
        self.assertEqual(self.run_main("--ids", "Example5013"), 0)
        self.assertEqual(sorted(self.ledger()["certificates"]), ["Example5013"])
        self.assertEqual(self.builder.commands_mentioning("Example0013"), [])

    def test_ids_leaves_the_entries_of_other_cases_alone(self):
        self.add_case("Example0013")
        self.add_case("Example5013")
        self.run_main()
        (self.root / "Benchmark" / "Example0013" / "Certificate" / "Invalid.lean").unlink()
        second = FakeBuilder()
        self.assertEqual(self.run_main("--ids", "Example5013", builder=second), 0)
        self.assertIn("Example0013", self.ledger()["certificates"],
                      "a selective run pruned a case it was not asked about")

    def test_an_unknown_id_is_an_error(self):
        self.add_case("Example0013")
        self.assertEqual(self.run_main("--ids", "Example9999"), 1)

    # -- --check and ledger_problems -------------------------------------------------------

    def test_check_passes_on_a_current_ledger_without_building_or_writing(self):
        self.add_case("Example0013")
        self.run_main()
        before = (self.root / "Benchmark" / "CertificatePlacement.json").read_bytes()
        checker = FakeBuilder()
        self.assertEqual(self.run_main("--check", builder=checker), 0)
        self.assertEqual(checker.calls, [])
        self.assertEqual((self.root / "Benchmark" / "CertificatePlacement.json").read_bytes(),
                         before)
        self.assertEqual(placement.ledger_problems(self.root), [])

    def test_check_reports_a_missing_ledger(self):
        self.add_case("Example0013")
        self.assertEqual(self.run_main("--check"), 1)
        self.assertIn("CertificatePlacement.json is missing", self.err)
        self.assertEqual(len(placement.ledger_problems(self.root)), 1)

    def test_check_reports_a_case_with_no_entry(self):
        self.add_case("Example0013")
        self.run_main()
        self.add_case("Example5013")
        checker = FakeBuilder()
        self.assertEqual(self.run_main("--check", builder=checker), 1)
        self.assertEqual(checker.calls, [])
        self.assertIn("Example5013: no entry in the ledger", self.err)
        self.assertIn("Example5013: no entry in the ledger", placement.ledger_problems(self.root))

    def test_check_reports_a_changed_certificate(self):
        self.add_case("Example5013")
        self.run_main()
        certificate = self.root / "Benchmark" / "Example5013" / "Certificate" / "Invalid.lean"
        certificate.write_text(certificate_text("Example5013") + "-- re-emitted\n",
                               encoding="utf-8")
        self.assertEqual(self.run_main("--check"), 1)
        self.assertIn("the certificate changed since it was measured", self.err)
        self.assertIn("Example5013: the certificate changed since it was measured",
                      placement.ledger_problems(self.root))

    def test_check_reports_a_stale_entry(self):
        self.add_case("Example0013")
        self.run_main()
        (self.root / "Benchmark" / "Example0013" / "Certificate" / "Invalid.lean").unlink()
        self.assertEqual(self.run_main("--check"), 1)
        self.assertIn("stale entry", self.err)
        self.assertIn("Example0013: stale entry, the case has no emitter-written certificate",
                      placement.ledger_problems(self.root))

    def test_check_reports_a_ledger_measured_at_another_limit(self):
        self.add_case("Example0013")
        self.run_main()
        self.assertEqual(self.run_main("--check", "--limit-kb", "10485760"), 1)
        # The limit is what --check was asked about, not a property of the ledger alone.
        self.assertEqual(placement.ledger_problems(self.root), [])

    def test_check_reports_a_ledger_of_the_previous_version_as_stale(self):
        """Version 1 inferred a kill instead of measuring a peak; its entries mean nothing here."""
        self.add_case("Example0013")
        self.run_main()
        ledger = self.ledger()
        ledger["version"] = 1
        for entry in ledger["certificates"].values():
            entry.pop("peakKb", None)
        self.write_ledger(json.dumps(ledger, indent=2) + "\n")
        self.assertEqual(self.run_main("--check"), 1)
        self.assertIn("not version 2", self.err)
        self.assertIn("re-run placement", self.err)
        self.assertEqual(len(placement.ledger_problems(self.root)), 1)

    def test_a_ledger_of_the_previous_version_is_measured_again_and_rewritten(self):
        self.add_case("Example0013")
        self.run_main()
        ledger = self.ledger()
        ledger["version"] = 1
        for entry in ledger["certificates"].values():
            entry.pop("peakKb", None)
        self.write_ledger(json.dumps(ledger, indent=2) + "\n")
        second = FakeBuilder()
        self.assertEqual(self.run_main(builder=second), 0)
        self.assertTrue(second.calls, "a ledger of the previous version was trusted")
        self.assertEqual(self.ledger()["version"], 2)
        self.assertIn("peakKb", self.ledger()["certificates"]["Example0013"])

    def test_check_reports_a_malformed_entry(self):
        self.add_case("Example0013")
        self.run_main()
        for broken, expected in (({"treeSha256": 7, "fits": True, "peakKb": 1},
                                  "treeSha256 is not a string"),
                                 ({"treeSha256": "ab", "fits": "yes", "peakKb": 1},
                                  "fits is not a boolean"),
                                 ({"treeSha256": "ab", "fits": True},
                                  "peakKb is not a non-negative integer"),
                                 ({"treeSha256": "ab", "fits": True, "peakKb": -1},
                                  "peakKb is not a non-negative integer"),
                                 ({"treeSha256": "ab", "fits": True, "peakKb": True},
                                  "peakKb is not a non-negative integer"),
                                 ("not an object", "the ledger entry is not an object")):
            with self.subTest(expected=expected):
                self.write_ledger(json.dumps(
                    {"version": 2, "limitKb": LIMIT,
                     "certificates": {"Example0013": broken}}, indent=2) + "\n")
                problems = placement.ledger_problems(self.root)
                self.assertIn(f"Example0013: {expected}", problems)
                self.assertEqual(self.run_main("--check"), 1)
                self.assertIn(expected, self.err)

    def test_check_reports_a_malformed_ledger_file(self):
        self.add_case("Example0013")
        self.write_ledger("{not json\n")
        self.assertEqual(self.run_main("--check"), 1)
        self.assertEqual(len(placement.ledger_problems(self.root)), 1)
        self.assertIn("malformed", placement.ledger_problems(self.root)[0])

    def test_check_honours_ids(self):
        self.add_case("Example0013")
        self.run_main("--ids", "Example0013")
        self.add_case("Example5013")
        self.assertEqual(self.run_main("--check", "--ids", "Example0013"), 0)
        self.assertEqual(self.run_main("--check"), 1)

    def test_ledger_problems_builds_nothing_and_writes_nothing(self):
        self.add_case("Example0013")
        self.run_main()
        path = self.root / "Benchmark" / "CertificatePlacement.json"
        before = path.read_bytes()
        self.assertEqual(placement.ledger_problems(str(self.root)), [])
        self.assertEqual(path.read_bytes(), before)

    # -- the ledger bytes -----------------------------------------------------------------

    def test_the_ledger_bytes_are_deterministic_and_sorted(self):
        for case in ("Example5013", "Example0013", "Example3001"):
            self.add_case(case)
        self.too_heavy("Example5013")
        self.run_main()
        text = (self.root / "Benchmark" / "CertificatePlacement.json").read_text(encoding="utf-8")
        self.assertTrue(text.endswith("}\n"))
        self.assertIn('\n  "limitKb": ', text)
        self.assertIn('\n      "peakKb": ', text)
        self.assertEqual(list(self.ledger()["certificates"]),
                         ["Example0013", "Example3001", "Example5013"])
        self.assertEqual(self.run_main("--force"), 0)
        self.assertEqual((self.root / "Benchmark" / "CertificatePlacement.json")
                         .read_text(encoding="utf-8"), text)

    def test_the_same_certificate_in_another_checkout_digests_the_same(self):
        self.add_case("Example5013", extra={"leancheck.lean": "-- artifact\n",
                                            "problem.p": "fof(a, axiom, p).\n"})
        first = placement.tree_digest(self.root / "Benchmark" / "Example5013")
        with tempfile.TemporaryDirectory() as other:
            elsewhere = Path(other)
            (elsewhere / "Benchmark").mkdir()
            self.root, keep = elsewhere, self.root
            self.add_case("Example5013", extra={"leancheck.lean": "-- artifact\n",
                                                "problem.p": "fof(a, axiom, p).\n"})
            second = placement.tree_digest(elsewhere / "Benchmark" / "Example5013")
            self.root = keep
        self.assertEqual(first, second)

    def test_a_changed_limit_re_measures_everything(self):
        self.add_case("Example0013")
        self.run_main()
        raised = FakeBuilder()
        self.assertEqual(self.run_main("--limit-kb", "10485760", builder=raised), 0)
        self.assertTrue(raised.calls, "a ledger measured at another limit was trusted")
        self.assertEqual(self.ledger()["limitKb"], 10485760)

    def test_a_safety_cap_below_the_limit_is_refused(self):
        self.add_case("Example0013")
        self.assertEqual(self.run_main("--hard-limit-kb", "1024"), 2)
        self.assertIn("below --limit-kb", self.err)


class LiveTreeLedger(unittest.TestCase):
    """The committed ledger against the committed corpus, with nothing measured.

    This is the same question the registry generator asks before it generates, so it is asked
    here too: a ledger that no longer matches the tree is a stale ledger whatever its bytes say.
    """

    @unittest.skipUnless((REPO / "Benchmark" / "CertificatePlacement.json").is_file(),
                         "no placement ledger in this checkout")
    def test_the_committed_ledger_matches_the_committed_corpus(self):
        problems = placement.ledger_problems(REPO)
        self.assertEqual(problems, [], "run python3 scripts/place_certificates.py --force")


if __name__ == "__main__":
    unittest.main()
