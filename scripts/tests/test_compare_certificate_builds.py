import importlib.util
import json
import os
from pathlib import Path
from types import SimpleNamespace
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "compare_certificate_builds.py"
SPEC = importlib.util.spec_from_file_location("compare_certificate_builds", SCRIPT)
C = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(C)


class ComparisonTests(unittest.TestCase):
    def test_phase_diagnostics_distinguish_failed_and_unfinished_launches(self):
        def event(identity, phase, kind, **fields):
            return "certificate phase: " + json.dumps(dict(
                version=1, id=identity, phase=phase, subject="fixture", event=kind, **fields))
        log = "\n".join([
            event(1, "lake", "start"),
            event(1, "lake", "finish", outcome="failure", elapsed_seconds=2.0),
            event(2, "lake", "start"),
            event(2, "lake", "finish", outcome="success", elapsed_seconds=3.0),
            event(3, "lake", "start"),
            event(4, "sat", "start"),
            event(4, "sat", "finish", outcome="cancelled", elapsed_seconds=1.0),
            "certificate phase: {broken",
        ])
        result = C.phase_diagnostics(log)
        self.assertEqual(result["lake_launches"], 3)
        self.assertEqual(result["lake_completions"], 1)
        self.assertEqual(result["malformed_phase_events"], 1)
        self.assertEqual([p["outcome"] for p in result["phase_timings"]],
                         ["failure", "success", "incomplete", "cancelled"])
        self.assertIsNone(result["phase_timings"][2]["elapsed_seconds"])
        self.assertEqual(C.phase_diagnostics("certificate compiler: Lake completed 4 modules")
                         ["lake_launches"], 0)

    def test_settings_require_requested_backend_and_solver_bound(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "settings.json"
            value = dict(kind="whiel_certificate_build_settings", version=1,
                         compiler="lake", solver_jobs=2,
                         preparation_packaging_cpu_worker_limit=1)
            path.write_text(json.dumps(value))
            self.assertEqual(C.validate_settings(path, "lake", "valid", 2), value)
            for backend, shape, jobs in [("sequential", "valid", 2),
                                         ("lake", "valid", 1), ("lake", "invalid", 2)]:
                with self.assertRaises(ValueError):
                    C.validate_settings(path, backend, shape, jobs)
            value["solver_jobs"] = 0
            path.write_text(json.dumps(value))
            C.validate_settings(path, "lake", "invalid", 2)

    def test_inventory_and_profiles(self):
        records = C.inventory(C.REPO)
        self.assertEqual(len(records), 86)
        self.assertEqual(sum(p.name == "Core.json" for p in records.values()), 69)
        self.assertEqual(C.profiles("Example5034"), ("casc_2025", 120))
        self.assertEqual(C.profiles("Example0001"), ("direct", 60))

    def test_receipt_requires_exact_axioms_and_shape(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "receipt.json"
            receipt = dict(kind="whiel_certificate_build_receipt", version=4,
                           canonical_id="Example0001", shape="valid", axioms=list(C.STD3),
                           certificate_module="Benchmark.Example0001.Certificate.Valid")
            path.write_text(json.dumps(receipt))
            C.validate_receipt(path, "Example0001", "valid")
            receipt["axioms"].append("sorryAx")
            path.write_text(json.dumps(receipt))
            with self.assertRaises(ValueError):
                C.validate_receipt(path, "Example0001", "valid")

    def test_timeout_cleans_child_in_separate_session(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            marker = directory / "child.pid"
            program = (
                "import pathlib,subprocess,sys,time; "
                "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)'],start_new_session=True); "
                "pathlib.Path(sys.argv[1]).write_text(str(p.pid)); time.sleep(30)"
            )
            result = C.watched_run([sys.executable, "-c", program, str(marker)], directory,
                                   os.environ.copy(), directory / "log", 0.8, 12582912)
            self.assertEqual(result["outcome"], "timeout")
            self.assertTrue(result["cleanup_ok"])
            child = C.process_snapshot().get(int(marker.read_text()))
            self.assertTrue(child is None or child[3].startswith("Z"))

    def test_memory_limit_is_reported_separately(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            result = C.watched_run([sys.executable, "-c", "import time; time.sleep(30)"],
                                   directory, os.environ.copy(), directory / "log", 5, 1)
            self.assertEqual(result["outcome"], "memory_limit")
            self.assertTrue(result["cleanup_ok"])

    def test_per_process_limit_is_distinct_from_aggregate_limit(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            result = C.watched_run([sys.executable, "-c", "import time; time.sleep(30)"],
                                   directory, os.environ.copy(), directory / "log", 5,
                                   12582912, process_memory_kb=1)
            self.assertEqual(result["outcome"], "process_memory_limit")
            self.assertTrue(result["cleanup_ok"])
            self.assertGreater(result["peak_process_rss_kb"], 1)
            self.assertLess(result["peak_tree_rss_kb"], 12582912)

    def test_inspection_failure_stops_leader_and_refuses_continuation(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            with patch.object(C, "process_snapshot", side_effect=OSError("inspection unavailable")):
                result = C.watched_run([sys.executable, "-c", "import time; time.sleep(30)"],
                                       directory, os.environ.copy(), directory / "log", 5, 12582912)
            self.assertEqual(result["outcome"], "infrastructure_failure")
            self.assertFalse(result["cleanup_ok"])
            self.assertLess(result["exit_code"], 0)

    def test_lake_only_summary_does_not_claim_a_sequential_run(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            C.write_summary(directory, {("Example0001", "lake"): {
                "outcome": "success", "elapsed_seconds": 1.0,
                "serial_recovery": False, "job_proof_digests": {}}}, ["lake"])
            with (directory / "comparison.csv").open() as stream:
                row = next(C.csv.DictReader(stream))
            self.assertEqual(row["sequential_outcome"], "not_run")
            self.assertEqual(row["speedup"], "")

    def test_old_runner_cannot_be_reported_as_successful_lake_build(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            record = directory / "Core.json"
            record.write_text("{}")
            args = SimpleNamespace(output=directory / "results", runner=Path("runner"),
                                   worker=Path("worker"), threads=2, solver_jobs=1, limit=180,
                                   memory_kb=12582912, process_memory_kb=4194304)

            def old_runner(command, cwd, env, log, limit, memory_kb, process_memory_kb):
                log.write_text("old sequential runner succeeded\n")
                (log.parent / "receipt.json").write_text(json.dumps(dict(
                    kind="whiel_certificate_build_receipt", version=4,
                    canonical_id="Example0001", shape="valid", axioms=list(C.STD3),
                    certificate_module="Benchmark.Example0001.Certificate.Valid")))
                (log.parent / "Certificate").mkdir()
                (log.parent / "Certificate/Valid.lean").write_text("-- fixture\n")
                return dict(outcome="finished", elapsed_seconds=1, exit_code=0, cleanup_ok=True)

            with patch.object(C, "watched_run", side_effect=old_runner):
                result = C.run_attempt(args, "Example0001", record, "lake")
            self.assertEqual(result["outcome"], "bad_receipt")
            self.assertIn("missing successful Lake build", result["receipt_error"])


if __name__ == "__main__":
    unittest.main()
