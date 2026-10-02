"""Synthetic, compiler-free tests for the paper-specific saved-receipt audit."""
import copy
from contextlib import redirect_stderr, redirect_stdout
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "paper_repro_audit.py"
SPEC = importlib.util.spec_from_file_location("paper_repro_audit", SCRIPT)
A = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(A)


class DirectLeanAuditTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name)
        self.root = self.repo / "artifacts" / "run"
        self.root.mkdir(parents=True)
        self.case = "Example0001"
        self.directory = self.root / "cases" / self.case
        (self.directory / "check").mkdir(parents=True)
        self.response = b'{"verdict":"valid","source":"synthetic fixture only"}\n'
        (self.directory / "response.json").write_bytes(self.response)
        self.receipt = {
            "schema_version": 1, "case": self.case, "verdict": "valid",
            "status": "valid_proof_checked", "proof_checked": True,
            "failure_stage": None, "response_sha256": hashlib.sha256(self.response).hexdigest(),
            "axioms": sorted(A.STD3), "native_rechecked": [], "native_kernel_rechecked": [],
        }
        self.save(self.root / "run.json", {"cases": [self.case]})
        self.write_receipt(self.receipt)

    @staticmethod
    def save(path, value):
        path.write_text(json.dumps(value), encoding="utf-8")

    def write_receipt(self, receipt, outer=None):
        if outer is None:
            outer = {"check": copy.deepcopy(receipt), "proof_checked": receipt.get("proof_checked"),
                     "status": receipt.get("status")}
        self.save(self.directory / "check" / "result.json", receipt)
        self.save(self.directory / "result.json", outer)

    def assert_classification(self, expected):
        report = A.audit_run(self.root)
        self.assertEqual(report["cases"][0]["classification"], expected)
        self.assertEqual(report["counts"][expected], 1)
        self.assertEqual(sum(report["counts"].values()), 1)
        self.assertEqual(report["complete"], expected not in A.PROBLEMS)
        self.assertEqual(bool(report["issues"]), expected in A.PROBLEMS)
        return report

    def test_std3_all_subset_empty_and_invalid_verdict(self):
        for axioms, verdict in [(sorted(A.STD3), "valid"), (["Quot.sound"], "valid"),
                                ([], "valid"), (["propext"], "invalid")]:
            with self.subTest(axioms=axioms, verdict=verdict):
                receipt = dict(self.receipt, axioms=axioms, verdict=verdict,
                               status=verdict + "_proof_checked")
                self.write_receipt(receipt)
                self.assert_classification("accepted_std3_only")

    def test_native_assertions_and_kernel_fallback_stay_native(self):
        names = ["Unused.helper._native.a", "DirectLeanTask.answer._native.b"]
        for kernel in [[], names[:1], names]:
            with self.subTest(kernel=kernel):
                self.write_receipt(dict(self.receipt, axioms=sorted(A.STD3) + names,
                                        native_rechecked=names, native_kernel_rechecked=kernel))
                report = self.assert_classification("accepted_native_assertions")
                self.assertEqual(report["cases"][0]["native_assertions"], sorted(names))
                self.assertEqual(report["cases"][0]["kernel_fallback"], sorted(kernel))

    def test_unexpected_accepted_axiom_relationships(self):
        native = "answer._native.a"
        changes = [
            {"axioms": ["sorryAx"]},
            {"axioms": [native]},
            {"native_rechecked": [native]},
            {"axioms": ["answer_native.a"], "native_rechecked": ["answer_native.a"]},
            {"axioms": [native], "native_rechecked": [native],
             "native_kernel_rechecked": ["other._native.a"]},
            {"native_rechecked": ["propext"]},
        ]
        for change in changes:
            with self.subTest(change=change):
                self.write_receipt(dict(self.receipt, **change))
                self.assert_classification("unexpected_accepted_axioms")

    def test_rejections_do_not_require_axiom_lists(self):
        for status, stage in [("check_failed", "compile"), ("check_failed", "audit"),
                              ("task_setup_failed", "task"), ("check_timeout", "audit")]:
            with self.subTest(status=status, stage=stage):
                receipt = dict(self.receipt, proof_checked=False, status=status, failure_stage=stage)
                for field in ("axioms", "native_rechecked", "native_kernel_rechecked"):
                    del receipt[field]
                self.write_receipt(receipt)
                report = self.assert_classification("rejected")
                self.assertEqual(report["cases"][0]["detail"], status + ":" + stage)

    def test_malformed_receipt_fields_never_accept(self):
        changes = [
            {"schema_version": True}, {"schema_version": 2}, {"case": "Example0002"},
            {"proof_checked": 1}, {"proof_checked": "true"}, {"proof_checked": None},
            {"verdict": []}, {"verdict": "unknown"}, {"status": "valid_uncertified"},
            {"status": []}, {"failure_stage": "audit"}, {"response_sha256": "wrong"},
            {"axioms": None}, {"axioms": ["propext", "propext"]}, {"axioms": [1]},
            {"axioms": [""]}, {"native_rechecked": "answer._native.a"},
            {"native_kernel_rechecked": [None]},
            {"proof_checked": False},
            {"proof_checked": False, "status": "agent_failed", "failure_stage": "audit"},
            {"proof_checked": False, "status": "check_failed", "failure_stage": None},
        ]
        for change in changes:
            with self.subTest(change=change):
                self.write_receipt(dict(self.receipt, **change))
                self.assert_classification("missing_or_inconsistent_evidence")
        for field in self.receipt:
            with self.subTest(missing=field):
                receipt = dict(self.receipt)
                del receipt[field]
                self.write_receipt(receipt)
                self.assert_classification("missing_or_inconsistent_evidence")

    def test_outer_disagreement_and_bool_integer_copy_comparison(self):
        for change in [{"proof_checked": False}, {"proof_checked": 1},
                       {"status": "invalid_proof_checked"}, {"check": None}]:
            with self.subTest(change=change):
                outer = {"check": copy.deepcopy(self.receipt), "proof_checked": True,
                         "status": "valid_proof_checked"}
                outer.update(change)
                self.write_receipt(self.receipt, outer)
                self.assert_classification("missing_or_inconsistent_evidence")
        outer = {"check": dict(self.receipt, proof_checked=1), "proof_checked": True,
                 "status": "valid_proof_checked"}
        self.write_receipt(self.receipt, outer)
        self.assert_classification("missing_or_inconsistent_evidence")

    def test_missing_corrupt_or_nonobject_case_files(self):
        paths = [self.directory / "result.json", self.directory / "check" / "result.json",
                 self.directory / "response.json"]
        for path in paths:
            original = path.read_bytes()
            with self.subTest(missing=path.name):
                path.unlink()
                self.assert_classification("missing_or_inconsistent_evidence")
                path.write_bytes(original)
        for content in [b"{broken", b"[]", b"\xff", b'{"check":NaN}',
                        b'{"check":true,"check":false}']:
            with self.subTest(content=content):
                (self.directory / "result.json").write_bytes(content)
                self.assert_classification("missing_or_inconsistent_evidence")
        self.write_receipt(self.receipt)
        (self.directory / "response.json").write_bytes(self.response + b" ")
        self.assert_classification("missing_or_inconsistent_evidence")

    def test_invalid_inventory_is_not_inferred_from_directories(self):
        inventories = [None, [], "Example0001", [self.case, self.case], [1], ["../secret"],
                       ["Example0001/other"], ["Example0001\n"], ["secret-token"]]
        for cases in inventories:
            with self.subTest(cases=cases):
                self.save(self.root / "run.json", {"cases": cases, "auth": "DO_NOT_PRINT"})
                report = A.audit_run(self.root)
                self.assertFalse(report["complete"])
                self.assertEqual(report["cases"], [])
                self.assertEqual(sum(report["counts"].values()), 0)
                self.assertEqual(len(report["issues"]), 1)
                self.assertNotIn("DO_NOT_PRINT", json.dumps(report))
                self.assertNotIn("secret-token", json.dumps(report))
        for content in ["[]", "{broken", '{"cases":[],"cases":["Example0001"]}']:
            (self.root / "run.json").write_text(content)
            self.assertFalse(A.audit_run(self.root)["complete"])
        (self.root / "run.json").unlink()
        self.assertFalse(A.audit_run(self.root)["complete"])

    def test_all_declared_cases_remain_visible_and_inputs_are_unchanged(self):
        self.save(self.root / "run.json", {"cases": [self.case, "Example0002"],
                                           "auth": "DO_NOT_PRINT"})
        outer = json.loads((self.directory / "result.json").read_text())
        outer["model_output"] = "DO_NOT_PRINT"
        self.save(self.directory / "result.json", outer)
        before = {path: path.read_bytes() for path in self.root.rglob("*") if path.is_file()}
        report = A.audit_run(self.root)
        self.assertEqual([row["case"] for row in report["cases"]], [self.case, "Example0002"])
        self.assertEqual(report["counts"]["accepted_std3_only"], 1)
        self.assertEqual(report["counts"]["missing_or_inconsistent_evidence"], 1)
        self.assertNotIn("DO_NOT_PRINT", json.dumps(report))
        after = {path: path.read_bytes() for path in self.root.rglob("*") if path.is_file()}
        self.assertEqual(before, after)

    def cli(self, *arguments):
        stdout, stderr = io.StringIO(), io.StringIO()
        with patch.object(A, "ROOT", self.repo), redirect_stdout(stdout), redirect_stderr(stderr):
            status = A.main([str(self.root), *arguments])
        return status, stdout.getvalue(), stderr.getvalue()

    def test_cli_exit_status_and_optional_artifact_json(self):
        status, stdout, stderr = self.cli("--output", "artifacts/audit.json")
        self.assertEqual(status, 0)
        self.assertIn("accepted_std3_only: 1", stdout)
        self.assertEqual(stderr, "")
        self.assertEqual(json.loads((self.repo / "artifacts/audit.json").read_text()),
                         A.audit_run(self.root))
        before = (self.repo / "artifacts/audit.json").read_bytes()
        self.assertEqual(self.cli("--output", "artifacts/audit.json")[0], 2)
        self.assertEqual(before, (self.repo / "artifacts/audit.json").read_bytes())
        self.write_receipt(dict(self.receipt, axioms=["sorryAx"]))
        status, _stdout, stderr = self.cli()
        self.assertEqual(status, 1)
        self.assertIn(self.case, stderr)
        self.write_receipt(dict(self.receipt, proof_checked=False, status="check_failed",
                                failure_stage="compile"))
        self.assertEqual(self.cli()[0], 0)
        (self.root / "run.json").unlink()
        self.assertEqual(self.cli()[0], 1)

    def test_cli_output_paths_cannot_modify_source_or_existing_records(self):
        for destination in ["report.json", "scripts/audit.json", "artifacts/../README.md",
                            "artifacts", str(self.repo / "absolute.json"),
                            "artifacts/run/run.json"]:
            with self.subTest(destination=destination):
                self.assertEqual(self.cli("--output", destination)[0], 2)
        outside = self.repo / "outside"
        outside.mkdir()
        (self.repo / "artifacts" / "escape").symlink_to(outside, target_is_directory=True)
        self.assertEqual(self.cli("--output", "artifacts/escape/audit.json")[0], 2)
        self.assertEqual(list(outside.iterdir()), [])
        self.assertFalse((self.repo / "scripts").exists())
        self.assertEqual(json.loads((self.root / "run.json").read_text()), {"cases": [self.case]})

    def test_standalone_command_works_from_another_directory(self):
        process = subprocess.run([sys.executable, "-B", str(SCRIPT), str(self.root)],
                                 cwd=self.repo, capture_output=True, text=True, check=False)
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertIn("Saved-receipt audit only", process.stdout)


if __name__ == "__main__":
    unittest.main()
