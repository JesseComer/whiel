"""Token-free unit tests for GNU Parallel experiment glue."""
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from agent_houdini import experiment, experiment_pool as pool


class PoolTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.inputs = [f"Example{number:04d}" for number in range(1, 7)]
        for identity in self.inputs:
            directory = self.root / "Benchmark" / identity
            directory.mkdir(parents=True)
            (directory / "Input.lean").write_text("-- fixture\n")
        self.spec = self.root / "spec.json"
        self.settings = {"repo": str(self.root), "model": "fixture", "all_inputs": True,
                         "certify": "never", "workers": 4, "iteration_limit": 6,
                         "search_limit_seconds": 600, "retention": "all", "agent_retention": "all"}
        self.spec.write_text(json.dumps(self.settings))

    def test_dry_run_has_no_side_effects(self):
        with patch.object(pool.subprocess, "Popen") as launch:
            self.assertEqual(pool.run_pool(self.spec, dry_run=True, out=io.StringIO()), 0)
            launch.assert_not_called()
        self.assertFalse((self.root / "artifacts").exists())

    def test_public_pool_command_forwards_configuration(self):
        auth = self.root / "auth"
        with patch.object(pool, "run_pool", return_value=3) as run:
            self.assertEqual(experiment.main([
                "pool", str(self.spec), "--jobs", "4", "--auth-root", str(auth),
                "--parallel", "/usr/bin/parallel", "--dry-run"]), 3)
        run.assert_called_once_with(self.spec, jobs=4, dry_run=True,
                                    auth_root=auth, parallel="/usr/bin/parallel")

    def test_inputs_and_budgets_preserved(self):
        resolved = experiment.resolve_spec(self.settings)
        self.assertEqual(pool.selected_inputs(resolved), self.inputs)
        child = pool._child_spec(resolved, self.inputs[0], self.root / "pool")
        self.assertEqual(child["inputs"], [self.inputs[0]])
        self.assertFalse(child["all_inputs"])
        for key in ("model", "workers", "iteration_limit", "search_limit_seconds",
                    "certify", "retention", "agent_retention"):
            self.assertEqual(child[key], resolved[key])

    def test_invalid_scope_refused(self):
        for change in ({"certify": "inline"}, {"agent_args": ["--other"]},
                       {"verifier_args": ["--all"]},
                       {"verifier_args": ["--no-tools", "--all"]},
                       {"verifier_args": ["--no-tools", "--no-tools"]},
                       {"verifier_args": ["--tools", "history"]},
                       {"verifier_args": ["--no-tools"], "agent_args": ["--other"]},
                       {"all_inputs": False, "inputs": ["Example9999"]}):
            self.spec.write_text(json.dumps(self.settings | change))
            with self.assertRaises(experiment.SpecError):
                pool.run_pool(self.spec, dry_run=True)
        with self.assertRaises(experiment.SpecError):
            pool.run_pool(self.spec, jobs=0)

    def test_no_tools_arm_preserves_every_other_setting(self):
        root = Path(__file__).resolve().parents[2]
        path = root / "agent_houdini/experiments/full-benchmark.json"
        base = experiment.load_spec(path)
        arm = {**base, "verifier_args": ["--no-tools"]}
        resolved = experiment.resolve_spec(arm)
        inputs = pool.selected_inputs(resolved)
        self.assertEqual(len(inputs), 86)
        for identity in inputs:
            child = experiment.resolve_spec(pool._child_spec(resolved, identity, self.root))
            command, environment, _ = experiment.build_command(child, self.root)
            self.assertEqual(child["verifier_args"], ["--no-tools"])
            self.assertEqual(command.count("--no-tools"), 1)
            self.assertIsNone(child["skills_file"])
            self.assertIsNone(child["skills_dir"])
            self.assertFalse(set(pool.SKILL_VARIABLES) & environment.keys())
            for key in ("model", "reasoning_effort", "search_limit_seconds", "iteration_limit",
                        "workers", "certify", "retention", "agent_retention"):
                self.assertEqual(child[key], resolved[key])
        with patch.object(experiment, "load_spec", return_value=arm), \
                patch.object(pool.subprocess, "Popen") as launch:
            self.assertEqual(pool.run_pool(path, jobs=4, dry_run=True, out=io.StringIO()), 0)
            launch.assert_not_called()

    def test_auth_required_and_private(self):
        with self.assertRaises(experiment.SpecError):
            pool.worker_homes(None, 4)
        root = self.root / "auth"
        for number in range(1, 5):
            home = root / f"worker-{number}"
            home.mkdir(parents=True, mode=0o700)
            auth = home / "auth.json"
            auth.write_text("synthetic")
            auth.chmod(0o600)
        self.assertEqual(len(pool.worker_homes(root, 4)), 4)
        auth.chmod(0o644)
        with self.assertRaises(experiment.SpecError):
            pool.worker_homes(root, 4)
        auth.chmod(0o600)
        auth.unlink()
        auth.symlink_to(root / "worker-1" / "auth.json")
        with self.assertRaises(experiment.SpecError):
            pool.worker_homes(root, 4)

    def test_gnu_owns_slots_and_refill(self):
        command = pool.parallel_command("/usr/bin/parallel", self.root, 4)
        self.assertIn("--plain", command)
        self.assertEqual(command[command.index("--jobs") + 1], "4")
        self.assertEqual(command[command.index("--halt") + 1], "soon,fail=1")
        self.assertIn("{%} {}", command[-3])
        self.assertNotIn("--retries", command)

    def settle(self, code, status, failure=None, resource=None):
        identity = self.inputs[0]
        run = self.root / "cases" / identity / "fixture"
        (run / "verifier" / identity).mkdir(parents=True, exist_ok=True)
        (run / "run.json").write_text("{}")
        (run / "verifier" / "summary.json").write_text(json.dumps({"resource_failure": resource}))
        (run / "verifier" / identity / "result.json").write_text(json.dumps({
            "status": status, "failure_kind": failure, "search_seconds": 12.5}))
        row = {"input": identity}
        reason = pool._settle(self.root, row, code)
        return reason, row

    def test_expected_outcomes_are_not_scheduler_failures(self):
        for code, status, failure in (
            (4, "valid_uncertified", None), (4, "invalid_uncertified", None),
            (3, "search_timeout", "OverallTimeout"),
            (3, "incomplete", "IterationLimitExhausted")):
            reason, row = self.settle(code, status, failure)
            self.assertIsNone(reason)
            self.assertEqual(row["state"], "finished")
            self.assertEqual(row["search_seconds"], 12.5)

    def test_infrastructure_and_missing_records_stop_dispatch(self):
        for code, status, failure, resource in (
            (3, "incomplete", "InfrastructureFailure", None),
            (3, "resource_exhausted", None, "guard"), (2, "incomplete", None, None)):
            reason, row = self.settle(code, status, failure, resource)
            self.assertIsNotNone(reason)
            self.assertEqual(row["state"], "failed")
        self.assertIsNotNone(pool._settle(self.root, {"input": self.inputs[-1]}, 4))

    def test_worker_gets_own_home_and_keeps_campaign_exit(self):
        auth_root = self.root / "auth"
        for number in range(1, 5):
            home = auth_root / f"worker-{number}"
            home.mkdir(parents=True, mode=0o700)
            auth = home / "auth.json"
            auth.write_text("synthetic")
            auth.chmod(0o600)
        for folder in ("specs", "logs", "records"):
            (self.root / folder).mkdir()
        identity = self.inputs[0]
        record = {"jobs": 4, "state": "running", "spec": {"proposer": "agent"},
                  "cases": [{"input": identity, "state": "queued"}]}
        pool._save(self.root, record)
        self.settle(4, "valid_uncertified")
        environment = {"WHIEL_POOL_AUTH_ROOT": str(auth_root), "CODEX_HOME": "wrong",
                       **{key: "inherited-skill" for key in pool.SKILL_VARIABLES}}
        with patch.dict(os.environ, environment), patch.object(pool.subprocess, "Popen") as launch:
            launch.return_value.wait.return_value = 4
            launch.return_value.poll.return_value = 4
            self.assertEqual(pool.run_worker(self.root, 3, identity), 0)
            env = launch.call_args.kwargs["env"]
            self.assertEqual(env["CODEX_HOME"], str(auth_root / "worker-3"))
            self.assertNotIn("WHIEL_POOL_AUTH_ROOT", env)
            for key in pool.SKILL_VARIABLES:
                self.assertNotIn(key, env)
        row = experiment._json(self.root / "records" / (identity + ".json"))
        self.assertEqual(row["slot"], 3)
        self.assertEqual(row["exit_code"], 4)
        self.assertEqual(row["state"], "finished")
        with self.assertRaises(FileExistsError), patch.dict(os.environ, environment):
            pool.run_worker(self.root, 3, identity)


if __name__ == "__main__":
    unittest.main()
