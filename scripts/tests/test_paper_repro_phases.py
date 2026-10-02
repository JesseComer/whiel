"""PAPER REPRODUCTION CODE: isolated phase routing and retained-trial fixtures."""
from contextlib import redirect_stderr, redirect_stdout
import io
from pathlib import Path
import unittest
from unittest.mock import patch

from scripts import paper_repro_certify as cert
from scripts import paper_repro_common as common
from scripts import paper_repro_search as search
from scripts import paper_repro_setup as setup
from scripts import reproduce_paper as cli
from scripts.tests import test_paper_repro_search as search_fixtures


class PhaseTests(unittest.TestCase):
    def setUp(self):
        self.fixture = search_fixtures.SearchTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.ctx = self.fixture.ctx
        self.repo = self.ctx.repo.resolve()
        self.out = self.ctx.output_root.resolve()
        self.ctx.repo, self.ctx.output_root = self.repo, self.out
        self.ctx.trial = self.ctx.trial.resolve()
        self.inputs = self.fixture.inputs
        sources = []
        for identity in self.inputs:
            relative = f"Benchmark/{identity}/Input.lean"
            path = self.repo / relative
            path.parent.mkdir(parents=True)
            path.write_text("synthetic input\n")
            sources.append(relative)
        for relative in ("lean-toolchain", "toolchain.lock.json", "lakefile.toml", "lake-manifest.json",
                         "agent_houdini/toolchain/cli-lock.json"):
            path = self.repo / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("synthetic pin\n")
            sources.append(relative)
        sources += ["agent_houdini/experiments/full-benchmark-lean-agent.json"]
        sources += [f"agent_houdini/experiments/paper/{arm}.json" for arm in common.ARMS]
        self.ctx.manifest.update(
            schema_version=1, state="prepared", trial=self.ctx.rel(self.ctx.trial),
            output_root=self.ctx.rel(self.out),
            source_sha256={name: common.digest(self.repo / name) for name in sources},
            certification={"state": "pending", "expected_pairs": None, "attempts": []},
        )
        self.ctx.save()
        common.atomic_json(self.out / "current.json", {
            "schema_version": 1, "manifest": self.ctx.rel(self.ctx.trial / "manifest.json"),
        })
        common.atomic_json(self.out / "setup.json", {"state": "complete"})
        self.pool = self.mock(search, "command", side_effect=self.fixture.fake_pool)
        self.search = self.mock(search, "run_search", wraps=search.run_search)
        self.direct = self.mock(search, "run_direct_lean", side_effect=self.complete_direct)
        self.certify = self.mock(cert, "run_certification", side_effect=self.complete_certification)
        self.cpu = self.mock(cert, "cpu_lanes", return_value=[list(range(12)), list(range(12, 24))])
        self.provider = self.mock(setup, "verify_cli", return_value=Path("synthetic-cli"))
        from agent_houdini import lean_baseline_utils
        self.homes = self.mock(lean_baseline_utils, "worker_homes", return_value=[])
        self.mock(common, "benchmark_ids", return_value=self.inputs)
        self.mock(common.subprocess, "check_output", return_value="synthetic revision\n")
        self.mock(common.subprocess, "Popen", side_effect=AssertionError("Unexpected external process"))

    def mock(self, target, name, **kwargs):
        patcher = patch.object(target, name, **kwargs)
        mocked = patcher.start()
        self.addCleanup(patcher.stop)
        return mocked

    def execute(self, phase, model=None, fresh=False):
        try:
            with redirect_stdout(io.StringIO()):
                return cli.execute(common.Context(self.repo, self.out), phase, model, fresh)
        finally:
            self.ctx = common.current_trial(self.repo, self.out)

    def all_search(self):
        for model in common.MODELS:
            self.execute("search", model)

    def complete_direct(self, ctx):
        directory = ctx.trial / "direct-lean/run"
        common.atomic_json(directory / "run.json", {"cases": self.inputs})
        common.atomic_json(directory / "summary.json", {
            "total": len(self.inputs), "finished": len(self.inputs), "proof_checked": 0,
        })
        ctx.manifest["direct_lean"].update(state="complete", run=ctx.rel(directory))
        ctx.save()

    def complete_certification(self, ctx, lanes):
        self.assertEqual(lanes, self.cpu.return_value)
        chosen = common.successful_search_cases(ctx)
        stage = ctx.manifest["certification"]
        stage.update(state="complete", expected_pairs=[], attempts=[])
        for row in chosen:
            pair = {"arm": row["arm"], "input": row["input"]}
            stage["expected_pairs"].append(pair)
            directory = ctx.trial / "certification" / row["arm"] / row["input"]
            common.atomic_json(directory / "supervisor.json", dict(pair, outcome="timeout"))
            stage["attempts"].append(dict(pair, state="complete", directory=ctx.rel(directory)))
        ctx.save()

    def reset_calls(self):
        for mocked in (self.pool, self.search, self.direct, self.certify, self.cpu,
                       self.provider, self.homes, self.fixture.verify):
            mocked.reset_mock()

    def assert_preflight_rejected(self, phase, model=None, fresh=False):
        manifest_path = self.ctx.trial / "manifest.json"
        before = manifest_path.read_bytes()
        pointer = (self.out / "current.json").read_bytes()
        self.reset_calls()
        with self.assertRaises(common.ReproError):
            self.execute(phase, model, fresh)
        self.assertEqual(manifest_path.read_bytes(), before)
        self.assertEqual((self.out / "current.json").read_bytes(), pointer)
        for mocked in (self.pool, self.search, self.direct, self.certify, self.cpu,
                       self.provider, self.homes, self.fixture.verify):
            mocked.assert_not_called()

    def test_search_routes_only_requested_model_without_certification_cpu(self):
        for index, model in enumerate(common.MODELS):
            self.reset_calls()
            self.assertEqual(self.execute("search", model), 0)
            self.search.assert_called_once()
            self.assertEqual(self.search.call_args.args[1], model)
            self.assertEqual(self.pool.call_count, 4)
            self.provider.assert_called_once_with(self.search.call_args.args[0], search.CLI_VERSIONS[model])
            self.homes.assert_called_once_with(self.ctx.auth_root.resolve(), 4)
            self.cpu.assert_not_called()
            self.direct.assert_not_called()
            self.certify.assert_not_called()
            self.assertEqual(self.ctx.manifest["state"], "ready")
            for stage in self.ctx.manifest["search"]:
                expected = "complete" if common.MODELS.index(stage["model"]) <= index else "pending"
                self.assertEqual(stage["state"], expected)
            report = (self.ctx.trial / "report.md").read_text()
            self.assertIn("Execution state: ready", report)
            self.assertIn("Direct Lean: pending", report)

    def test_direct_lean_runs_independently_and_leaves_whiel_pending(self):
        self.assertEqual(self.execute("direct-lean"), 0)
        self.direct.assert_called_once()
        self.provider.assert_called_once_with(self.direct.call_args.args[0], "0.148.0")
        self.homes.assert_called_once_with(self.ctx.auth_root.resolve(), 4)
        self.cpu.assert_not_called()
        self.search.assert_not_called()
        self.certify.assert_not_called()
        self.assertEqual(self.ctx.manifest["state"], "ready")
        self.assertTrue(all(stage["state"] == "pending" for stage in self.ctx.manifest["search"]))
        self.assert_preflight_rejected("direct-lean")

    def test_direct_lean_existing_destination_preserves_ready_trial_and_escalation(self):
        self.execute("search", common.MODELS[0])
        directory = self.ctx.trial / "direct-lean"
        directory.mkdir()
        marker = directory / "retained.txt"
        marker.write_text("preserve existing artifact")
        self.assert_preflight_rejected("direct-lean")
        self.assertEqual(self.ctx.manifest["state"], "ready")
        self.assertEqual(self.ctx.manifest["direct_lean"]["state"], "pending")
        self.execute("search", common.MODELS[1])
        self.assertEqual(self.ctx.manifest["state"], "ready")
        self.assertEqual(marker.read_text(), "preserve existing artifact")
        self.direct.assert_not_called()

    def test_direct_lean_invalid_pinned_spec_preserves_ready_trial_and_escalation(self):
        self.execute("search", common.MODELS[0])
        relative = "agent_houdini/experiments/full-benchmark-lean-agent.json"
        path = self.repo / relative
        original = common.read_json(path)
        changes = [
            lambda value: value.update(model=common.MODELS[1]),
            lambda value: value.update(reasoning_effort="high"),
            lambda value: value.update(agent_seconds=600),
            lambda value: value.pop("agent_seconds"),
            lambda value: value.update(provider_cli="artifacts/other-cli"),
        ]
        for index, change in enumerate(changes):
            with self.subTest(change=index):
                value = dict(original)
                change(value)
                common.atomic_json(path, value)
                # Model a trial whose recorded source already had an invalid baseline
                # setting, so source drift cannot mask the protocol preflight.
                self.ctx.manifest["source_sha256"][relative] = common.digest(path)
                self.ctx.save()
                self.assert_preflight_rejected("direct-lean")
                self.assertEqual(self.ctx.manifest["state"], "ready")
                self.assertEqual(self.ctx.manifest["direct_lean"]["state"], "pending")
        self.execute("search", common.MODELS[1])
        self.assertEqual(self.ctx.manifest["state"], "ready")
        self.direct.assert_not_called()

    def test_direct_lean_noncanonical_destination_is_read_only(self):
        self.execute("search", common.MODELS[0])
        target = self.ctx.trial / "other-destination"
        (self.ctx.trial / "direct-lean").symlink_to(target.name, target_is_directory=True)
        self.assert_preflight_rejected("direct-lean")
        self.assertFalse(target.exists())
        self.assertEqual(self.ctx.manifest["state"], "ready")
        self.assertEqual(self.ctx.manifest["direct_lean"]["state"], "pending")

    def test_certify_needs_no_provider_workers_or_direct_lean(self):
        self.all_search()
        self.reset_calls()
        self.assertEqual(self.execute("certify"), 0)
        self.cpu.assert_called_once_with()
        self.certify.assert_called_once()
        for mocked in (self.pool, self.search, self.direct, self.provider, self.homes, self.fixture.verify):
            mocked.assert_not_called()
        self.assertEqual(self.ctx.manifest["direct_lean"]["state"], "pending")
        self.assertEqual(self.ctx.manifest["state"], "ready")
        with redirect_stdout(io.StringIO()):
            self.assertEqual(cli.report(self.ctx), 0)
        self.assert_preflight_rejected("certify")

    def test_complete_requires_search_baseline_and_certification(self):
        self.all_search()
        self.execute("certify")
        self.assertFalse(cli.completed_trial(self.ctx))
        self.execute("direct-lean")
        self.assertTrue(cli.completed_trial(self.ctx))
        self.assertEqual(self.ctx.manifest["state"], "complete")
        self.assertIn("Execution state: complete", (self.ctx.trial / "report.md").read_text())
        with redirect_stdout(io.StringIO()):
            self.assertEqual(cli.report(self.ctx), 0)
        self.assert_preflight_rejected("search", common.MODELS[0])

    def test_out_of_order_and_duplicate_searches_preserve_ready_state(self):
        self.assert_preflight_rejected("search", common.MODELS[1])
        self.assert_preflight_rejected("search", common.MODELS[2])
        self.assert_preflight_rejected("certify")
        self.execute("search", common.MODELS[0])
        self.assert_preflight_rejected("search", common.MODELS[0])
        self.assert_preflight_rejected("search", common.MODELS[2])
        self.assertEqual(self.ctx.manifest["state"], "ready")
        self.assert_preflight_rejected("certify")

    def test_source_drift_and_terminal_or_stale_trial_stop_before_dispatch(self):
        self.execute("search", common.MODELS[0])
        path = self.repo / "Benchmark" / self.inputs[0] / "Input.lean"
        original = path.read_bytes()
        path.write_text("changed input\n")
        for phase, model in (("search", common.MODELS[1]), ("direct-lean", None), ("certify", None)):
            with self.subTest(source_drift=phase):
                self.assert_preflight_rejected(phase, model)
        path.write_bytes(original)
        for state in ("failed", "interrupted", "running"):
            self.ctx.manifest["state"] = state
            self.ctx.save()
            for phase, model in (("search", common.MODELS[1]), ("direct-lean", None), ("certify", None)):
                with self.subTest(state=state, phase=phase):
                    self.assert_preflight_rejected(phase, model)
        with redirect_stdout(io.StringIO()):
            self.assertEqual(cli.report(self.ctx), 1)
        self.assertIn("stale running record", (self.ctx.trial / "report.md").read_text())

    def test_tampered_retained_search_evidence_blocks_certification_read_only(self):
        self.all_search()
        stage = self.ctx.manifest["search"][0]
        pool = self.ctx.path(stage["pool"])
        child = self.ctx.path(stage["cases"][0]["run_directory"])
        changes = [
            (pool / "pool.json", lambda value: value["cases"].pop()),
            (pool / "pool.json", lambda value: value["spec"].update(iteration_limit=6)),
            (child / "verifier" / self.inputs[0] / "result.json", lambda value: value.update(status="search_timeout")),
            (child / "verifier" / self.inputs[0] / "result.json", lambda value: value.update(search_seconds=999)),
        ]
        for index, (path, change) in enumerate(changes):
            with self.subTest(change=index):
                original = path.read_bytes()
                value = common.read_json(path)
                change(value)
                common.atomic_json(path, value)
                self.assert_preflight_rejected("certify")
                self.assertEqual(self.ctx.manifest["state"], "ready")
                self.assertEqual(self.ctx.manifest["certification"]["attempts"], [])
                path.write_bytes(original)
        self.execute("certify")
        self.assertEqual(self.ctx.manifest["certification"]["state"], "complete")

    def test_new_preserves_prior_trials_and_only_allows_initial_phases(self):
        self.execute("search", common.MODELS[0])
        old_path = self.ctx.trial / "manifest.json"
        old_manifest = old_path.read_bytes()
        for model in common.MODELS[1:]:
            self.assert_preflight_rejected("search", model, fresh=True)
        self.assert_preflight_rejected("certify", fresh=True)
        self.execute("search", common.MODELS[0], fresh=True)
        self.assertNotEqual(self.ctx.trial, old_path.parent)
        self.assertEqual(old_path.read_bytes(), old_manifest)
        middle_path = self.ctx.trial / "manifest.json"
        middle_manifest = middle_path.read_bytes()
        self.execute("direct-lean", fresh=True)
        self.assertNotIn(self.ctx.trial, (old_path.parent, middle_path.parent))
        self.assertEqual(old_path.read_bytes(), old_manifest)
        self.assertEqual(middle_path.read_bytes(), middle_manifest)
        self.assertTrue(all(stage["state"] == "pending" for stage in self.ctx.manifest["search"]))
        self.assertEqual(self.ctx.manifest["direct_lean"]["state"], "complete")
        pins = self.ctx.manifest["source_sha256"]
        self.assertIn("agent_houdini/toolchain/cli-lock.json", pins)
        self.assertIn("agent_houdini/experiments/full-benchmark-lean-agent.json", pins)

    def test_without_current_trial_only_initial_phases_can_start(self):
        pointer = self.out / "current.json"
        pointer.unlink()
        for phase, model in (("search", common.MODELS[1]), ("search", common.MODELS[2]), ("certify", None)):
            with self.subTest(phase=phase, model=model), redirect_stdout(io.StringIO()):
                with self.assertRaises(common.ReproError):
                    cli.execute(common.Context(self.repo, self.out), phase, model)
                self.assertFalse(pointer.exists())
        self.execute("direct-lean")
        self.assertTrue(pointer.exists())
        self.assertEqual(self.ctx.manifest["state"], "ready")

    def test_execution_failure_and_interruption_write_partial_reports(self):
        for error, state in ((common.ReproError("synthetic pool failure"), "failed"),
                             (common.Interrupted("synthetic interrupt"), "interrupted")):
            with self.subTest(state=state):
                self.pool.side_effect = error
                with self.assertRaises(type(error)):
                    self.execute("search", common.MODELS[0], fresh=True)
                self.assertEqual(self.ctx.manifest["state"], state)
                self.assertEqual(self.ctx.manifest["phase_commands"][-1]["state"], state)
                self.assertIsNone(self.ctx.manifest["active_command"])
                self.assertEqual(self.ctx.manifest["search"][0]["state"], state)
                report = (self.ctx.trial / "report.md").read_text()
                self.assertIn(f"Execution state: {state}", report)
                self.assertIn("Incomplete or inconsistent evidence", report)
                self.assertIn("pending; not started", report)
                self.assert_preflight_rejected("search", common.MODELS[0])

    def test_report_failure_retains_original_execution_failure(self):
        self.pool.side_effect = common.Interrupted("synthetic interruption")
        with patch.object(cli, "report", side_effect=OSError("synthetic report failure")), redirect_stderr(io.StringIO()):
            with self.assertRaisesRegex(common.Interrupted, "synthetic interruption"):
                self.execute("search", common.MODELS[0])
        self.assertEqual(self.ctx.manifest["state"], "interrupted")
        self.assertEqual(self.ctx.manifest["report_error"], "synthetic report failure")
        self.assertIsNone(self.ctx.manifest["active_command"])

    def test_cli_parser_dispatches_only_explicit_commands(self):
        with patch.object(cli, "ROOT", self.repo), patch.object(cli, "execute", return_value=0) as execute:
            for model in common.MODELS:
                self.assertEqual(cli.main(["search", model]), 0)
                self.assertEqual(execute.call_args.args[1:], ("search", model, False))
            self.assertEqual(cli.main(["search", common.MODELS[0], "--new"]), 0)
            self.assertEqual(execute.call_args.args[1:], ("search", common.MODELS[0], True))
            self.assertEqual(cli.main(["direct-lean", "--new"]), 0)
            self.assertEqual(execute.call_args.args[1:], ("direct-lean", None, True))
            self.assertEqual(cli.main(["certify"]), 0)
            self.assertEqual(execute.call_args.args[1:], ("certify", None, False))
            execute.reset_mock()
            for arguments in (["run"], ["search"], ["search", "unlisted-model"], ["certify", "--new"]):
                with self.subTest(arguments=arguments), redirect_stderr(io.StringIO()):
                    with self.assertRaises(SystemExit) as error:
                        cli.main(arguments)
                    self.assertEqual(error.exception.code, 2)
            execute.assert_not_called()


if __name__ == "__main__":
    unittest.main()
