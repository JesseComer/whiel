"""PAPER REPRODUCTION CODE: synthetic orchestration tests; no models or builds."""
from copy import deepcopy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts.paper_repro_common import ARMS, MODELS, Context, Interrupted, ReproError, read_json, successful_search_cases
from scripts import paper_repro_search as search


class SearchTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name)
        self.inputs = ["Example0001", "Example0013", "Example0134"]
        templates = self.repo / "agent_houdini/experiments/paper"
        templates.mkdir(parents=True)
        for arm in ARMS:
            (templates / f"{arm}.json").write_text(json.dumps({
                "model": "old", "iteration_limit": 6, "notes": "historical fixture",
                "all_inputs": True, "verifier_args": ["--wrong"], "skills_dir": "wrong",
            }))
        self.baseline = self.repo / "agent_houdini/experiments/full-benchmark-lean-agent.json"
        self.baseline.write_text(json.dumps({
            "model": "gpt-5.5", "reasoning_effort": "medium", "agent_seconds": None,
            "provider_cli": "artifacts/provider-cli/0.148.0/x86_64-unknown-linux-musl/codex",
            "model_catalog": "artifacts/provider-cli/0.148.0/x86_64-unknown-linux-musl/models.json",
        }))
        output = self.repo / "artifacts/paper-reproduction"
        self.ctx = Context(self.repo, output, output / "runs/fixture", {
            "inputs": self.inputs, "commands": [],
            "search": [{"arm": arm, "model": model, "state": "pending", "inputs": None, "cases": []}
                       for arm in ARMS for model in MODELS],
            "direct_lean": {"state": "pending", "inputs": self.inputs},
        })
        self.ctx.save()
        self.calls = []
        self.mutation = None
        self.all_solved = False
        self.verify = patch.object(search, "verify_cli", return_value=Path("unused-cli")).start()
        self.addCleanup(patch.stopall)

    def write(self, path, value):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value))

    def fake_pool(self, ctx, arguments, log=None, **kwargs):
        self.calls.append((arguments, kwargs))
        self.assertEqual(arguments[1:5], ["-m", "agent_houdini", "experiment", "pool"])
        spec = read_json(ctx.path(arguments[5]))
        pool = ctx.path(spec["output_root"]) / "date-and-suffix-not-predicted-37"
        rows = []
        for identity in spec["inputs"]:
            solved = self.all_solved or identity == self.inputs[0] or (
                identity == self.inputs[1] and spec["model"] != "gpt-5.5")
            status = ("invalid_uncertified" if identity == self.inputs[1] else "valid_uncertified") if solved else "search_timeout"
            code = 4 if solved else 3
            location = f"cases/{identity}/unpredictable-child-29"
            child = pool / location
            child_spec = dict(spec, inputs=[identity], all_inputs=False, output_root=ctx.rel(pool / "cases" / identity))
            self.write(child / "run.json", {"spec": child_spec, "status": "finished", "exit_code": code})
            result = {"input": identity, "status": status, "search_seconds": 2.5}
            self.write(child / "verifier" / identity / "result.json", result)
            self.write(child / "verifier/summary.json", {
                "selected_inputs": [identity], "interrupted": False,
                "unrun_inputs": [], "resource_failure": None, "results": [result],
            })
            if solved:
                self.write(child / "verifier" / identity / "Accepted.json", {})
                self.write(child / "verifier" / identity / ("Counterexample.json" if identity == self.inputs[1] else "Core.json"), {})
            rows.append({"input": identity, "state": "finished", "status": status,
                         "run_directory": location, "exit_code": code, "search_seconds": 2.5})
        code = 4 if all(row["status"] in search.ACCEPTED for row in rows) else 3
        record = {"schema_version": 2, "scheduler": "GNU Parallel", "jobs": 4, "state": "finished",
                  "scheduler_exit_code": 0, "stop_reason": None, "exit_code": code, "spec": spec, "cases": rows}
        self.write(pool / "pool.json", record)
        if self.mutation:
            self.mutation(pool, record)
        return code

    def run_search(self, model=MODELS[0]):
        with patch.object(search, "command", side_effect=self.fake_pool):
            search.run_search(self.ctx, model)

    def run_all_search(self):
        for model in MODELS:
            self.run_search(model)

    def test_fixed_settings_fresh_escalation_and_real_output_discovery(self):
        before = {p.name: p.read_bytes() for p in (self.repo / "agent_houdini/experiments/paper").glob("*.json")}
        with patch.dict(os.environ, {"WHIEL_AGENT_SKILLS_FILE": "wrong", "WHIEL_AGENT_SKILLS_JSON": "wrong"}):
            self.run_all_search()
        self.assertEqual(len(self.calls), 12)
        for stage in self.ctx.manifest["search"]:
            self.assertEqual(stage["state"], "complete")
            expected = self.inputs if stage["model"] == "gpt-5.5" else self.inputs[1:] if stage["model"] == "gpt-5.6-sol" else self.inputs[2:]
            self.assertEqual(stage["inputs"], expected)
            self.assertIn("date-and-suffix-not-predicted-37", stage["pool"])
            spec = read_json(self.ctx.path(stage["spec"]))
            for key, value in {"iteration_limit": None, "consultation_limit_seconds": None,
                               "search_limit_seconds": 600, "workers": 4, "certify": "never",
                               "token_usage": "codex-rollout", "reasoning_effort": "medium",
                               "retention": "all", "agent_retention": "all", "all_inputs": False}.items():
                self.assertEqual(spec[key], value)
            self.assertEqual(spec["verifier_args"], [] if "-tools" in stage["arm"] else ["--no-tools"])
            self.assertEqual(spec["skills_dir"], search.SKILLS if stage["arm"].endswith("-skills") else None)
            for row in stage["cases"]:
                self.assertTrue(row["run_directory"].startswith("artifacts/"))
                self.assertEqual(row["search_seconds"], 2.5)
        for args, kwargs in self.calls:
            self.assertEqual(args[args.index("--jobs") + 1], "4")
            self.assertFalse({"WHIEL_AGENT_SKILLS_FILE", "WHIEL_AGENT_SKILLS_JSON"} & kwargs["env"].keys())
        after = {p.name: p.read_bytes() for p in (self.repo / "agent_houdini/experiments/paper").glob("*.json")}
        self.assertEqual(before, after)

    def test_all_accepted_skips_remaining_models(self):
        self.all_solved = True
        self.run_all_search()
        self.assertEqual(len(self.calls), 4)
        for stage in self.ctx.manifest["search"]:
            self.assertEqual(stage["state"], "complete" if stage["model"] == "gpt-5.5" else "skipped")
            if stage["state"] == "skipped":
                self.assertEqual(stage["inputs"], [])
                self.assertEqual(stage["cases"], [])

    def test_stopped_pool_is_not_unsolved_and_preserves_partial_evidence(self):
        def stop(pool, record):
            record.update(state="stopped", scheduler_exit_code=1, stop_reason="fixture infrastructure failure")
            self.write(pool / "pool.json", record)
        self.mutation = stop
        with self.assertRaises(ReproError):
            self.run_search()
        self.assertEqual(len(self.calls), 1)
        stage = self.ctx.manifest["search"][0]
        self.assertEqual(stage["state"], "failed")
        self.assertEqual(stage["cases"][0]["status"], "valid_uncertified")
        self.assertTrue(all(row["state"] == "pending" for row in self.ctx.manifest["search"][1:]))

    def test_inventory_mismatch_stops(self):
        def change(pool, record):
            record["cases"].pop()
            self.write(pool / "pool.json", record)
        self.mutation = change
        with self.assertRaisesRegex(ReproError, "inventory"):
            self.run_search()
        self.assertEqual(len(self.calls), 1)

    def test_changed_saved_settings_stop(self):
        def change(pool, record):
            record["spec"]["iteration_limit"] = 6
            self.write(pool / "pool.json", record)
        self.mutation = change
        with self.assertRaisesRegex(ReproError, "iteration_limit"):
            self.run_search()

    def test_child_status_disagreement_stops(self):
        def change(pool, record):
            path = pool / record["cases"][0]["run_directory"] / "verifier" / self.inputs[0] / "result.json"
            data = read_json(path)
            data["status"] = "resource_exhausted"
            self.write(path, data)
        self.mutation = change
        with self.assertRaisesRegex(ReproError, "disagree"):
            self.run_search()

    def test_outside_child_path_stops(self):
        def change(pool, record):
            record["cases"][0]["run_directory"] = "../outside"
            self.write(pool / "pool.json", record)
        self.mutation = change
        with self.assertRaisesRegex(ReproError, "inside"):
            self.run_search()

    def test_missing_accepted_answer_stops(self):
        def change(pool, record):
            (pool / record["cases"][0]["run_directory"] / "verifier" / self.inputs[0] / "Core.json").unlink()
        self.mutation = change
        with self.assertRaisesRegex(ReproError, "frozen answer"):
            self.run_search()

    def test_interruption_before_pool_retains_expected_inventory(self):
        with patch.object(search, "command", side_effect=Interrupted("fixture interrupted")):
            with self.assertRaises(Interrupted):
                search.run_search(self.ctx, MODELS[0])
        stage = self.ctx.manifest["search"][0]
        self.assertEqual(stage["state"], "interrupted")
        self.assertIsNone(stage["pool"])
        self.assertEqual([row["input"] for row in stage["cases"]], self.inputs)
        self.assertTrue(all(row["run_directory"] is None for row in stage["cases"]))
        self.assertEqual(read_json(self.ctx.trial / "manifest.json")["search"][0]["state"], "interrupted")

    def test_attempted_trial_cannot_be_retried(self):
        self.ctx.manifest["search"][0]["state"] = "failed"
        with patch.object(search, "command") as call, self.assertRaisesRegex(ReproError, "retried"):
            search.run_search(self.ctx, MODELS[0])
        call.assert_not_called()

    def stage(self, arm=ARMS[0], model=MODELS[0]):
        return next(stage for stage in self.ctx.manifest["search"]
                    if stage["arm"] == arm and stage["model"] == model)

    def assert_read_only_rejection(self, action):
        before = deepcopy(self.ctx.manifest)
        manifest_bytes = (self.ctx.trial / "manifest.json").read_bytes()
        with patch.object(search, "command") as call, patch.object(self.ctx, "save") as save:
            with self.assertRaises(ReproError):
                action()
        call.assert_not_called()
        save.assert_not_called()
        self.assertEqual(self.ctx.manifest, before)
        self.assertEqual((self.ctx.trial / "manifest.json").read_bytes(), manifest_bytes)

    def test_each_command_executes_only_its_requested_model(self):
        for index, model in enumerate(MODELS):
            self.run_search(model)
            self.assertEqual(len(self.calls), 4 * (index + 1))
            for args, _ in self.calls[-4:]:
                self.assertEqual(read_json(self.ctx.path(args[5]))["model"], model)
            for stage in self.ctx.manifest["search"]:
                expected = "complete" if MODELS.index(stage["model"]) <= index else "pending"
                self.assertEqual(stage["state"], expected)
        chosen = successful_search_cases(self.ctx)
        for arm in ARMS:
            self.assertEqual([(row["input"], row["model"]) for row in chosen if row["arm"] == arm],
                             [(self.inputs[0], MODELS[0]), (self.inputs[1], MODELS[1])])

    def test_no_automatic_escalation_or_skip(self):
        self.all_solved = True
        self.run_search()
        self.assertEqual(len(self.calls), 4)
        self.assertTrue(all(stage["state"] == "pending" for stage in self.ctx.manifest["search"]
                            if stage["model"] != MODELS[0]))
        self.assertEqual(search.validate_search_stage(self.ctx, MODELS[1]), {arm: [] for arm in ARMS})
        self.run_search(MODELS[1])
        self.assertEqual(len(self.calls), 4)
        self.assertTrue(all(self.stage(arm, MODELS[1])["state"] == "skipped" for arm in ARMS))
        self.assertTrue(all(self.stage(arm, MODELS[2])["state"] == "pending" for arm in ARMS))

    def test_later_model_requires_every_prior_model(self):
        for model in MODELS[1:]:
            with self.subTest(model=model):
                self.assert_read_only_rejection(lambda: search.run_search(self.ctx, model))
        self.run_search()
        self.assert_read_only_rejection(lambda: search.run_search(self.ctx, MODELS[2]))

    def test_duplicate_completed_or_terminal_stage_cannot_launch(self):
        self.run_search()
        self.assert_read_only_rejection(lambda: search.run_search(self.ctx, MODELS[0]))
        for state in ("failed", "interrupted", "running"):
            with self.subTest(state=state):
                self.stage(ARMS[-1])["state"] = state
                self.assert_read_only_rejection(lambda: search.run_search(self.ctx, MODELS[1]))
                self.stage(ARMS[-1])["state"] = "complete"
                self.stage(model=MODELS[1])["state"] = state
                self.assert_read_only_rejection(lambda: search.run_search(self.ctx, MODELS[1]))
                self.stage(model=MODELS[1])["state"] = "pending"

    def test_changed_earlier_records_reject_before_launch_without_writes(self):
        self.run_search()
        stage = self.stage()
        pool = self.ctx.path(stage["pool"])
        child = self.ctx.path(stage["cases"][0]["run_directory"])
        records = [
            (self.ctx.path(stage["spec"]), lambda value: value.update(iteration_limit=6)),
            (pool / "pool.json", lambda value: value["spec"].update(inputs=self.inputs[:1])),
            (pool / "pool.json", lambda value: value["spec"].update(output_root="artifacts/other")),
            (pool / "pool.json", lambda value: value["cases"].pop()),
            (pool / "pool.json", lambda value: value.update(state="stopped")),
            (child / "run.json", lambda value: value["spec"].update(model=MODELS[1])),
            (child / "run.json", lambda value: value["spec"].update(inputs=self.inputs)),
            (child / "verifier" / self.inputs[0] / "result.json", lambda value: value.update(status="search_timeout")),
            (child / "verifier" / self.inputs[0] / "result.json", lambda value: value.update(search_seconds=3.0)),
            (child / "verifier" / self.inputs[0] / "result.json", lambda value: value.pop("search_seconds")),
            (child / "verifier/summary.json", lambda value: value.update(interrupted=True)),
        ]
        for path, change in records:
            with self.subTest(record=path.name, change=records.index((path, change))):
                original = path.read_bytes()
                value = read_json(path)
                change(value)
                self.write(path, value)
                self.assert_read_only_rejection(lambda: search.run_search(self.ctx, MODELS[1]))
                path.write_bytes(original)
        search.validate_search_stage(self.ctx, MODELS[1])

    def test_changed_stage_inventory_subset_and_paths_reject(self):
        self.run_search()
        original = deepcopy(self.ctx.manifest["search"])
        mutations = [
            lambda stage: stage["cases"].append(deepcopy(stage["cases"][0])),
            lambda stage: stage["cases"].pop(),
            lambda stage: stage["cases"][0].update(input="Example9999"),
            lambda stage: stage["cases"][0].update(status="search_timeout"),
            lambda stage: stage.update(inputs=self.inputs[1:]),
            lambda stage: stage.update(pool=self.stage(ARMS[1])["pool"]),
            lambda stage: stage.update(spec=self.stage(ARMS[1])["spec"]),
        ]
        for index, change in enumerate(mutations):
            with self.subTest(change=index):
                change(self.stage())
                self.assert_read_only_rejection(lambda: search.run_search(self.ctx, MODELS[1]))
                self.ctx.manifest["search"] = deepcopy(original)
        self.ctx.manifest["search"].append(deepcopy(self.stage()))
        self.assert_read_only_rejection(lambda: search.run_search(self.ctx, MODELS[1]))

    def test_preexisting_later_arm_destination_rejects_before_first_pool(self):
        directory = self.ctx.trial / "search" / ARMS[-1] / MODELS[0]
        directory.mkdir(parents=True)
        self.assert_read_only_rejection(lambda: search.run_search(self.ctx, MODELS[0]))

    def test_certification_validation_requires_all_stages_and_is_read_only(self):
        self.run_search()
        self.assert_read_only_rejection(lambda: search.validate_completed_search(self.ctx))
        self.run_search(MODELS[1])
        self.assert_read_only_rejection(lambda: search.validate_completed_search(self.ctx))
        self.run_search(MODELS[2])
        before = deepcopy(self.ctx.manifest)
        with patch.object(self.ctx, "save") as save:
            self.assertEqual(search.validate_completed_search(self.ctx), {arm: self.inputs[2:] for arm in ARMS})
        save.assert_not_called()
        self.assertEqual(self.ctx.manifest, before)
        child = self.ctx.path(self.stage(model=MODELS[2])["cases"][0]["run_directory"])
        path = child / "verifier" / self.inputs[2] / "result.json"
        value = read_json(path)
        value["search_seconds"] = 99
        self.write(path, value)
        self.assert_read_only_rejection(lambda: search.validate_completed_search(self.ctx))

    def test_skipped_stages_require_complete_prior_coverage_and_no_cases(self):
        self.all_solved = True
        self.run_all_search()
        self.assertEqual(search.validate_completed_search(self.ctx), {arm: [] for arm in ARMS})
        self.stage(model=MODELS[1])["cases"] = [{"input": self.inputs[0]}]
        self.assert_read_only_rejection(lambda: search.validate_completed_search(self.ctx))
        self.stage(model=MODELS[1])["cases"] = []
        self.stage()["state"] = "skipped"
        self.assert_read_only_rejection(lambda: search.validate_completed_search(self.ctx))

    def fake_direct(self, ctx, arguments, log=None, **kwargs):
        self.calls.append((arguments, kwargs))
        stage = ctx.manifest["direct_lean"]
        if arguments[3] == "prepare":
            ctx.path(stage["bundle"]).mkdir(parents=True)
        elif arguments[3] == "run":
            output = ctx.path(stage["run"])
            self.write(output / "run.json", {
                "cases": self.inputs, "jobs": 4, "final_check_seconds": 180,
                "automatic_retries": 0, "runtime_memory_limit_bytes": None, "lean_max_heartbeats": 0,
            })
            self.write(output / "summary.json", {
                "total": 3, "finished": 3, "outcomes": {"accepted": 1, "proof_rejected": 2},
            })
        return 0

    def test_direct_lean_public_commands_and_unlimited_spec(self):
        before = self.baseline.read_bytes()
        with patch.object(search, "command", side_effect=self.fake_direct):
            search.run_direct_lean(self.ctx)
        self.assertEqual([args[3] for args, _ in self.calls], ["prepare", "run", "summarize"])
        self.assertTrue(self.calls[0][1]["cleanup_tree"])
        self.assertTrue(self.calls[1][1]["cleanup_tree"])
        launch = self.calls[1][0]
        self.assertIn("--launch", launch)
        self.assertEqual(launch[launch.index("--jobs") + 1], "4")
        self.assertEqual(self.ctx.manifest["direct_lean"]["state"], "complete")
        self.assertEqual(self.baseline.read_bytes(), before)

    def test_direct_lean_rejects_changed_budget(self):
        spec = read_json(self.baseline)
        spec["agent_seconds"] = 600
        self.write(self.baseline, spec)
        self.assert_read_only_rejection(lambda: search.run_direct_lean(self.ctx))
        self.assertEqual(self.ctx.manifest["direct_lean"]["state"], "pending")
        self.verify.assert_not_called()

    def test_direct_lean_interrupt_is_terminal(self):
        with patch.object(search, "command", side_effect=Interrupted("fixture interrupted")):
            with self.assertRaises(Interrupted):
                search.run_direct_lean(self.ctx)
        self.assertEqual(self.ctx.manifest["direct_lean"]["state"], "interrupted")
        with patch.object(search, "command") as call, self.assertRaisesRegex(ReproError, "retried"):
            search.run_direct_lean(self.ctx)
        call.assert_not_called()

    def test_direct_lean_infrastructure_summary_stops(self):
        def fail(ctx, arguments, log=None, **kwargs):
            code = self.fake_direct(ctx, arguments, log, **kwargs)
            if arguments[3] == "summarize":
                path = ctx.path(ctx.manifest["direct_lean"]["run"]) / "summary.json"
                data = read_json(path)
                data["outcomes"]["infrastructure_failure"] = 1
                self.write(path, data)
            return code
        with patch.object(search, "command", side_effect=fail), self.assertRaisesRegex(ReproError, "normally"):
            search.run_direct_lean(self.ctx)
        self.assertEqual(self.ctx.manifest["direct_lean"]["state"], "failed")


if __name__ == "__main__":
    unittest.main()
