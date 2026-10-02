# Author: Fangzhu Shen
"""Experiment specs, run directories and the digest read from both record trees."""

import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from agent_houdini import experiment
from agent_houdini.experiment import (
    SpecError, agent_turn, allocate_run_directory, build_command, load_spec, parse_prompt,
    resolve_spec, run, run_directory_name, write_report,
)


SPEC = {"model": "model-a", "provider": "codex", "reasoning_effort": "medium",
        "isolation": "bwrap", "inputs": ["Example0001"], "search_limit_seconds": 90,
        "certification_limit_seconds": 120, "iteration_limit": 2, "name": "smoke"}


def frame(ordinal, record):
    return json.dumps({"version": 3, "ordinal": ordinal, "previous_digest": None,
                       "payload": list(json.dumps(record).encode())})


def write_verifier(root, identity="Example0001", status="valid", search_seconds=12.5):
    """A minimal B tree: settings, result, ledger and the final projection."""
    (root / "campaign-settings.json").write_text(json.dumps({
        "schema_version": 2, "inputs": [identity],
        "controls": {"search_limit_seconds": 90.0, "certification_limit_seconds": 120.0,
                     "iteration_limit": 2, "workers": 1},
        "proposer": {"arguments": ["--provider", "codex", "--model", "model-a",
                                   "--isolation", "bwrap"], "executable": "/python"}}))
    (root / "summary.json").write_text(json.dumps({"all_certified": status == "valid",
                                                   "interrupted": False, "unrun_inputs": []}))
    example = root / identity
    example.mkdir()
    (example / "Certificate").mkdir()
    (example / "Certificate" / "Valid.lean").write_text("theorem valid : True := trivial\n")
    run_dir = example / "artifacts" / "run-0000"
    (run_dir / "required").mkdir(parents=True)
    history = {"kind": "whiel_framework_ii_attempt_history", "iteration": 2, "failure": None,
               "ledger": [
                   {"row": "attempt", "clause": 0, "level": 0, "role": "initialization",
                    "invalidated": False, "outcome": {"kind": "proved"}},
                   {"row": "attempt", "clause": 0, "level": 0, "role": "maintenance",
                    "invalidated": False, "outcome": {"kind": "proved"}},
                   {"row": "attempt", "clause": 1, "level": 1, "role": "maintenance",
                    "invalidated": False, "outcome": {"kind": "inconclusive", "reason": "solver_unknown"}},
                   {"row": "attempt", "clause": 2, "level": 0, "role": "initialization",
                    "invalidated": False, "outcome": {"kind": "refuted", "attempt": 7}},
                   {"row": "invalidation", "target": 0, "reason": "snapshot_changed"}]}
    projection = {"kind": "event", "event": {"kind": "final_owner_projection", "projection": {
        "state": {"committed": [[0, 0]], "pending": [[1, 1]], "dead": [{"clause": 2, "cause": "refuted"}],
                  "catalog": {"records": [
                      {"id": 0, "canonical_source": "(op_zT = ∅[2])", "display": "(T = ∅[2])", "protected": False},
                      {"id": 1, "canonical_source": "(op_zT ⊆ yp_zT)", "display": "(T ⊆ T∞)", "protected": False},
                      {"id": 2, "canonical_source": "(op_zE = ∅[2])", "display": "(E = ∅[2])", "protected": False}]},
                  "terminations": [{"ordinal": 1, "result": {"kind": "applied", "outcome": {
                      "kind": "inconclusive", "reason": "solver_unknown"}}},
                                   {"ordinal": 2, "result": {"kind": "applied", "outcome": {"kind": "proved"}}}]}}}}
    payloads = [("runtime_trace", ["root", "attempt-history"], json.dumps(history)),
                ("witness", ["root", "entailment-attempt:7"], "model bytes"),
                ("runtime_trace", ["root", "consultation-records"], frame(0, {"kind": "header"})),
                ("runtime_trace", ["root", "consultation-records"], frame(1, projection)),
                ("runtime_trace", ["root", "consultation-records"], frame(2, {"kind": "closed"}))]
    manifest = {"format_version": 2, "artifacts": []}
    for index, (kind, scope, text) in enumerate(payloads):
        path = f"required/artifact-{index:020d}.bin"
        (run_dir / path).write_text(text)
        manifest["artifacts"].append({"id": index, "kind": kind, "scope": scope,
                                      "relative_path": path, "byte_len": len(text), "retained": True})
    (run_dir / "manifest.json").write_text(json.dumps(manifest))
    result = {"input": identity, "status": status, "schema_version": 2,
              "attempt_history": {"artifact_id": 0}}
    if search_seconds is not None:
        result["search_seconds"] = search_seconds
    (example / "result.json").write_text(json.dumps(result))
    return example


def _rendered(entries, kind):
    lines = []
    for entry in entries:
        clause = entry["clause"]
        identifier = clause["clause_id"]
        if kind == "core":
            words = f"level {entry['level']}  origin submitted"
        elif kind == "pending":
            words = (f"minimum level {entry['minimum_level']}  current level {entry['current_level']}"
                     "  origin submitted  drop_reference: yes")
        else:
            outcome = entry["outcome"]
            words = outcome["kind"]
            if outcome.get("level") is not None:
                words += f" at level {outcome['level']}"
            if outcome.get("cause"):
                words += f", cause {outcome['cause']}"
            words += "  origin submitted"
        lines.append(f"    clause {identifier}  {words}")
        lines.append(f"        {clause['canonical_source']}")
        if clause.get("display") and clause["display"] != clause["canonical_source"]:
            lines.append(f"        displayed: {clause['display']}")
    return "\n".join(lines)


def prompt_text(identity, consultation, core, pending, last_round, latest, *, old_format=False):
    """A prompt in the current shape, or (old_format) one that dumps the observation."""
    head = (f"# Your role\n\nexplanation\n\n# Task {identity} — consultation {consultation}\n\n"
            f"# Current Core ({len(core)} clauses)\n\n{_rendered(core, 'core')}\n\n"
            f"# Pending clauses ({len(pending)})\n\n{_rendered(pending, 'pending')}\n\n"
            f"# Last round ({len(last_round)} clauses)\n\n{_rendered(last_round, 'last')}\n\n"
            f"# Latest result\n\n    {latest['kind']} — words\n\n"
            "==========\nRESPONSE ENVELOPE\n==========\n\n")
    if not old_format:
        return head + "RESPONSE EXAMPLE:\n{\"kind\":\"candidate_clauses\",\"binding\":{}}\n\n" \
            "==========\nIDENTITIES AND DROP REFERENCES\n==========\n\n    none\n"
    observation = {"schema_version": 15, "operation": "proposer_observation", "correction": None,
                   "feedback": {"iteration": consultation, "core": core, "pending": pending,
                                "last_round": last_round, "latest": latest,
                                "presentation": {"task": {"canonical_id": identity}}}}
    return head + "==\nCOMPLETE CONTROLLER PUSH\n==\n\nThe observation.\n\n" \
        + json.dumps(observation, ensure_ascii=False) + "\n"


def clause(identifier, source, display, **extra):
    return {"clause": {"clause_id": identifier, "record_digest": "r", "formula_digest": "f",
                       "canonical_source": source, "display": display}, "source": "submitted", **extra}


def write_agent(root, identity="Example0001", *, layout="new"):
    """A minimal C tree with two retained consultations."""
    if layout == "new":
        input_dir = root / identity
    else:
        input_dir = root / "whiel-agent-abc" / "input-xyz"
    input_dir.mkdir(parents=True)
    (root / "launcher.jsonl").write_text("")
    events = [
        {"kind": "endpoint_configuration", "fields": {"selection": {"provider": "codex", "model": "model-a",
                                                                    "reasoning_effort": "medium"},
                                                      "isolation": "bwrap", "retention": "all"}},
        {"kind": "request_started", "fields": {"request_id": 1, "prompt_bytes": 10}},
        {"kind": "input_identified", "fields": {"request_id": 1, "canonical_id": identity,
                                                "directory": identity if layout == "new" else None}},
        {"kind": "request_outcome", "fields": {"request_id": 1, "outcome": "response",
                                               "diagnostic_code": None, "directory": "request-1"}},
        {"kind": "request_started", "fields": {"request_id": 2, "prompt_bytes": 12}},
        {"kind": "request_outcome", "fields": {"request_id": 2, "outcome": "no_response",
                                               "diagnostic_code": "agent_native_deadline",
                                               "directory": "request-2"}},
        {"kind": "agent_traffic", "fields": {"bytes": 100, "messages": 4}},
    ]
    (input_dir / "events.jsonl").write_text("".join(
        json.dumps({"schema_version": 1, "sequence": index, **event}) + "\n"
        for index, event in enumerate(events)))
    first = input_dir / "request-1"
    first.mkdir()
    (first / "prompt.txt").write_text(prompt_text(identity, 1, [], [], [], {"kind": "initial"}))
    (first / "native-stdout.jsonl").write_text("".join(json.dumps(line) + "\n" for line in [
        {"type": "thread.started"},
        {"type": "item.completed", "item": {"type": "agent_message", "text": "I will try the definitional clause."}},
        {"type": "item.completed", "item": {"type": "mcp_tool_call", "tool": "validate_clauses",
                                            "arguments": {"clauses": ["(op_zT = ∅[2])"]}, "status": "completed"}},
        {"type": "item.completed", "item": {"type": "mcp_tool_call", "tool": "submit",
                                            "arguments": {"payload": "..."}, "status": "completed"}}]))
    (first / "mcp.jsonl").write_text("".join(json.dumps(line) + "\n" for line in [
        {"exchange": 1, "direction": "request", "method": "initialize", "tool": None, "bytes": 10, "time": 1.0},
        {"exchange": 1, "direction": "reply", "method": "initialize", "tool": None, "bytes": 10, "time": 1.5},
        {"exchange": 2, "direction": "request", "method": "tools/call", "tool": "validate_clauses",
         "bytes": 50, "time": 2.0},
        {"exchange": 2, "direction": "reply", "method": "tools/call", "tool": "validate_clauses",
         "bytes": 70, "error": None, "time": 3.0},
        {"exchange": 3, "direction": "request", "method": "tools/call", "tool": "submit", "bytes": 90, "time": 4.0},
        {"exchange": 3, "direction": "reply", "method": "tools/call", "tool": "submit", "bytes": 30,
         "error": None, "time": 5.0}]))
    (first / "submissions.jsonl").write_text(json.dumps({
        "submission": 1, "exchange": 3, "time": 5.0, "payload_bytes": 90, "accepted": True,
        "verdict": "receipt", "detail": None,
        "payload": json.dumps({"kind": "candidate_clauses", "binding": {}, "dropped": [],
                               "clauses": ["(op_zT = ∅[2])", "(op_zT ⊆ yp_zT)", "(op_zE = ∅[2])"]})}) + "\n")
    second = input_dir / "request-2"
    second.mkdir()
    core = [clause(0, "(op_zT = ∅[2])", "(T = ∅[2])", level=0)]
    pending = [clause(1, "(op_zT ⊆ yp_zT)", "(T ⊆ T∞)", minimum_level=1, current_level=1)]
    last = [clause(0, "(op_zT = ∅[2])", "(T = ∅[2])", outcome={"kind": "committed", "level": 0}),
            clause(1, "(op_zT ⊆ yp_zT)", "(T ⊆ T∞)", outcome={"kind": "pending", "level": 1}),
            clause(2, "(op_zE = ∅[2])", "(E = ∅[2])", outcome={"kind": "dead", "cause": "refuted"})]
    (second / "prompt.txt").write_text(prompt_text(identity, 2, core, pending, last,
                                                   {"kind": "postcondition_open"}))
    (second / "native-stdout.jsonl").write_text(json.dumps({
        "type": "assistant", "message": {"content": [
            {"type": "text", "text": "Thinking about the exit facts."},
            {"type": "tool_use", "name": "mcp__whiel__countermodel", "input": {"attempt": 7}}]}}) + "\n")
    (second / "mcp.jsonl").write_text(json.dumps({
        "exchange": 1, "direction": "request", "method": "tools/call", "tool": "countermodel",
        "bytes": 40, "time": 6.0}) + "\n" + json.dumps({
        "exchange": 1, "direction": "reply", "method": "tools/call", "tool": "countermodel", "bytes": 120,
        "error": None, "time": 7.0,
        "text": json.dumps({"result": {"content": [{"type": "text", "text": json.dumps(
            {"tool": "countermodel", "result": {"relations": [{"name": "o:p::E", "rows": [["num:1", "num:2"]]}]}})}]}})}) + "\n")
    (second / "submissions.jsonl").write_text("")
    return input_dir


class SpecTests(unittest.TestCase):
    def test_spec_defaults_paths_and_refusals(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            path = root / "spec.json"
            path.write_text(json.dumps({**SPEC, "repo": name, "provider_cli": "bin/codex"}))
            resolved = resolve_spec(load_spec(path))
            self.assertEqual(resolved["repo"], str(root.resolve()))
            self.assertEqual(resolved["provider_cli"], str((root / "bin/codex").resolve()))
            self.assertEqual(resolved["verifier"], str((root / "whiel_runner/target/release/whiel-symbolic").resolve()))
            self.assertEqual(resolved["output_root"], str((root / "artifacts/runs").resolve()))
            self.assertEqual(resolved["retention"], "all")
            self.assertEqual(resolved["certify"], "inline")
            self.assertEqual(resolved["agent_retention"], "all")
            self.assertEqual(resolved["iteration_limit"], 2)
            for broken, message in (({**SPEC, "iteration_limt": 2}, "unknown spec keys"),
                                    ({**SPEC, "model": None}, "model must be"),
                                    ({**SPEC, "inputs": [], "all_inputs": False}, "inputs list"),
                                    ({**SPEC, "all_inputs": True}, "inputs list"),
                                    ({**SPEC, "provider": "other"}, "codex or claude"),
                                    ({**SPEC, "isolation": "docker"}, "local or bwrap"),
                                    ({**SPEC, "search_limit_seconds": -1}, "positive"),
                                    ({**SPEC, "retention": "none"}, "retention must be"),
                                    ({**SPEC, "certify": "sometimes"}, "certify must be")):
                path.write_text(json.dumps(broken))
                with self.assertRaisesRegex(SpecError, message):
                    resolve_spec(load_spec(path))
            path.write_text("[]")
            with self.assertRaisesRegex(SpecError, "JSON object"):
                load_spec(path)

    def test_omitted_or_null_iteration_limit_emits_no_count_guard(self):
        base = {key: value for key, value in SPEC.items() if key != "iteration_limit"}
        for spec in (base, {**base, "iteration_limit": None}):
            with self.subTest(spec=spec):
                resolved = resolve_spec(spec)
                self.assertIsNone(resolved["iteration_limit"])
                argv = build_command(resolved, Path("/runs/unbounded"))[0]
                self.assertNotIn("--iteration-limit", argv)
                self.assertEqual(argv[argv.index("--search-limit") + 1], "90")

    def test_shipped_model_specs_have_no_iteration_cap(self):
        specs = Path(__file__).resolve().parents[1] / "experiments"
        for name in ("full-benchmark", "sample-5", "subset-template", "weak-model-smoke"):
            with self.subTest(name=name):
                spec = load_spec(specs / f"{name}.json")
                spec["model"] = spec.get("model") or "test-model"
                resolved = resolve_spec(spec)
                self.assertIsNone(resolved["iteration_limit"])
                argv = build_command(resolved, Path("/runs/unbounded"))[0]
                self.assertNotIn("--iteration-limit", argv)
                self.assertEqual(argv[argv.index("--search-limit") + 1], "600")

    def test_replay_command_starts_the_replay_proposer_and_takes_a_transcript(self):
        replay_spec = {"proposer": "replay", "repo": "/checkout", "inputs": ["Example0001"]}
        resolved = resolve_spec(replay_spec)
        argv = build_command(resolved, Path("/runs/replay-20260920"))[0]
        self.assertEqual(argv[0], "/checkout/whiel_runner/target/release/whiel-symbolic")
        self.assertEqual(argv[argv.index("--proposer-executable") + 1], sys.executable)
        arguments = argv[argv.index("--proposer-arg") + 1::2]
        self.assertTrue(str(arguments[0]).endswith("replay_proposer.py"))
        self.assertNotIn("--transcript", argv)
        # `transcript` names a retained run to replay consultation by
        # consultation instead of the repository's single recorded answer;
        # it is forwarded to the replay proposer the same way `--repo` is.
        with_transcript = resolve_spec({**replay_spec, "transcript": "artifacts/runs/old-run"})
        argv = build_command(with_transcript, Path("/runs/replay-20260920"))[0]
        self.assertIn("--transcript", argv)
        self.assertEqual(argv[argv.index("--transcript") + 2], "/checkout/artifacts/runs/old-run")
        with self.assertRaisesRegex(SpecError, "needs proposer: replay"):
            resolve_spec({**SPEC, "repo": "/checkout", "transcript": "artifacts/runs/old-run"})
        # `answers` names another directory of recorded answers, such as the
        # ones an earlier run accepted; it and `transcript` exclude each other.
        with_answers = resolve_spec({**replay_spec, "answers": "artifacts/runs/old-run"})
        argv = build_command(with_answers, Path("/runs/replay-20260920"))[0]
        self.assertEqual(argv[argv.index("--answers") + 2], "/checkout/artifacts/runs/old-run")
        with self.assertRaisesRegex(SpecError, "not both"):
            resolve_spec({**replay_spec, "answers": "a", "transcript": "b"})
        with self.assertRaisesRegex(SpecError, "needs proposer: replay"):
            resolve_spec({**SPEC, "repo": "/checkout", "answers": "artifacts/runs/old-run"})

    def test_run_directory_name_and_collision_suffix(self):
        import datetime
        resolved = resolve_spec({**SPEC, "model": "gpt/5.5 sol", "name": "cert 3600"})
        self.assertEqual(run_directory_name(resolved, datetime.date(2026, 9, 17)),
                         "gpt-5.5-sol-20260917-cert-3600")
        with tempfile.TemporaryDirectory() as name:
            first = allocate_run_directory(name, "m-20260917")
            second = allocate_run_directory(name, "m-20260917")
            self.assertEqual((first.name, second.name), ("m-20260917", "m-20260917-2"))

    def test_command_places_both_trees_in_the_run_directory(self):
        resolved = resolve_spec({**SPEC, "repo": "/checkout", "provider_cli": "bin/codex",
                                 "skills_file": "skills.json", "verifier_args": ["--workers", "2"],
                                 "agent_args": ["--agent-messages", "5"], "agent_thinking_tokens": 4000})
        argv, environment, cwd = build_command(resolved, Path("/runs/m-20260917-smoke"))
        self.assertEqual(argv[:5], [sys.executable, "-m", "agent_houdini", "campaign", "run"])
        delimiter = argv.index("--")
        before, after = argv[5:delimiter], argv[delimiter + 1:]
        self.assertEqual(before, [
            "--verifier", "/checkout/whiel_runner/target/release/whiel-symbolic", "--provider", "codex",
            "--model", "model-a", "--reasoning-effort", "medium", "--provider-cli", "/checkout/bin/codex",
            "--isolation", "bwrap", "--agent-log-dir", "/runs/m-20260917-smoke/agent",
            "--agent-retention", "all", "--agent-thinking-tokens", "4000", "--agent-messages", "5"])
        self.assertEqual(after, [
            "--repo", "/checkout", "--input", "Example0001",
            "--destination", "/runs/m-20260917-smoke/verifier", "--retention", "all",
            "--certify", "inline",
            "--search-limit", "90", "--certification-limit", "120", "--iteration-limit", "2",
            "--workers", "2"])
        # A large campaign asks for `deferred`: the searches finish, the run
        # directory holds every record, and one certification phase follows.
        deferred = resolve_spec({**SPEC, "repo": "/checkout", "certify": "deferred"})
        deferred_argv = build_command(deferred, Path("/runs/m"))[0]
        self.assertEqual(deferred_argv[deferred_argv.index("--certify") + 1], "deferred")
        self.assertEqual(environment, {"WHIEL_AGENT_SKILLS_FILE": "/checkout/skills.json"})
        self.assertEqual(cwd, str(experiment.PACKAGE_ROOT))
        library = resolve_spec({**SPEC, "repo": "/checkout", "skills_dir": "agent_houdini/skills/v1"})
        self.assertEqual(build_command(library, Path("/r"))[1],
                         {"WHIEL_AGENT_SKILLS_FILE": "/checkout/agent_houdini/skills/v1"})
        with self.assertRaisesRegex(SpecError, "not both"):
            resolve_spec({**SPEC, "skills_dir": "a", "skills_file": "b"})
        every = resolve_spec({**SPEC, "inputs": None, "all_inputs": True})
        self.assertIn("--all", build_command(every, Path("/r"))[0])

    def test_dry_run_creates_nothing(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "spec.json"
            path.write_text(json.dumps({**SPEC, "repo": name}))
            out = io.StringIO()
            self.assertEqual(run(path, dry_run=True, out=out), 0)
            self.assertIn("--agent-log-dir", out.getvalue())
            self.assertFalse((Path(name) / "artifacts").exists())


class ReadingTests(unittest.TestCase):
    def test_prompt_parse_reads_header_counts_entries_and_latest(self):
        core = [clause(0, "(op_zT = ∅[2])", "(T = ∅[2])", level=0)]
        last = [clause(2, "(op_zE = ∅[2])", "(E = ∅[2])", outcome={"kind": "dead", "cause": "refuted"})]
        found = parse_prompt(prompt_text("Example0042", 3, core, [], last, {"kind": "postcondition_open"}))
        self.assertEqual((found["task"], found["consultation"]), ("Example0042", 3))
        self.assertEqual((found["core"], found["pending"], found["last_round"]), (1, 0, 1))
        self.assertTrue(found["latest"].startswith("postcondition_open"))
        self.assertFalse(found["correction"])
        self.assertEqual(found["core_entries"][0]["id"], 0)
        self.assertEqual(found["core_entries"][0]["text"], "(T = ∅[2])")
        self.assertEqual(found["last_round_entries"][0]["outcome"], "dead, cause refuted")
        self.assertIsNone(found["observation"])
        # A prompt recorded before the identity tail still parses, from its JSON too.
        older = parse_prompt(prompt_text("Example0042", 3, core, [], last, {"kind": "postcondition_open"},
                                         old_format=True))
        self.assertEqual(older["observation"]["feedback"]["iteration"], 3)
        self.assertEqual(older["core_entries"][0]["text"], "(T = ∅[2])")
        self.assertEqual(parse_prompt("no push here")["observation"], None)

    def test_agent_turn_reads_codex_and_claude_streams(self):
        messages, calls = agent_turn([
            {"type": "item.completed", "item": {"type": "agent_message", "text": "hello"}},
            {"type": "item.completed", "item": {"type": "mcp_tool_call", "tool": "ledger",
                                                "arguments": {}, "status": "completed", "error": None}},
            {"type": "assistant", "message": {"content": [
                {"type": "text", "text": "claude words"},
                {"type": "tool_use", "name": "mcp__whiel__submit", "input": {"payload": "x"}}]}},
            {"type": "unparsed"}])
        self.assertEqual(messages, ["hello", "claude words"])
        self.assertEqual([call["tool"] for call in calls], ["ledger", "submit"])


class ReportTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="c-experiment-")
        self.addCleanup(self.temporary.cleanup)
        # The harness reports resolved paths, and a temporary directory can
        # sit behind a symbolic link.
        self.root = Path(self.temporary.name).resolve()

    def _rendered_run(self, name, **verifier):
        """One rendered run directory, for reading its digest back."""
        run_dir = self.root / name
        (run_dir / "verifier").mkdir(parents=True)
        (run_dir / "agent").mkdir()
        write_verifier(run_dir / "verifier", **verifier)
        write_agent(run_dir / "agent")
        (run_dir / "run.json").write_text(json.dumps({
            "spec": SPEC, "status": "finished", "exit_code": 0,
            "started_at": "2026-09-17T10:00:00", "finished_at": "2026-09-17T10:30:00"}))
        write_report(run_dir)
        return run_dir

    def test_the_verifiers_search_time_is_the_only_time_the_digest_reports(self):
        """The reported search time comes from result.json, and it is alone.

        The harness could time an input from when it first prompted to when
        the result file appeared, but that span measures the machine and the
        certification too, and beside the real figure it would be read as a
        rival measure of the same thing. So no such figure is rendered
        anywhere, and a run directory that predates the verifier's own
        measurement shows the search column absent rather than filled in.
        """
        run_dir = self._rendered_run("measured-20260917", search_seconds=12.5)
        text = (run_dir / "progress.md").read_text()
        self.assertIn("| search | detail |", text)
        self.assertIn("| 12 s |  |", text)
        self.assertNotIn("wall", text)
        self.assertIn("excludes runner and Lean worker startup and all certification", text)
        rows = json.loads((run_dir / "progress.json").read_text())["inputs"]
        self.assertEqual(rows[0]["search_seconds"], 12.5)
        self.assertNotIn("wall_seconds", rows[0])
        rounds = json.loads(
            (run_dir / "examples" / "Example0001" / "rounds.json").read_text())
        self.assertNotIn("wall_seconds", rounds)
        # The per-consultation split survives: it is the only model-versus-
        # verifier division an experiment records. What it is not is stated
        # in the file itself, beside the figures.
        for round_row in rounds["rounds"]:
            self.assertIn("agent_seconds", round_row)
            self.assertIn("verifier_seconds", round_row)
        self.assertIsNone(rounds["rounds"][-1]["verifier_seconds"])
        self.assertIn("Neither is search time", rounds["round_seconds_meaning"])
        summary = (run_dir / "examples" / "Example0001" / "summary.md").read_text()
        self.assertIn("search time (verifier-measured, excludes certification): 12 s", summary)
        self.assertNotIn("wall time", summary)
        self.assertIn("agent side", summary)
        self.assertIn("(harness estimate, not search time)", summary)

        absent = self._rendered_run("unmeasured-20260917", search_seconds=None)
        rows = json.loads((absent / "progress.json").read_text())["inputs"]
        self.assertIsNone(rows[0]["search_seconds"])
        summary = (absent / "examples" / "Example0001" / "summary.md").read_text()
        self.assertNotIn("search time (verifier-measured", summary)
        self.assertNotIn("wall time", summary)

    def test_digest_from_both_trees_in_the_new_layout(self):
        run_dir = self.root / "model-a-20260917-smoke"
        (run_dir / "verifier").mkdir(parents=True)
        (run_dir / "agent").mkdir()
        write_verifier(run_dir / "verifier")
        write_agent(run_dir / "agent")
        (run_dir / "run.json").write_text(json.dumps({
            "spec": {**SPEC, "notes": "a note"}, "status": "finished", "exit_code": 0,
            "started_at": "2026-09-17T10:00:00", "finished_at": "2026-09-17T10:30:00",
            "git_revision": "abc123"}))
        progress = write_report(run_dir)
        self.assertEqual(progress, run_dir / "progress.md")
        text = progress.read_text()
        self.assertIn("model: `model-a` (codex, effort medium, isolation bwrap)", text)
        self.assertIn("limits: search 90.0 s, certification 120.0 s, iterations 2, workers 1", text)
        self.assertIn("revision: `abc123`", text)
        self.assertIn("notes: a note", text)
        self.assertIn("| [Example0001](examples/Example0001/summary.md) | valid | 2 | 3 | 0 | 1 | 1 | 1 |", text)
        # The search column is the verifier's own measurement from
        # result.json, and it is the only time figure the digest carries.
        self.assertIn("| search | detail |", text)
        self.assertIn("| 12 s |  |", text)
        self.assertIn("excludes runner and Lean worker startup and all certification", text)
        progress_json = json.loads((run_dir / "progress.json").read_text())
        self.assertEqual(progress_json["inputs"][0]["search_seconds"], 12.5)
        self.assertNotIn("wall_seconds", progress_json["inputs"][0])
        summary = (run_dir / "examples" / "Example0001" / "summary.md").read_text()
        self.assertIn("search time (verifier-measured, excludes certification): 12 s", summary)
        self.assertNotIn("wall time", summary)
        self.assertIn("# Example0001 — valid", summary)
        self.assertIn("certificate: `../../verifier/Example0001/Certificate/Valid.lean`", summary)
        self.assertIn("verifier consultations: 2", summary)
        self.assertIn("### Request 1 — consultation 1", summary)
        self.assertIn("outcome: response;", summary)
        self.assertIn("> I will try the definitional clause.", summary)
        self.assertIn("tool calls: `validate_clauses`, `submit`", summary)
        self.assertIn("submission 1: 3 clauses, verifier reply: receipt", summary)
        self.assertIn("    (op_zT ⊆ yp_zT)", summary)
        self.assertIn("### Request 2 — consultation 2", summary)
        self.assertIn("outcome: no_response [agent_native_deadline]", summary)
        self.assertIn("push: Core 1, pending 1, last round 3, latest: postcondition_open — words", summary)
        self.assertIn("- clause 2: dead, cause refuted — `(E = ∅[2])`", summary)
        self.assertIn("> Thinking about the exit facts.", summary)
        self.assertIn("| 0 | `(T = ∅[2])` | Core, level 0 | L0 init proved; L0 main proved |", summary)
        self.assertIn("| 1 | `(T ⊆ T∞)` | pending, last level 1 | L1 main inconclusive(solver_unknown) |", summary)
        self.assertIn("| 2 | `(E = ∅[2])` | dead, cause=refuted | L0 init refuted |", summary)
        self.assertIn("- check 1: inconclusive (solver_unknown)", summary)
        self.assertIn("- check 2: proved", summary)
        self.assertIn("clause 2 refuted at level 0 (initialization), attempt 7; verifier artifacts: "
                      "witness `required/artifact-00000000000000000001.bin`", summary)
        self.assertIn("the agent fetched `countermodel` (120 bytes reply): {\"tool\": \"countermodel\"", summary)
        example = run_dir / "examples" / "Example0001"
        self.assertEqual(os.readlink(example / "verifier"), "../../verifier/Example0001")
        self.assertEqual(os.readlink(example / "agent"), "../../agent/Example0001")
        self.assertTrue((example / "agent" / "request-1" / "prompt.txt").is_file())
        recorded = json.loads((run_dir / "progress.json").read_text())
        self.assertEqual(recorded["inputs"][0]["clauses_submitted"], 3)
        self.assertEqual(recorded["all_certified"], True)
        # A second report replaces the digest and keeps the links.
        write_report(run_dir)
        self.assertEqual(os.readlink(example / "agent"), "../../agent/Example0001")

    def test_running_campaign_and_unstarted_inputs_are_reported_as_such(self):
        run_dir = self.root / "run"
        (run_dir / "verifier").mkdir(parents=True)
        (run_dir / "agent").mkdir()
        (run_dir / "verifier" / "campaign-settings.json").write_text(json.dumps({
            "inputs": ["Example0001", "Example0002"], "controls": {}}))
        write_agent(run_dir / "agent")
        (run_dir / "run.json").write_text(json.dumps({"spec": SPEC, "status": "running"}))
        text = write_report(run_dir).read_text()
        self.assertIn("verifier summary: not written yet", text)
        self.assertIn("| [Example0001](examples/Example0001/summary.md) | running | 2 | 3 | 0 | 1* | 1 | ? |", text)
        self.assertIn("| [Example0002](examples/Example0002/summary.md) | not started | 0 | 0 | 0 | ? | ? | ? |", text)
        summary = (run_dir / "examples" / "Example0001" / "summary.md").read_text()
        self.assertIn("# Example0001 — running", summary)
        self.assertIn("No verifier ledger was published", summary)

    def test_old_layout_campaign_directory_becomes_a_linked_run_directory(self):
        artifacts = self.root / "artifacts"
        campaign = artifacts / "campaigns" / "20260916-old"
        logs = artifacts / "agent-logs" / "20260916-old"
        campaign.mkdir(parents=True)
        logs.mkdir(parents=True)
        write_verifier(campaign)
        write_agent(logs, layout="old")
        progress = write_report(campaign)
        target = artifacts / "runs" / "20260916-old"
        self.assertEqual(progress, target / "progress.md")
        self.assertEqual(Path(os.readlink(target / "verifier")), Path("../../campaigns/20260916-old"))
        self.assertEqual(Path(os.readlink(target / "agent")), Path("../../agent-logs/20260916-old"))
        text = progress.read_text()
        self.assertIn("model: `model-a` (codex, effort default, isolation bwrap)", text)
        self.assertIn("| [Example0001](examples/Example0001/summary.md) | valid | 2 | 3 | 0 | 1 | 1 | 1 |", text)
        summary = (target / "examples" / "Example0001" / "summary.md").read_text()
        self.assertIn("### Request 1 — consultation 1", summary)
        link = target / "examples" / "Example0001" / "agent"
        self.assertTrue(link.is_symlink())
        self.assertTrue((link / "request-2" / "prompt.txt").is_file())
        # The agent-log directory is accepted as the argument too.
        self.assertEqual(write_report(logs), progress)
        with self.assertRaisesRegex(SpecError, "neither a run directory"):
            write_report(self.root)

    def test_run_records_the_command_streams_the_output_and_reports(self):
        spec_path = self.root / "spec.json"
        spec_path.write_text(json.dumps({**SPEC, "repo": str(self.root)}))
        script = self.root / "fake_launcher.py"
        script.write_text(
            "import json, os, sys\n"
            "run = sys.argv[1]\n"
            "os.makedirs(os.path.join(run, 'verifier', 'Example0001'))\n"
            "open(os.path.join(run, 'verifier', 'campaign-settings.json'), 'w').write("
            "json.dumps({'inputs': ['Example0001'], 'controls': {}}))\n"
            "open(os.path.join(run, 'verifier', 'Example0001', 'result.json'), 'w').write("
            "json.dumps({'status': 'search_timeout', 'detail': 'no proof'}))\n"
            "print('verifier output: ' + run)\n"
            "sys.exit(3)\n")

        def fake_command(resolved, run_dir):
            return [sys.executable, str(script), str(run_dir)], {"WHIEL_AGENT_SKILLS_FILE": "x"}, str(self.root)

        out = io.StringIO()
        with patch.object(experiment, "build_command", fake_command):
            status = run(spec_path, out=out)
        self.assertEqual(status, 3)
        run_dir = next((self.root / "artifacts" / "runs").iterdir())
        self.assertTrue(run_dir.name.startswith("model-a-"))
        self.assertTrue(run_dir.name.endswith("-smoke"))
        record = json.loads((run_dir / "run.json").read_text())
        self.assertEqual((record["status"], record["exit_code"]), ("finished", 3))
        # Every path the record carries is repo-relative: the script and the
        # run directory both sit under `self.root` (the spec's own `repo`),
        # and the interpreter, which does not, is reduced to its file name.
        # Nothing here is an absolute path, a home directory or a host name.
        self.assertEqual(record["command"][0], Path(sys.executable).name)
        self.assertEqual(record["command"][1], "fake_launcher.py")
        self.assertEqual(record["command"][2], "artifacts/runs/" + run_dir.name)
        self.assertEqual(record["spec_file"], "spec.json")
        self.assertEqual(record["run_directory"], "artifacts/runs/" + run_dir.name)
        self.assertEqual(record["cwd"], ".")
        self.assertEqual(record["python"], Path(sys.executable).name)
        self.assertEqual(record["environment"], {"WHIEL_AGENT_SKILLS_FILE": "x"})
        self.assertNotIn("hostname", record)
        self.assertIn("verifier output: " + str(run_dir), (run_dir / "launcher.log").read_text())
        self.assertIn("verifier output: " + str(run_dir), out.getvalue())
        progress = (run_dir / "progress.md").read_text()
        self.assertIn("| [Example0001](examples/Example0001/summary.md) | search_timeout | 0 | 0 | 0 "
                      "| ? | ? | ? | ? | no proof |", progress)
        self.assertIn("exit code 3", progress)


if __name__ == "__main__":
    unittest.main()
