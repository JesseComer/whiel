"""PAPER REPRODUCTION CODE: fixed search escalation and Direct Lean orchestration.

This additive wrapper calls the existing public runners. It never resumes,
retries, certifies, or changes verifier/provider acceptance decisions.
"""
from __future__ import annotations

from copy import deepcopy
import math
import os
from pathlib import Path
import sys

from scripts.paper_repro_common import (
    ACCEPTED, ARMS, MODELS, Interrupted, ReproError, atomic_json, command,
    now, read_json, require,
)
from scripts.paper_repro_setup import cli_path, verify_cli

# PAPER REPRODUCTION CODE: the reported scientific settings, not CLI defaults.
SEARCH_SECONDS = 600
VERIFIER_WORKERS = 4
POOL_JOBS = 4
DIRECT_LEAN_JOBS = 4
CLI_VERSIONS = {"gpt-5.5": "0.148.0", "gpt-5.6-sol": "0.148.0", "gpt-6-astra": "0.154.0"}
SKILLS = "agent_houdini/skills/v1"


def _environment():
    environment = dict(os.environ)
    for key in ("WHIEL_AGENT_SKILLS_FILE", "WHIEL_AGENT_SKILLS_JSON"):
        environment.pop(key, None)
    return environment


def _spec(ctx, arm, model, inputs, output):
    spec = read_json(ctx.repo / "agent_houdini/experiments/paper" / f"{arm}.json")
    spec.update(
        name=f"paper-{arm}-{model}",
        notes="PAPER REPRODUCTION CODE: one fresh attempt per input and model.",
        proposer="agent", provider="codex", model=model, reasoning_effort="medium",
        provider_cli=ctx.rel(cli_path(ctx, CLI_VERSIONS[model])),
        isolation="bwrap", repo=".",
        verifier="whiel_runner/target/release/whiel-symbolic",
        all_inputs=False, inputs=list(inputs), output_root=ctx.rel(output),
        search_limit_seconds=SEARCH_SECONDS, consultation_limit_seconds=None,
        iteration_limit=None, workers=VERIFIER_WORKERS, retention="all",
        agent_retention="all", token_usage="codex-rollout", certify="never",
        skills_file=None, skills_dir=SKILLS if arm.endswith("-skills") else None,
        verifier_args=[] if "-tools" in arm else ["--no-tools"],
        agent_args=[], agent_thinking_tokens=None, transcript=None, answers=None,
    )
    return spec


# These fields must survive unchanged in the public runner's saved specs.
_SPEC_FIELDS = (
    "proposer", "provider", "model", "reasoning_effort", "isolation", "provider_cli",
    "verifier", "search_limit_seconds", "consultation_limit_seconds", "iteration_limit",
    "workers", "retention", "agent_retention", "token_usage", "certify",
    "skills_file", "skills_dir", "verifier_args", "agent_args", "agent_thinking_tokens",
    "repo", "transcript", "answers", "certification_limit_seconds",
)


def _check_spec(actual, expected):
    require(isinstance(actual, dict), "Missing saved experiment settings.")
    for key in _SPEC_FIELDS:
        require(actual.get(key) == expected.get(key), f"Saved experiment setting differs: {key}.")


def _inspect_pool(ctx, stage, spec, output, *, complete, save=True):
    """Record validated child paths; a stopped pool can retain partial evidence."""
    candidates = sorted(output.glob("*/pool.json")) if output.is_dir() else []
    require(len(candidates) == 1, "Expected exactly one pool record in this stage's fresh output root.")
    pool = candidates[0].parent
    require(pool.resolve().parent == output.resolve(), "Pool directory escaped its output root.")
    stage["pool"] = ctx.rel(pool)
    record = read_json(pool / "pool.json")
    require(record.get("schema_version") == 2 and record.get("scheduler") == "GNU Parallel"
            and record.get("jobs") == POOL_JOBS, "Unexpected pool protocol or concurrency.")
    _check_spec(record.get("spec"), spec)
    require(record["spec"].get("inputs") == stage["inputs"]
            and record["spec"].get("all_inputs") is False
            and record["spec"].get("output_root") == ctx.rel(output),
            "Pool saved selection or output root differs from the planned stage.")
    _check_case_inventory(stage)
    rows = record.get("cases")
    require(isinstance(rows, list) and all(isinstance(row, dict) for row in rows), "Invalid pool cases.")
    identities = [row.get("input") for row in rows]
    require(all(isinstance(identity, str) for identity in identities)
            and len(identities) == len(stage["inputs"]) and len(set(identities)) == len(identities)
            and set(identities) == set(stage["inputs"]), "Pool input inventory differs from the planned stage.")
    indexed = {row["input"]: row for row in stage["cases"]}
    for row in rows:
        identity = row["input"]
        location = row.get("run_directory")
        if location is None:
            require(not complete and row.get("status") not in ACCEPTED, "Finished case lacks a child run.")
            indexed[identity].update(status=row.get("status") or row.get("state", "unknown"))
            continue
        require(isinstance(location, str), "Invalid child-run path.")
        relative = Path(location)
        require(not relative.is_absolute() and len(relative.parts) == 3
                and relative.parts[:2] == ("cases", identity) and ".." not in relative.parts
                and relative.as_posix() == location,
                "Child run must be inside its own pool case directory.")
        child = ctx.path(ctx.rel(pool / relative))
        require(child.parent == pool.resolve() / "cases" / identity, "Child run escaped its case directory.")
        run = read_json(child / "run.json")
        _check_spec(run.get("spec"), spec)
        require(run["spec"].get("inputs") == [identity] and run["spec"].get("all_inputs") is False
                and run["spec"].get("output_root") == ctx.rel(pool / "cases" / identity),
                "Child run is not the selected single-input campaign.")
        result = read_json(child / "verifier" / identity / "result.json")
        summary = read_json(child / "verifier" / "summary.json")
        require(result.get("input") == identity and result.get("status") == row.get("status"),
                "Pool and authoritative child result disagree.")
        require(summary.get("selected_inputs") == [identity], "Child summary input identity differs.")
        status = result.get("status")
        if status in ACCEPTED:
            case = child / "verifier" / identity
            answer = "Core.json" if status == "valid_uncertified" else "Counterexample.json"
            require((case / "Accepted.json").is_file() and (case / answer).is_file(),
                    "Accepted child is missing its frozen answer.")
        saved = {"input": identity, "status": status, "run_directory": ctx.rel(child)}
        if result.get("search_seconds") is not None:
            seconds = result["search_seconds"]
            require(type(seconds) in (int, float) and math.isfinite(seconds) and seconds >= 0,
                    "Invalid recorded search duration.")
            saved["search_seconds"] = seconds
        indexed[identity].pop("search_seconds", None)
        indexed[identity].update(saved)
        if complete:
            require(row.get("state") == "finished" and not row.get("stop_reason"), "Pool child did not finish normally.")
            require(not summary.get("resource_failure") and summary.get("interrupted") is False
                    and not summary.get("unrun_inputs"), "Child campaign stopped before normal completion.")
            require(status in ACCEPTED or status == "search_timeout",
                    "Unexpected child outcome; infrastructure failures are not unsolved tasks.")
            expected_code = 4 if status in ACCEPTED else 3
            require(row.get("exit_code") == expected_code and run.get("exit_code") == expected_code
                    and run.get("status") == "finished", "Child exit records disagree with its outcome.")
    if complete:
        require(record.get("state") == "finished" and record.get("scheduler_exit_code") == 0
                and not record.get("stop_reason"), "Pool did not finish normally; escalation stopped.")
        expected_code = 4 if all(row["status"] in ACCEPTED for row in stage["cases"]) else 3
        require(record.get("exit_code") == expected_code, "Pool exit record disagrees with its cases.")
    if save:
        ctx.save()


def _check_case_inventory(stage):
    rows = stage.get("cases")
    require(isinstance(rows, list) and all(isinstance(row, dict) for row in rows),
            "Invalid stage case inventory.")
    require([row.get("input") for row in rows] == stage["inputs"],
            "Stage case inventory differs from its selected inputs.")


def _stage_directory(ctx, arm, model):
    directory = ctx.trial / "search" / arm / model
    expected = f"{ctx.rel(ctx.trial)}/search/{arm}/{model}"
    require(ctx.rel(directory) == expected
            and ctx.rel(directory / "spec.json") == expected + "/spec.json"
            and ctx.rel(directory / "pools") == expected + "/pools",
            "Search stage destination is not canonical.")
    return directory


def _validate_search(ctx, completed_models):
    """Re-read authoritative records without changing any retained evidence."""
    require(ctx.trial is not None and ctx.manifest is not None, "Select a trial before search.")
    stages = ctx.manifest.get("search")
    require(isinstance(stages, list) and all(isinstance(stage, dict) for stage in stages),
            "Unexpected paper stage inventory.")
    require([(stage.get("arm"), stage.get("model")) for stage in stages]
            == [(arm, model) for arm in ARMS for model in MODELS], "Unexpected paper stage inventory.")
    inputs = ctx.manifest.get("inputs")
    require(isinstance(inputs, list) and bool(inputs)
            and all(isinstance(identity, str) for identity in inputs)
            and len(set(inputs)) == len(inputs), "Invalid trial input inventory.")
    for stage in stages:
        index = MODELS.index(stage["model"])
        if index < completed_models:
            require(stage.get("state") in ("complete", "skipped"),
                    "Earlier search stages must complete before escalation or certification.")
        else:
            require(stage.get("state") == "pending", "Search attempts cannot be resumed or retried.")
            require(stage.get("cases") == []
                    and stage.get("inputs") in (None, inputs if index == 0 else None)
                    and not any(key in stage for key in ("spec", "pool", "started_at", "finished_at")),
                    "Pending search stage already contains attempt evidence.")
    remaining_by_arm = {}
    for arm in ARMS:
        remaining = list(inputs)
        for model in MODELS[:completed_models]:
            stage = next(row for row in stages if row["arm"] == arm and row["model"] == model)
            require(stage.get("inputs") == remaining, "Saved search subset differs from earlier outcomes.")
            _check_case_inventory(stage)
            directory = _stage_directory(ctx, arm, model)
            if stage["state"] == "skipped":
                require(not remaining and stage["cases"] == []
                        and not any(key in stage for key in ("spec", "pool", "started_at"))
                        and not directory.exists(), "Skipped stage is not an empty, fully covered subset.")
                continue
            require(bool(remaining), "An empty search subset must be explicitly skipped.")
            require(stage.get("spec") == ctx.rel(directory / "spec.json"), "Noncanonical search spec path.")
            spec = _spec(ctx, arm, model, remaining, directory / "pools")
            require(read_json(directory / "spec.json") == spec, "Saved stage spec differs from its planned settings.")
            checked = deepcopy(stage)
            _inspect_pool(ctx, checked, spec, directory / "pools", complete=True, save=False)
            require(checked["pool"] == stage.get("pool"), "Saved pool path differs from the stage's pool.")
            require(checked["cases"] == stage["cases"], "Saved stage cases disagree with authoritative child results.")
            remaining = [row["input"] for row in checked["cases"] if row["status"] not in ACCEPTED]
        remaining_by_arm[arm] = remaining
    return remaining_by_arm


def validate_search_stage(ctx, model):
    """Check prerequisites for one explicit model command, without writes."""
    require(model in MODELS, "Unknown paper search model.")
    remaining = _validate_search(ctx, MODELS.index(model))
    for arm in ARMS:
        require(not _stage_directory(ctx, arm, model).exists(), "Search stage destination already exists.")
    return remaining


def validate_completed_search(ctx):
    """Guard certification against incomplete, changed, or misselected searches."""
    return _validate_search(ctx, len(MODELS))


def run_search(ctx, model):
    remaining_by_arm = validate_search_stage(ctx, model)
    stages = ctx.manifest["search"]
    for arm in ARMS:
        remaining = remaining_by_arm[arm]
        stage = next(row for row in stages if row["arm"] == arm and row["model"] == model)
        stage["inputs"] = list(remaining)
        stage["cases"] = [{"input": identity, "status": "pending", "run_directory": None}
                          for identity in remaining]
        if not remaining:
            stage.update(state="skipped", finished_at=now())
            ctx.save()
            continue
        directory = _stage_directory(ctx, arm, model)
        output = directory / "pools"
        stage.update(state="running", started_at=now(), spec=ctx.rel(directory / "spec.json"), pool=None)
        ctx.save()
        spec = None
        try:
            require(not directory.exists(), "Search stage destination already exists.")
            spec = _spec(ctx, arm, model, remaining, output)
            atomic_json(directory / "spec.json", spec)
            verify_cli(ctx, CLI_VERSIONS[model])
            code = command(ctx, [sys.executable, "-m", "agent_houdini", "experiment", "pool",
                                 stage["spec"], "--jobs", str(POOL_JOBS),
                                 "--auth-root", ctx.rel(ctx.auth_root)],
                           directory / "pool.log", env=_environment(), allowed=(3, 4))
            _inspect_pool(ctx, stage, spec, output, complete=True)
            require(code == read_json(ctx.path(stage["pool"]) / "pool.json")["exit_code"],
                    "Pool process and record exit codes disagree.")
            stage.update(state="complete", finished_at=now())
            ctx.save()
        except BaseException as error:
            stage.update(state="interrupted" if isinstance(error, (Interrupted, KeyboardInterrupt)) else "failed",
                         finished_at=now(), error=str(error))
            if spec is not None:
                try:
                    _inspect_pool(ctx, stage, spec, output, complete=False)
                except (ReproError, OSError, ValueError, TypeError) as evidence_error:
                    stage["record_error"] = str(evidence_error)
            ctx.save()
            raise


def validate_direct_lean(ctx):
    """Check deterministic baseline prerequisites without changing the trial."""
    require(ctx.trial is not None and ctx.manifest is not None, "Select a trial before Direct Lean.")
    stage = ctx.manifest["direct_lean"]
    require(stage.get("state") == "pending", "Direct Lean attempts cannot be resumed or retried.")
    directory = ctx.trial / "direct-lean"
    require(not directory.is_symlink()
            and ctx.rel(directory) == f"{ctx.rel(ctx.trial)}/direct-lean",
            "Direct Lean destination is not canonical.")
    require(not directory.exists(), "Direct Lean destination already exists.")
    spec = read_json(ctx.repo / "agent_houdini/experiments/full-benchmark-lean-agent.json")
    require(spec.get("model") == "gpt-5.5" and spec.get("reasoning_effort") == "medium"
            and "agent_seconds" in spec and spec["agent_seconds"] is None,
            "Direct Lean spec no longer matches the paper protocol.")
    require(spec.get("provider_cli") == ctx.rel(cli_path(ctx, "0.148.0")), "Unexpected Direct Lean CLI path.")


def run_direct_lean(ctx):
    validate_direct_lean(ctx)
    stage = ctx.manifest["direct_lean"]
    directory = ctx.trial / "direct-lean"
    bundle, output = directory / "bundle", directory / "run"
    stage.update(state="running", started_at=now(), bundle=ctx.rel(bundle), run=ctx.rel(output))
    ctx.save()
    try:
        spec_path = "agent_houdini/experiments/full-benchmark-lean-agent.json"
        verify_cli(ctx, "0.148.0")
        checker = "whiel_runner/direct_lean/target/debug/whiel-direct-lean"
        command(ctx, [sys.executable, "-m", "agent_houdini.lean_baseline", "prepare",
                      "--checker", checker, "--bundle", stage["bundle"]], directory / "prepare.log", cleanup_tree=True)
        command(ctx, [sys.executable, "-m", "agent_houdini.lean_baseline", "run", spec_path,
                      "--checker", checker, "--bundle", stage["bundle"],
                      "--auth-root", ctx.rel(ctx.auth_root), "--jobs", str(DIRECT_LEAN_JOBS),
                      "--out", stage["run"], "--launch"], directory / "run.log", env=_environment(), cleanup_tree=True)
        command(ctx, [sys.executable, "-m", "agent_houdini.lean_baseline", "summarize",
                      stage["run"]], directory / "summarize.log")
        run, summary = read_json(output / "run.json"), read_json(output / "summary.json")
        require(run.get("cases") == ctx.manifest["inputs"] and run.get("jobs") == DIRECT_LEAN_JOBS,
                "Direct Lean input inventory or concurrency differs.")
        require(run.get("final_check_seconds") == 180 and run.get("automatic_retries") == 0
                and run.get("runtime_memory_limit_bytes") is None and run.get("lean_max_heartbeats") == 0,
                "Direct Lean runtime controls differ.")
        require(summary.get("total") == len(stage["inputs"]) and summary.get("finished") == len(stage["inputs"])
                and not summary.get("outcomes", {}).get("infrastructure_failure"),
                "Direct Lean did not complete every case normally.")
        stage.update(state="complete", finished_at=now(), summary=ctx.rel(output / "summary.json"))
        ctx.save()
    except BaseException as error:
        stage.update(state="interrupted" if isinstance(error, (Interrupted, KeyboardInterrupt)) else "failed",
                     finished_at=now(), error=str(error))
        ctx.save()
        raise
