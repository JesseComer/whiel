#!/usr/bin/env python3
"""PAPER REPRODUCTION CODE: fixed VLDB experiment orchestration, not a new verifier.

Models, budgets, arms and concurrency are intentionally fixed to the protocol in
REPRODUCIBILITY.md. Existing search/checking/certification commands do the work.
All reproduction records are below artifacts/; setup retains ordinary build caches.
"""
from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import sys

# Permit invocation from any working directory without requiring package installation.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.paper_repro_common import (  # noqa: E402
    ACCEPTED, ARMS, DEFAULT_OUTPUT, MODELS, ROOT, Context, Interrupted, ReproError,
    atomic_json, current_trial, digest, exclusive, lock_held, new_trial, now,
    output_directory, read_json, require, resolve,
)


def report(ctx, *, live=False):
    """Index retained search, baseline and certification records and counts."""
    manifest = ctx.manifest
    state = manifest["state"]
    if state == "running" and not live and not lock_held(ctx.output_root):
        state = "incomplete (stale running record; owning wrapper is no longer active)"
    lines = ["# Paper reproduction records", "", f"Execution state: {state}",
             f"Manifest: `{ctx.rel(ctx.trial / 'manifest.json')}`", "",
             "Accepted counts below come from retained search result records; they are not certifications.", ""]
    selected = {arm: set() for arm in ARMS}
    remaining = {arm: set(manifest["inputs"]) for arm in ARMS}
    missing = []
    expected_stages = {(arm, model) for arm in ARMS for model in MODELS}
    seen_stages = set()
    if state == "complete" and any(stage.get("state") not in ("complete", "skipped")
                                    for stage in manifest["search"]):
        missing.append("Execution claims completion with unfinished search stages.")
    for stage in manifest["search"]:
        arm, model = stage["arm"], stage["model"]
        if (arm, model) in seen_stages:
            missing.append(f"Duplicate search stage: {arm}/{model}")
        seen_stages.add((arm, model))
        inputs = stage.get("inputs")
        if stage["state"] == "pending":
            lines.append(f"- {arm} / {model}: pending; not started.")
            continue
        if inputs is None:
            lines.append(f"- {arm} / {model}: {stage['state']}; subset not yet selected.")
            continue
        if set(inputs) != remaining.get(arm) or len(inputs) != len(set(inputs)):
            missing.append(f"{arm}/{model}: selected subset differs from unresolved inputs.")
        if stage["state"] == "skipped" and (inputs or stage.get("cases")):
            missing.append(f"{arm}/{model}: nonempty skipped stage.")
        accepted = 0
        known = 0
        seen = set()
        for row in stage.get("cases", []):
            identity = row["input"]
            if identity in seen or identity not in inputs:
                missing.append(f"{arm}/{model}: unexpected or duplicate case {identity}")
                continue
            seen.add(identity)
            try:
                result = read_json(ctx.path(row["run_directory"]) / "verifier" / identity / "result.json")
                require(result.get("status") == row["status"], "Search result changed since stage completion.")
                known += 1
                if result["status"] in ACCEPTED:
                    require((ctx.path(row["run_directory"]) / "verifier" / identity / "Accepted.json").is_file(),
                            "Accepted result has no saved answer envelope.")
                    accepted += 1
                    selected[arm].add(identity)
                    remaining[arm].discard(identity)
            except (ReproError, OSError, KeyError) as error:
                missing.append(f"{arm}/{model}/{identity}: {error}")
        total = len(inputs)
        percentage = f" ({100 * accepted / total:.1f}%)" if total else ""
        lines.append(f"- {arm} / {model}: {stage['state']}; {accepted}/{total} accepted{percentage}; "
                     f"{known}/{total} result records read.")
        if stage.get("pool"):
            lines.append(f"  Pool report: `{stage['pool']}/progress.md`; raw records: `{stage['pool']}/pool.json`.")
        if stage["state"] == "complete" and known != total:
            missing.append(f"{arm}/{model}: incomplete case evidence")
    if seen_stages != expected_stages:
        missing.append("Expected arm/model stages are missing from the manifest.")
    total = len(manifest["inputs"])
    lines += ["", "Cumulative search coverage (each input counted once per arm):"]
    for arm in ARMS:
        count = len(selected[arm])
        lines.append(f"- {arm}: {count}/{total} ({100 * count / total:.1f}%).")
    baseline = manifest["direct_lean"]
    lines += ["", f"Direct Lean: {baseline['state']}."]
    if state == "complete" and (baseline["state"] != "complete" or not baseline.get("run")):
        missing.append("Execution claims completion without a completed Direct Lean run.")
    if baseline.get("run"):
        lines.append(f"Existing summary: `{baseline['run']}/summary.json`; case data: `{baseline['run']}/cases/`.")
        try:
            from scripts.paper_repro_audit import audit_run
            summary = read_json(ctx.path(baseline["run"]) / "summary.json")
            checked = summary["proof_checked"]
            lines.append(f"Direct Lean proof_checked: {checked}/{total} ({100 * checked / total:.1f}%).")
            if baseline["state"] == "complete" and (summary.get("total") != total or summary.get("finished") != total):
                missing.append("Direct Lean completion disagrees with its summary.")
            audit = audit_run(ctx.path(baseline["run"]))
            audit_path = ctx.trial / "direct-lean-audit.json"
            atomic_json(audit_path, audit)
            lines.append("Receipt audit counts: " + ", ".join(f"{name}={count}" for name, count in audit["counts"].items()) + ".")
            lines.append(f"Per-case axiom classifications and issues: `{ctx.rel(audit_path)}`.")
            if not audit["complete"]:
                lines.append("Receipt audit coverage is incomplete: inspect the listed cases. A finished attempt that submitted no proof can have no checker receipt; this is distinct from execution completeness.")
        except (ReproError, OSError, ValueError, KeyError) as error:
            missing.append(f"Direct Lean audit: {error}")
    certification = manifest["certification"]
    outcomes = Counter()
    observed_pairs = []
    if state == "complete" and certification["state"] != "complete":
        missing.append("Execution claims completion with unfinished certification.")
    for attempt in certification.get("attempts", []):
        observed_pairs.append((attempt["arm"], attempt["input"]))
        try:
            receipt = read_json(ctx.path(attempt["directory"]) / "supervisor.json")
            require(receipt.get("input") == attempt["input"] and receipt.get("arm") == attempt["arm"],
                    "Certification receipt identity mismatch.")
            outcomes[receipt["outcome"]] += 1
        except (ReproError, OSError, KeyError) as error:
            missing.append(f"Certification {attempt['arm']}/{attempt['input']}: {error}")
    expected_pairs = certification.get("expected_pairs")
    if len(set(observed_pairs)) != len(observed_pairs):
        missing.append("Duplicate certification attempts appear in the manifest.")
    if certification["state"] == "complete":
        expected = {(arm, identity) for arm, ids in selected.items() for identity in ids}
        recorded = {(row["arm"], row["input"]) for row in expected_pairs or []}
        if expected_pairs is None or recorded != expected or set(observed_pairs) != expected or sum(outcomes.values()) != len(expected):
            missing.append("Certification completion does not cover exactly the accepted search answers.")
        if any(attempt.get("state") != "complete" for attempt in certification.get("attempts", [])):
            missing.append("Certification contains unfinished attempts.")
        from scripts.paper_repro_certify import NORMAL_OUTCOMES
        if set(outcomes) - NORMAL_OUTCOMES:
            missing.append("Certification contains an unexpected outcome.")
    lines += ["", f"Certification: {certification['state']}; "
              f"{sum(outcomes.values())}/{len(expected_pairs) if expected_pairs is not None else '?'} receipts.",
              "Outcomes: " + (", ".join(f"{name}={count}" for name, count in sorted(outcomes.items())) or "none") + ".",
              f"Raw measurements: `{ctx.rel(ctx.trial)}/certification/<arm>/<input>/supervisor.json`."]
    if missing:
        lines += ["", "Incomplete or inconsistent evidence:"] + ["- " + item for item in missing]
    lines += ["", "Use the per-run progress, verifier consultation history, token-usage, and checker records for analysis.",
              "Missing measurements are not zero.", ""]
    text = "\n".join(lines)
    (ctx.trial / "report.md").write_text(text)
    print(text)
    return 0 if state in ("ready", "complete") and not missing else 1


def check_source_identity(ctx):
    identities = ctx.manifest.get("source_sha256")
    require(isinstance(identities, dict) and identities, "Trial lacks recorded input/settings identities.")
    for path, expected in identities.items():
        require(digest(ctx.path(path)) == expected,
                f"Recorded source changed since this trial began: {path}.")


def completed_trial(ctx):
    return (all(stage["state"] in ("complete", "skipped") for stage in ctx.manifest["search"])
            and ctx.manifest["direct_lean"]["state"] == "complete"
            and ctx.manifest["certification"]["state"] == "complete")


def execute(ctx, phase, model=None, fresh=False):
    """Run exactly one explicitly selected experiment/model stage."""
    from scripts.paper_repro_certify import cpu_lanes, run_certification
    from scripts.paper_repro_search import (CLI_VERSIONS, run_direct_lean, run_search,
                                           validate_completed_search, validate_direct_lean, validate_search_stage)
    from scripts.paper_repro_setup import verify_cli

    require(phase in ("search", "direct-lean", "certify"), "Unknown experiment phase.")
    require(phase != "search" or model in MODELS, "Select one of the three paper search models.")
    can_start = phase == "direct-lean" or (phase == "search" and model == MODELS[0])
    require(not fresh or can_start, "Only GPT-5.5 search or Direct Lean can start a new trial.")
    setup_record = read_json(ctx.output_root / "setup.json")
    require(setup_record.get("state") == "complete", "Run setup before starting experiments.")
    pointer = ctx.output_root / "current.json"
    if pointer.exists() and not fresh:
        ctx = current_trial(ctx.repo, ctx.output_root)
    else:
        require(can_start, "Start GPT-5.5 search before escalating or certifying.")
        new_trial(ctx)
    # Precondition errors leave the selected trial and all completed stage states intact.
    require(ctx.manifest.get("state") in ("prepared", "ready", "complete"),
            "Trial is running, failed or interrupted. Inspect report; stages are never resumed or retried.")
    check_source_identity(ctx)
    lanes = None
    if phase == "search":
        validate_search_stage(ctx, model)
    elif phase == "direct-lean":
        validate_direct_lean(ctx)
    else:
        require(ctx.manifest["certification"]["state"] == "pending", "Certification was already attempted.")
        validate_completed_search(ctx)
        lanes = cpu_lanes()
    if phase in ("search", "direct-lean"):
        # Certification requires no provider CLI or credentials.
        version = CLI_VERSIONS[model] if phase == "search" else "0.148.0"
        verify_cli(ctx, version)
        from agent_houdini.lean_baseline_utils import worker_homes
        worker_homes(ctx.auth_root.resolve(), 4)
        label = model if phase == "search" else "GPT-5.5 Direct Lean (unlimited agent time)"
        print(f"WARNING: starting paid model calls for {label}.", flush=True)
    active = {"phase": phase, "model": model, "started_at": now()}
    ctx.manifest.update(state="running", active_command=active)
    ctx.manifest.setdefault("phase_commands", []).append(active)
    ctx.save()
    try:
        if phase == "search":
            run_search(ctx, model)
        elif phase == "direct-lean":
            run_direct_lean(ctx)
        else:
            run_certification(ctx, lanes)
        active["state"] = "complete"
        ctx.manifest["state"] = "complete" if completed_trial(ctx) else "ready"
        return 0
    except BaseException as error:
        active.update(state="interrupted" if isinstance(error, (Interrupted, KeyboardInterrupt)) else "failed",
                      detail=str(error))
        ctx.manifest.update(state=active["state"], detail=str(error))
        raise
    finally:
        active["finished_at"] = now()
        ctx.manifest["active_command"] = None
        ctx.save()
        try:
            report(ctx, live=True)
        except Exception as error:
            ctx.manifest["report_error"] = str(error)
            ctx.save()
            print("Partial-report error; raw records are retained:", error, file=sys.stderr)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-root", default=DEFAULT_OUTPUT,
                        help="repository-relative artifact subdirectory (default: %(default)s)")
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("setup", help="install project tools and run original watched builds; no model calls")
    commands.add_parser("login", help="perform four independent native provider logins")
    search = commands.add_parser("search", help="PAID model calls for one search model across the four configurations")
    search.add_argument("model", choices=MODELS, help="explicit model stage; escalate only after the preceding stage finishes")
    search.add_argument("--new", action="store_true", help="GPT-5.5 only: start a fresh trial, preserving older records")
    baseline = commands.add_parser("direct-lean", help="PAID GPT-5.5 baseline with unlimited agent time")
    baseline.add_argument("--new", action="store_true", help="start a fresh trial, preserving older records")
    commands.add_parser("certify", help="certify this trial's accepted Whiel answers; no model calls or login")
    commands.add_parser("report", help="show accepted counts, percentages and paths to existing raw reports; no model calls")
    internal = commands.add_parser("_certify-one", help="internal helper used by certify; not a standalone experiment")
    internal.add_argument("job")
    args = parser.parse_args(argv)
    try:
        root = output_directory(ROOT, args.output_root)
        if args.command == "_certify-one":
            from scripts.paper_repro_certify import run_one
            return run_one(ROOT, resolve(ROOT, args.job))
        if args.command == "report":
            return report(current_trial(ROOT, root))
        ctx = Context(ROOT, root)
        with exclusive(root):
            if args.command == "setup":
                from scripts.paper_repro_setup import setup
                setup(ctx)
            elif args.command == "login":
                from scripts.paper_repro_setup import login
                login(ctx)
            elif args.command in ("search", "direct-lean", "certify"):
                return execute(ctx, args.command, getattr(args, "model", None), getattr(args, "new", False))
        return 0
    except (Interrupted, KeyboardInterrupt) as error:
        print(f"Reproduction interrupted: {error}", file=sys.stderr)
        return 130
    except (ReproError, OSError, ValueError, KeyError) as error:
        print(f"Reproduction stopped: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
