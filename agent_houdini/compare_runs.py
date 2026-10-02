# Author: Fangzhu Shen
"""Compare an original campaign against a replay of it: three named checks.

`python3 -m agent_houdini compare-runs ORIGINAL REPLAY` reads two record
trees -- each a harness run directory (has `verifier/`), a bare
`campaign run --destination` tree, or, for ORIGINAL only, a single frozen
transcript file (`export-transcript`'s own output) -- and reports three
fidelity checks by name, each PASS or FAIL with the specific differences
listed:

    1st replay fidelity check   every input present in both runs has the
                                 same verdict class (accepted valid /
                                 accepted invalid / not accepted)
    2nd replay fidelity check   for every input accepted valid in both, the
                                 same Core (clause set and levels); for every
                                 input accepted invalid in both, the same
                                 counterexample instance
    3rd replay fidelity check   the same set of (clause, check kind, level,
                                 outcome) entries in the two attempt ledgers,
                                 ignoring order, timing, attempt numbering
                                 and duplicates; an entry inconclusive on
                                 either side is excluded from this decision
                                 and reported separately as a timing
                                 difference

The command exits 0 only if all three pass. `--require-all` turns an input
present in only one run into a failure instead of a reported, ignored gap.
`--expect-different ID[,ID...]` names inputs whose differences are still
reported but do not fail a check -- for a verifier change already known to
affect specific inputs. `--json PATH` additionally writes a machine-readable
report.

This reads two already-finished record trees; it starts no campaign, no
proposer and no solver.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from .experiment import read_verifier_input


TRANSCRIPT_KIND = "whiel_transcript_replay"
CHECK_1_NAME = "1st replay fidelity check"
CHECK_2_NAME = "2nd replay fidelity check"
CHECK_3_NAME = "3rd replay fidelity check"
INCONCLUSIVE_OUTCOME = "inconclusive"


class CompareError(ValueError):
    """A record tree or transcript file cannot be read as one to compare."""


# --------------------------------------------------------------------------
# Reading one side into one common shape, whichever kind it is


def verdict_class(status):
    """`accepted_valid`, `accepted_invalid` or `not_accepted`, from a
    `result.json` `status` word.

    Only `valid`/`valid_uncertified` and `invalid`/`invalid_uncertified`
    count as accepted (see `docs/analysts-guide.md` §1); every other status
    -- `search_timeout`, `incomplete`, `resource_exhausted`, a certification
    failure, anything else -- is "not accepted". This is deliberately coarse:
    a replay's own non-acceptance need not end the same way the original's
    did (a transcript replay that runs out ends `incomplete` at once rather
    than `search_timeout`; see `agent_houdini/tests/replay_proposer.py`'s own
    docstring), so the checks compare the class, never the exact word.
    """
    if status in ("valid", "valid_uncertified"):
        return "accepted_valid"
    if status in ("invalid", "invalid_uncertified"):
        return "accepted_invalid"
    return "not_accepted"


def _core_dict(rows):
    """`{clause text: level}` from a `Core.json`-shaped `rows` list."""
    core = {}
    for row in rows or []:
        if isinstance(row, dict) and isinstance(row.get("source"), str):
            core[row["source"]] = row.get("level")
    return core


def _counterexample_dict(instance):
    """`{relation name: frozenset of row tuples}` from a counterexample
    `instance` (see `docs/analysts-guide.md` §3): row order and duplicate
    rows are not part of the instance's identity.
    """
    found = {}
    for relation in (instance or {}).get("relations") or []:
        if isinstance(relation, dict) and isinstance(relation.get("name"), str):
            rows = relation.get("rows") if isinstance(relation.get("rows"), list) else []
            found[relation["name"]] = frozenset(
                tuple(row) for row in rows if isinstance(row, list))
    return found


def catalog_canonical_texts(state):
    """id -> canonical clause text (never the shorter `display` spelling),
    from a run's own final state's catalog.

    `experiment.py`'s own `catalog_texts` prefers `display` -- right for a
    human-readable digest, wrong here: `Core.json` and a submitted
    `candidate_clauses` proposal are both written in canonical text, so
    comparing a ledger entry against either (a Core row, in
    `check_accepted_records`, or a transcript's own recorded submissions, in
    `export_transcript.py`) needs the same canonical form throughout, not a
    mix of two spellings that happen to agree only for a clause with no
    separate display form.
    """
    texts = {}
    catalog = state.get("catalog") if isinstance(state, dict) else None
    for record in (catalog.get("records") if isinstance(catalog, dict) else None) or []:
        if isinstance(record, dict) and isinstance(record.get("id"), int):
            text = record.get("canonical_source") or record.get("display")
            if isinstance(text, str):
                texts[record["id"]] = text
    return texts


def completed_rounds(attempt_history):
    """How many of this input's consultations the verifier actually
    finished -- accepted a submission or a decline and issued the next
    request -- rather than merely started.

    `attempt_history`'s own `consultations` list carries one entry per
    consultation with its own `outcome`; `accepted` is the only outcome that
    means the round ran (a `cancelled` entry is the one the search's own
    deadline caught mid-flight, always last). Read identically from a live
    run's `attempt_history` (`_read_verifier_tree`) or a frozen transcript's
    own recorded `expected.completed_rounds` (`export_transcript.py` writes
    it with this same function), so both sides of a comparison use one
    definition; see docs/analysts-guide.md, "Checking a replay against its
    transcript".
    """
    consultations = (attempt_history or {}).get("consultations")
    return sum(1 for item in consultations or []
              if isinstance(item, dict) and item.get("outcome") == "accepted")


def ledger_entries(ledger_rows, texts):
    """`[(clause text, check kind, level, outcome), ...]` from a run's own
    attempt-ledger rows (`attempt_history`'s `ledger`, see
    `docs/analysts-guide.md` §1 and §2): one entry per clause-check attempt,
    read at the clause's own canonical text rather than the run-local
    integer id a ledger row names it by, since that id means nothing in a
    different run's catalog. `texts` is `catalog_canonical_texts`'s id ->
    text map, read from the same run's own final state. A clause missing
    from that map (should not happen for a retained run) falls back to a
    `#<id>` label rather than being silently dropped, so it still shows up
    as a difference instead of vanishing from both sides unevenly.
    """
    entries = []
    for row in ledger_rows or []:
        if not isinstance(row, dict) or row.get("row") != "attempt":
            continue
        identifier = row.get("clause")
        if not isinstance(identifier, int):
            continue
        text = texts.get(identifier) or f"#{identifier}"
        outcome = row.get("outcome") if isinstance(row.get("outcome"), dict) else {}
        entries.append((text, row.get("role"), row.get("level"), outcome.get("kind")))
    return entries


def _expected_record(status, core_rows, counterexample_instance, ledger, rounds_completed):
    verdict = verdict_class(status)
    return {
        "status": status, "verdict_class": verdict,
        "core": _core_dict(core_rows) if verdict == "accepted_valid" and core_rows else None,
        "counterexample": (_counterexample_dict(counterexample_instance)
                           if verdict == "accepted_invalid" and counterexample_instance else None),
        "ledger": list(ledger), "completed_rounds": rounds_completed,
    }


def _verifier_root(path):
    """The directory holding `<ID>/result.json` entries directly: `path`
    itself for a bare `campaign run --destination`, or its `verifier/`
    subdirectory for a harness `experiment run` directory.
    """
    path = Path(path)
    verifier = path / "verifier"
    if verifier.is_dir():
        return verifier
    return path


def _read_verifier_tree(root):
    """Every input under a verifier destination, read the way the digest
    (`experiment.py`) already reads them, reduced to the comparison shape.
    """
    root = Path(root)
    inputs = {}
    for directory in sorted(root.iterdir()):
        if not directory.is_dir() or not (directory / "result.json").is_file():
            continue
        verifier = read_verifier_input(directory)
        result = verifier.get("result") or {}
        status = result.get("status")
        if status is None:
            continue
        core_rows = None
        core_path = directory / "Core.json"
        if core_path.is_file():
            try:
                core_rows = json.loads(core_path.read_text(encoding="utf-8")).get("rows")
            except (OSError, ValueError):
                core_rows = None
        counterexample_instance = None
        if isinstance(verifier.get("counterexample"), dict):
            counterexample_instance = verifier["counterexample"].get("instance")
        texts = catalog_canonical_texts(verifier.get("final_state") or {})
        history = verifier.get("attempt_history") or {}
        ledger = ledger_entries(history.get("ledger"), texts)
        inputs[directory.name] = _expected_record(status, core_rows, counterexample_instance, ledger,
                                                   completed_rounds(history))
    return inputs


def _read_transcript_json(path):
    try:
        document = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise CompareError(f"cannot read {path}: {error}") from error
    if not isinstance(document, dict) or document.get("kind") != TRANSCRIPT_KIND:
        raise CompareError(f"{path} is not a {TRANSCRIPT_KIND} file")
    inputs = {}
    for identity, record in (document.get("inputs") or {}).items():
        expected = record.get("expected") if isinstance(record, dict) else None
        if not isinstance(expected, dict):
            continue
        ledger = [tuple(entry) for entry in expected.get("ledger") or []]
        core = expected.get("core")
        counterexample = expected.get("counterexample")
        inputs[identity] = {
            "status": expected.get("status"), "verdict_class": expected.get("verdict_class"),
            "core": {row["source"]: row.get("level") for row in core
                     if isinstance(row, dict) and isinstance(row.get("source"), str)} if core else None,
            "counterexample": _counterexample_dict(counterexample) if counterexample else None,
            "ledger": ledger, "completed_rounds": expected.get("completed_rounds") or 0,
        }
    return inputs, document


def read_side(path):
    """One side's `{input id: comparison record}`, and a short label for it.

    `path` is a frozen transcript file (detected by extension, then
    content), a harness run directory or a bare verifier destination; the
    caller does not need to know which.
    """
    path = Path(path)
    if path.is_file():
        inputs, _document = _read_transcript_json(path)
        return inputs, f"{path} (transcript)"
    if not path.is_dir():
        raise CompareError(f"{path} is neither a file nor a directory")
    root = _verifier_root(path)
    if not root.is_dir():
        raise CompareError(f"{path} has no verifier records to compare (looked in {root})")
    return _read_verifier_tree(root), str(path)


# --------------------------------------------------------------------------
# The three checks


def _parse_ids(text):
    return {item.strip() for item in (text or "").split(",") if item.strip()}


def _common_and_only(original, replay):
    common = sorted(set(original) & set(replay))
    only_original = sorted(set(original) - set(replay))
    only_replay = sorted(set(replay) - set(original))
    return common, only_original, only_replay


def _no_completed_round(original, common):
    """Inputs, among those present on both sides, whose ORIGINAL side never
    finished a single consultation -- the search's own limit expired before
    a catalog even existed to check anything against (see
    `docs/analysts-guide.md`). There is nothing for any of the three checks
    to compare for such an input: it is reported as its own category, never
    as a difference, and never fails.
    """
    return sorted(identity for identity in common if original[identity].get("completed_rounds") == 0)


def check_verdicts(original, replay, *, expect_different, require_all):
    common, only_original, only_replay = _common_and_only(original, replay)
    no_completed_round = _no_completed_round(original, common)
    comparable = [identity for identity in common if identity not in no_completed_round]
    differences = []
    for identity in comparable:
        left, right = original[identity], replay[identity]
        if left["verdict_class"] != right["verdict_class"]:
            differences.append({
                "input": identity, "expected_different": identity in expect_different,
                "original": {"status": left["status"], "verdict_class": left["verdict_class"]},
                "replay": {"status": right["status"], "verdict_class": right["verdict_class"]}})
    failing = [item for item in differences if not item["expected_different"]]
    passed = not failing and (not require_all or (not only_original and not only_replay))
    return {"name": CHECK_1_NAME, "passed": passed, "differences": differences,
            "only_in_original": only_original, "only_in_replay": only_replay,
            "no_completed_round": no_completed_round}


def check_accepted_records(original, replay, *, expect_different, require_all):
    common, only_original, only_replay = _common_and_only(original, replay)
    no_completed_round = _no_completed_round(original, common)
    comparable = [identity for identity in common if identity not in no_completed_round]
    differences = []
    for identity in comparable:
        left, right = original[identity], replay[identity]
        if left["verdict_class"] != right["verdict_class"]:
            continue  # the 1st check already reports the class mismatch
        if left["verdict_class"] == "accepted_valid":
            if (left["core"] or {}) != (right["core"] or {}):
                differences.append({
                    "input": identity, "kind": "core", "expected_different": identity in expect_different,
                    "original": left["core"], "replay": right["core"]})
        elif left["verdict_class"] == "accepted_invalid":
            left_ce = {name: sorted(rows) for name, rows in (left["counterexample"] or {}).items()}
            right_ce = {name: sorted(rows) for name, rows in (right["counterexample"] or {}).items()}
            if left_ce != right_ce:
                differences.append({
                    "input": identity, "kind": "counterexample",
                    "expected_different": identity in expect_different,
                    "original": left_ce, "replay": right_ce})
    failing = [item for item in differences if not item["expected_different"]]
    passed = not failing and (not require_all or (not only_original and not only_replay))
    return {"name": CHECK_2_NAME, "passed": passed, "differences": differences,
            "only_in_original": only_original, "only_in_replay": only_replay,
            "no_completed_round": no_completed_round}


def check_ledgers(original, replay, *, expect_different, require_all):
    common, only_original, only_replay = _common_and_only(original, replay)
    no_completed_round = _no_completed_round(original, common)
    comparable = [identity for identity in common if identity not in no_completed_round]
    differences, timing_differences = [], []
    for identity in comparable:
        left_entries = list(original[identity]["ledger"])
        right_entries = list(replay[identity]["ledger"])
        # An entry's (clause, check kind, level) key is excluded from the
        # pass/fail decision entirely when either side recorded it
        # inconclusive there -- not just the inconclusive entry itself,
        # because the same key can carry a settled outcome on the other
        # side, and a decided-vs-inconclusive split at the same key is a
        # timing artifact, not a fidelity difference (see the module and
        # `docs/analysts-guide.md`'s own caveat on this check).
        inconclusive_keys = {(clause, kind, level) for clause, kind, level, outcome
                             in left_entries + right_entries if outcome == INCONCLUSIVE_OUTCOME}
        left_set = {entry for entry in left_entries if entry[:3] not in inconclusive_keys}
        right_set = {entry for entry in right_entries if entry[:3] not in inconclusive_keys}
        only_left = sorted(left_set - right_set)
        only_right = sorted(right_set - left_set)
        if only_left or only_right:
            differences.append({
                "input": identity, "expected_different": identity in expect_different,
                "only_in_original": [list(entry) for entry in only_left],
                "only_in_replay": [list(entry) for entry in only_right]})
        timing = sorted({(clause, kind, level) for clause, kind, level in inconclusive_keys})
        if timing:
            timing_differences.append({"input": identity,
                                       "entries": [list(entry) for entry in timing]})
    failing = [item for item in differences if not item["expected_different"]]
    passed = not failing and (not require_all or (not only_original and not only_replay))
    return {"name": CHECK_3_NAME, "passed": passed, "differences": differences,
            "timing_differences": timing_differences,
            "only_in_original": only_original, "only_in_replay": only_replay,
            "no_completed_round": no_completed_round}


# --------------------------------------------------------------------------
# Reporting


def _format_gap(label, ids):
    return f"  {label}: {', '.join(ids)}" if ids else None


def render_check(check):
    lines = [f"{check['name']}: {'PASS' if check['passed'] else 'FAIL'}"]
    for gap in (_format_gap("only in original", check["only_in_original"]),
               _format_gap("only in replay", check["only_in_replay"]),
               _format_gap("no completed round — nothing to compare", check.get("no_completed_round"))):
        if gap:
            lines.append(gap)
    for item in check.get("differences") or []:
        marker = " (expected different)" if item.get("expected_different") else ""
        if "kind" in item:
            lines.append(f"  {item['input']} [{item['kind']}]{marker}:")
            lines.append(f"    original: {item['original']}")
            lines.append(f"    replay:   {item['replay']}")
        elif "verdict_class" in item.get("original", {}):
            lines.append(f"  {item['input']}{marker}: original={item['original']['verdict_class']} "
                         f"({item['original']['status']}), replay={item['replay']['verdict_class']} "
                         f"({item['replay']['status']})")
        else:
            lines.append(f"  {item['input']}{marker}:")
            if item.get("only_in_original"):
                lines.append(f"    only in original: {item['only_in_original']}")
            if item.get("only_in_replay"):
                lines.append(f"    only in replay: {item['only_in_replay']}")
    for item in check.get("timing_differences") or []:
        lines.append(f"  {item['input']} timing difference (inconclusive on one side, excluded "
                     f"from PASS/FAIL): {item['entries']}")
    return lines


def compare(original_path, replay_path, *, expect_different=(), require_all=False):
    original, original_label = read_side(original_path)
    replay, replay_label = read_side(replay_path)
    expect_different = set(expect_different)
    checks = [
        check_verdicts(original, replay, expect_different=expect_different, require_all=require_all),
        check_accepted_records(original, replay, expect_different=expect_different, require_all=require_all),
        check_ledgers(original, replay, expect_different=expect_different, require_all=require_all),
    ]
    return {"original": original_label, "replay": replay_label,
            "checks": checks, "passed": all(check["passed"] for check in checks)}


def render_report(report):
    lines = [f"original: {report['original']}", f"replay:   {report['replay']}", ""]
    for check in report["checks"]:
        lines.extend(render_check(check))
        lines.append("")
    lines.append("overall: " + ("PASS" if report["passed"] else "FAIL"))
    return "\n".join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="python -m agent_houdini compare-runs", allow_abbrev=False, description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("original", metavar="ORIGINAL",
                        help="a harness run directory, a bare verifier destination, or an "
                             "export-transcript JSON file")
    parser.add_argument("replay", metavar="REPLAY",
                        help="a harness run directory or a bare verifier destination")
    parser.add_argument("--require-all", action="store_true",
                        help="an input present in only one run fails the checks it would "
                             "otherwise just be reported and ignored for")
    parser.add_argument("--expect-different", default="", metavar="ID[,ID...]",
                        help="inputs whose differences are reported but do not fail a check")
    parser.add_argument("--json", type=Path, default=None, metavar="PATH",
                        help="also write a machine-readable report here")
    options = parser.parse_args(sys.argv[1:] if argv is None else argv)
    try:
        report = compare(options.original, options.replay,
                         expect_different=_parse_ids(options.expect_different),
                         require_all=options.require_all)
    except CompareError as error:
        print(f"compare-runs: {error}", file=sys.stderr)
        return 2
    print(render_report(report))
    if options.json is not None:
        options.json.write_text(json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
                                encoding="utf-8")
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
