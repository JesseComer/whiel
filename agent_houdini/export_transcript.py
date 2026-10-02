# Author: Fangzhu Shen
"""Freeze a run's transcript into one publishable file, and nothing else.

`python3 -m agent_houdini export-transcript RUN_DIR OUT.json` reads a
harness run directory (`experiment run`'s own layout: `verifier/` and
`agent/` side by side) and writes a single JSON file built only from fields
this tool authors itself:

    kind, version                 a fixed format marker
    controls                      the run's recorded verifier controls
                                   (`campaign-settings.json`'s `controls`
                                   block; no paths, no proposer selection)
    provider, model,
    reasoning_effort               as recorded in `run.json` -- experimental
                                   facts, not machine or account details
    inputs.<ID>.requests           every consultation's own submission, in
                                   round order: its `kind`, `clauses`,
                                   `dropped` (resolved to clause text where
                                   the original prompt shows it, `null`
                                   where it cannot be), and `input` for a
                                   counterexample proposal -- a malformed
                                   payload is kept exactly as it was sent,
                                   apart from this `dropped` resolution and
                                   the removed `binding` (see below); a
                                   consultation with no recorded submission
                                   is `null`
    inputs.<ID>.expected           what the three `compare-runs` fidelity
                                   checks compare a replay against: verdict
                                   class and status, the accepted Core with
                                   levels (or the counterexample instance),
                                   and the attempt ledger reduced to
                                   (clause, check kind, level, outcome)

Every `binding` (a consultation's own digests, meaningless to a different
run) is dropped, along with every path, prompt, MCP exchange, provider
stream and solver output the run directory also holds -- a transcript is a
small file built for replay and review, not a copy of the run directory.
After writing, the file is scanned with the same unsafe-string check
`export_run.py` uses and deleted, with a non-zero exit, on any hit: this
tool's own fields are built from JSON already free of that content, so a
hit here would mean this tool has a bug, not that the input needed cleaning.

This is diagnostic tooling around a finished run directory: it reads what
`experiment run` already wrote and starts no campaign, proposer or solver.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

from .compare_runs import catalog_canonical_texts, completed_rounds, ledger_entries, verdict_class
from .experiment import find_agent_inputs, read_verifier_input
from .export_run import scan_file, unsafe_markers
from .run_records import SUBMISSIONS_FILE


TRANSCRIPT_KIND = "whiel_transcript_replay"
TRANSCRIPT_VERSION = 1


class ExportTranscriptError(ValueError):
    """The run directory cannot be turned into a frozen transcript."""


# --------------------------------------------------------------------------
# Reading one input's own submissions, verbatim apart from `binding` and a
# resolved `dropped` list -- the transcript's only lossy transformation, and
# one that only ever removes digests, never clause content.


PENDING_HEADER = re.compile(r"^# Pending clauses \(\d+\)\s*$", re.M)
PENDING_CLAUSE = re.compile(r"^    clause (\d+)  minimum level")
SECTION_END = re.compile(r"^(?:# |={10,})", re.M)


def _section(text, header):
    """The body of one rendered `# ...` prompt section, verbatim.

    Duplicated from `agent_houdini/tests/replay_proposer.py`'s own
    `_section`/`recorded_pending_sources` rather than imported: that module
    is test-only tooling that a real proposer must never import, and this
    one is the mirror image -- real tooling that must never import test
    tooling, however harmless the one function in common would be.
    """
    match = header.search(text)
    if not match:
        return ""
    rest = text[match.end():]
    end = SECTION_END.search(rest)
    return rest if not end else rest[:end.start()]


def recorded_pending_sources(prompt_text):
    """clause_id -> the clause text a recorded prompt's own "Pending
    clauses" section printed for it, the same way `replay_proposer.py`'s
    identically named function reads it (see that module for the format).
    """
    sources, current = {}, None
    for line in _section(prompt_text, PENDING_HEADER).split("\n"):
        header = PENDING_CLAUSE.match(line)
        if header:
            current = []
            sources[int(header.group(1))] = current
            continue
        if current is None:
            continue
        if line.startswith("        displayed:"):
            current = None
        elif line.startswith("        "):
            current.append(line[8:])
        else:
            current = None
    return {identifier: "\n".join(lines) for identifier, lines in sources.items() if lines}


def _last_submission_payload(path):
    """The last submitted `payload`, parsed, from one consultation's
    `submissions.jsonl` -- or `None` when it has nothing usable, meaning the
    original proposer never submitted this consultation.
    """
    if not path.is_file():
        return None
    payload = None
    try:
        with open(path, encoding="utf-8") as source:
            for line in source:
                line = line.strip()
                if not line:
                    continue
                try:
                    record = json.loads(line)
                except ValueError:
                    continue
                candidate = record.get("payload") if isinstance(record, dict) else None
                if not isinstance(candidate, str):
                    continue
                try:
                    document = json.loads(candidate)
                except ValueError:
                    continue
                if isinstance(document, dict):
                    payload = document
    except OSError:
        return None
    return payload


def _resolve_dropped(dropped, recorded_sources, *, on_unresolved):
    """Every `dropped` entry, replaced by the clause text it names, or
    `None` where the original prompt did not show it. Never the original
    reference: that carries only digests (`record_digest`, `formula_digest`,
    `consultation_digest`, `authorization_digest`), meaningless to a
    different run and excluded from a transcript file categorically.
    """
    resolved = []
    for entry in dropped:
        clause_id = None
        if isinstance(entry, dict):
            clause = entry.get("clause")
            if isinstance(clause, dict) and isinstance(clause.get("clause_id"), int):
                clause_id = clause["clause_id"]
        text = recorded_sources.get(clause_id) if clause_id is not None else None
        if text is None:
            on_unresolved(clause_id)
        resolved.append(text)
    return resolved


def _read_text(path):
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


TASK_HEADER = re.compile(r"^# Task \S+(?: — consultation (\d+))?", re.M)


def _consultation_number(prompt_text):
    """The consultation number a rendered prompt's own task header names, or
    `None` when it cannot be read. Duplicated from `experiment.py`'s
    `TASK_HEADER`/`parse_prompt` for the same reason `_section` above is
    duplicated rather than imported.
    """
    match = TASK_HEADER.search(prompt_text)
    return int(match.group(1)) if match and match.group(1) else None


def _frozen_submission(directory, identity, number, *, err):
    payload = _last_submission_payload(directory / SUBMISSIONS_FILE)
    if payload is None:
        return None
    frozen = {key: value for key, value in payload.items() if key != "binding"}
    dropped = frozen.get("dropped")
    if isinstance(dropped, list) and dropped:
        recorded_sources = recorded_pending_sources(_read_text(directory / "prompt.txt"))

        def unresolved(clause_id):
            print(f"export-transcript: {identity}: request {number}: cannot resolve "
                 f"dropped clause {clause_id} to text; recording it as null", file=err)

        frozen["dropped"] = _resolve_dropped(dropped, recorded_sources, on_unresolved=unresolved)
    return frozen


def _round_groups(agent_dir, identity):
    """This input's own wire requests, grouped by the *consultation* each one
    belongs to (a group's several requests are one consultation's correction
    cycle: an envelope- or content-level correction never runs a round --
    B's own prompt says so verbatim, "refused and no round ran"
    (`agent_houdini/prompt.py`'s `_correction_section`) -- so only a group's
    *last* member is real content; every earlier member in the same group
    was corrected away and never reached admission at all.

    A request whose own consultation number cannot be read (a missing or
    unreadable `prompt.txt`) is never merged with a neighbor by guesswork:
    it becomes its own one-request group, exactly the old, uncorrected
    behavior.
    """
    raw = []
    for agent in find_agent_inputs(agent_dir):
        if agent.get("identity") != identity:
            continue
        for request in agent["requests"]:
            raw.append((request["number"], request.get("directory")))
    raw.sort(key=lambda item: item[0])
    groups, current_consultation, current_group = [], None, []
    for number, directory in raw:
        consultation = _consultation_number(_read_text(directory / "prompt.txt")) if directory else None
        if current_group and (consultation is None or consultation != current_consultation):
            groups.append(current_group)
            current_group = []
        current_consultation = consultation
        current_group.append((number, directory))
        if consultation is None:
            groups.append(current_group)
            current_group = []
    if current_group:
        groups.append(current_group)
    return groups


def _input_requests(agent_dir, identity, *, err):
    """This input's own consultations, one entry per *round* (a group from
    `_round_groups`, collapsed to its last, uncorrected member), in order.

    A round whose last member has no recorded submission -- the original
    proposer never got to answer it, whether because the search's own
    deadline arrived mid-consultation or (rarer) because retention simply
    did not keep it -- is marked `cut_off` and carries a `null` submission;
    replaying it as though it were an answered round would let the live
    verifier admit content the original run never admitted (see the module
    docstring), so `TranscriptSource` must stop there instead, exactly as it
    stops at the true end of the transcript.

    Because a `cut_off` round is never replayed, and B never admits a clause
    on a round it cancels, the catalog a replay reaches contains exactly the
    clauses admission ever gave it in the original: the task's own ambient
    scope plus whatever a *completed* round proposed -- nothing a cut-off
    round would have added, because nothing was ever added on its account.
    The expected ledger (`_expected`, below) therefore needs no separate
    per-clause filtering of its own to stay within "rounds that completed":
    it already is, as long as this function keeps cut-off content out of
    what gets replayed, which is what it does.
    """
    rounds = []
    for round_number, group in enumerate(_round_groups(agent_dir, identity), start=1):
        last_number, last_directory = group[-1]
        submission = (_frozen_submission(last_directory, identity, last_number, err=err)
                     if last_directory else None)
        rounds.append({"number": round_number, "submission": submission,
                       "cut_off": submission is None})
    return rounds


# --------------------------------------------------------------------------
# The expected per-input record the replay fidelity checks compare against


def _core_rows(directory):
    core_path = directory / "Core.json"
    if not core_path.is_file():
        return None
    try:
        rows = json.loads(core_path.read_text(encoding="utf-8")).get("rows")
    except (OSError, ValueError):
        return None
    found = [{"source": row["source"], "level": row.get("level")}
            for row in rows or [] if isinstance(row, dict) and isinstance(row.get("source"), str)]
    return sorted(found, key=lambda row: row["source"]) if found else None


def _counterexample_relations(instance):
    relations = []
    for relation in (instance or {}).get("relations") or []:
        if isinstance(relation, dict) and isinstance(relation.get("name"), str):
            rows = relation.get("rows") if isinstance(relation.get("rows"), list) else []
            relations.append({"name": relation["name"],
                              "rows": sorted((list(row) for row in rows if isinstance(row, list)),
                                            key=str)})
    return {"relations": sorted(relations, key=lambda item: item["name"])} if relations else None


def _expected(directory, *, identity, err):
    verifier = read_verifier_input(directory)
    result = verifier.get("result") or {}
    status = result.get("status")
    verdict = verdict_class(status)
    core = _core_rows(directory) if verdict == "accepted_valid" else None
    counterexample = None
    if verdict == "accepted_invalid" and isinstance(verifier.get("counterexample"), dict):
        counterexample = _counterexample_relations(verifier["counterexample"].get("instance"))
    texts = catalog_canonical_texts(verifier.get("final_state") or {})
    history = verifier.get("attempt_history") or {}
    # No further per-clause filtering is needed here: a cut-off round is
    # never replayed (`_input_requests`, above) and B never admits a clause
    # on a round it cancels, so every ledger entry -- the task's own ambient
    # scope as much as anything a completed round proposed -- already
    # belongs to "rounds that completed" by construction. An earlier version
    # of this function filtered by which round's own submission proposed a
    # clause's text; that dropped a run's ambient/precondition clauses too
    # (never "proposed" by anyone), which is a masking bug, not a fix --
    # see docs/analysts-guide.md for the real cause it was chasing.
    entries = ledger_entries(history.get("ledger"), texts)
    if not texts and entries:
        print(f"export-transcript: {identity}: no catalog was published for this input "
             "(the deadline landed before any final_owner_projection); its ledger entries "
             "carry run-local #<id> labels that will not match a replay's own numbering",
             file=err)
    ledger = sorted(entries, key=lambda entry: [str(part) for part in entry])
    rounds_completed = completed_rounds(history)
    return {"status": status, "verdict_class": verdict, "core": core,
            "counterexample": counterexample, "ledger": [list(entry) for entry in ledger],
            "completed_rounds": rounds_completed}


# --------------------------------------------------------------------------


def build_transcript(run_dir, *, err=None):
    err = sys.stderr if err is None else err
    run_dir = Path(run_dir)
    verifier_dir, agent_dir = run_dir / "verifier", run_dir / "agent"
    if not verifier_dir.is_dir() or not agent_dir.is_dir():
        raise ExportTranscriptError(
            f"{run_dir} is not a harness run directory (needs verifier/ and agent/)")
    run_json = run_dir / "run.json"
    spec = {}
    if run_json.is_file():
        try:
            spec = json.loads(run_json.read_text(encoding="utf-8")).get("spec") or {}
        except (OSError, ValueError):
            spec = {}
    controls = None
    settings_path = verifier_dir / "campaign-settings.json"
    if settings_path.is_file():
        try:
            controls = json.loads(settings_path.read_text(encoding="utf-8")).get("controls")
        except (OSError, ValueError):
            controls = None
    document = {
        "kind": TRANSCRIPT_KIND, "version": TRANSCRIPT_VERSION,
        "controls": controls,
        "provider": spec.get("provider"), "model": spec.get("model"),
        "reasoning_effort": spec.get("reasoning_effort"),
        "inputs": {},
    }
    for directory in sorted(verifier_dir.iterdir()):
        if not directory.is_dir() or not (directory / "result.json").is_file():
            continue
        identity = directory.name
        document["inputs"][identity] = {
            "requests": _input_requests(agent_dir, identity, err=err),
            "expected": _expected(directory, identity=identity, err=err),
        }
    return document


def export_transcript(run_dir, out_path, *, out=None, err=None) -> int:
    out = sys.stdout if out is None else out
    err = sys.stderr if err is None else err
    out_path = Path(out_path)
    try:
        document = build_transcript(run_dir, err=err)
    except ExportTranscriptError as error:
        print(f"export-transcript: {error}", file=err)
        return 2
    if out_path.exists():
        print(f"export-transcript: {out_path} already exists; choose a fresh destination", file=err)
        return 2
    text = json.dumps(document, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    try:
        out_path.write_text(text, encoding="utf-8")
    except OSError as error:
        print(f"export-transcript: cannot write {out_path}: {error}", file=err)
        return 2
    hits = scan_file(out_path, unsafe_markers())
    if hits:
        for marker, location, excerpt in hits:
            print(f"export-transcript: unsafe: {out_path} {location}: {marker!r} in {excerpt!r}",
                 file=err)
        out_path.unlink(missing_ok=True)
        print(f"export-transcript: refusing to leave {out_path} in place: "
             f"{len(hits)} unsafe hit(s), see above -- this is a bug in export_transcript.py, "
             "not something to work around", file=err)
        return 1
    print(f"export-transcript: {out_path}", file=out)
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="python -m agent_houdini export-transcript", allow_abbrev=False, description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("run_dir", type=Path, metavar="RUN_DIR",
                        help="a harness run directory (has verifier/ and agent/)")
    parser.add_argument("out_path", type=Path, metavar="OUT.json",
                        help="the not-yet-existing file to write")
    options = parser.parse_args(sys.argv[1:] if argv is None else argv)
    return export_transcript(options.run_dir, options.out_path)


if __name__ == "__main__":
    raise SystemExit(main())
