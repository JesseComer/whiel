# Author: Fangzhu Shen
"""Experiments: one spec file in, one self-describing run directory out.

`python3 -m agent_houdini experiment run SPEC.json` reads a JSON spec that
names the inputs, the provider, model and effort, the isolation and the
verifier limits, and creates one run directory

    <output_root>/<model>-<YYYYMMDD>[-<name>]/
        run.json          the resolved spec, the exact command, revision, timing, exit code
        launcher.log      everything the launcher and the verifier printed
        verifier/         B's campaign destination: campaign-settings.json, summary.json, <ID>/...
        agent/            C's logs: launcher.jsonl, <ID>/events.jsonl, <ID>/request-N/...
        progress.md       one row per input: verdict, consultations, clauses, Core
        examples/<ID>/    summary.md (the input's rounds, clauses, ledger, countermodels)
                          verifier -> ../../verifier/<ID>, agent -> ../../agent/<ID>

then starts the public campaign command with B's destination and C's log
directory both inside it, and writes the digest when the campaign has ended.

`python3 -m agent_houdini experiment report RUN_DIR` rewrites the digest for a
finished or still running run. Given a campaign directory made before this
layout existed (`artifacts/campaigns/<name>`, with its agent logs under
`artifacts/agent-logs/<name>`), it builds the run directory under
`artifacts/runs/<name>` with links to both, so old runs read the same way.

The digest is C's reading of the two record trees, for the person running the
experiment. It is never evidence: an input's verdict is its `result.json`, and
its proof is `Certificate/`.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

from .run_records import MCP_FILE, PROMPT_FILE, STDOUT_FILE, SUBMISSIONS_FILE, read_entries
from .safe_paths import safe_argv, safe_environment, safe_path
from .token_usage import MODES as USAGE_MODES, USAGE_ENV, write_usage_report


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
RUN_FILE = "run.json"
LAUNCHER_LOG = "launcher.log"
VERIFIER_DIR = "verifier"
AGENT_DIR = "agent"
EXAMPLES_DIR = "examples"
PROGRESS_FILE = "progress.md"
PROGRESS_JSON = "progress.json"
SUMMARY_FILE = "summary.md"
ROUNDS_FILE = "rounds.json"
MAXIMUM_ENTRIES = 20000
# Written into every rounds.json beside the figures it describes, so an
# analyst reading the file alone cannot mistake the split for search time.
ROUND_SECONDS_MEANING = (
    "agent_seconds and verifier_seconds split one consultation between the model and the "
    "verifier. They are this harness's estimate from its own log file timestamps, not a "
    "measurement either side made: agent_seconds spans that consultation's request records and "
    "includes the harness's overhead, and verifier_seconds is the gap to the next request, null "
    "on the last round. Neither is search time; an input's search time is search_seconds, which "
    "the verifier measures around its own search loop."
)
MAXIMUM_FRAME_BYTES = 64 * 1024 * 1024
SKILLS_ENV = "WHIEL_AGENT_SKILLS_FILE"

# Every accepted spec key with its default; an unknown key is refused so a
# misspelled limit cannot silently fall back to the verifier's default.
SPEC_DEFAULTS = {
    "name": None, "notes": "",
    # `agent` runs the C launcher against a provider; `replay` runs the
    # token-free replay proposer, which needs no provider and no model and
    # submits the repository's own recorded answer for each input, or, with
    # `transcript` set, a retained run's own responses instead; `answers`
    # names another directory of recorded answers (a run's accepted ones).
    "proposer": "agent", "transcript": None, "answers": None,
    "provider": "codex", "model": None, "reasoning_effort": None, "provider_cli": None,
    "isolation": "bwrap",
    "inputs": None, "all_inputs": False,
    "repo": None, "verifier": "whiel_runner/target/release/whiel-symbolic",
    "output_root": "artifacts/runs",
    "search_limit_seconds": None, "certification_limit_seconds": None,
    "consultation_limit_seconds": None, "iteration_limit": None, "workers": None,
    "retention": "all",
    # inline certifies each input after its own search; deferred searches
    # every input first and certifies them in one final phase; never leaves
    # the run directory for a later `campaign certify --run DIR`. A large
    # campaign wants `deferred`: the agents are paid for by the hour and the
    # certification is deterministic.
    "certify": "inline",
    "agent_retention": "all", "agent_thinking_tokens": None, "skills_file": None,
    "skills_dir": None,
    "token_usage": "off",
    "verifier_args": [], "agent_args": [],
}
PATH_FIELDS = ("repo", "verifier", "provider_cli", "output_root", "skills_file", "skills_dir",
              "transcript", "answers")
NAME_PATTERN = re.compile(r"[^A-Za-z0-9._-]+")
# A replay run has no provider, model, prompt, sandbox or agent log, so every
# key that configures one is refused rather than silently ignored.
AGENT_ONLY_FIELDS = ("provider", "model", "reasoning_effort", "provider_cli", "isolation",
                     "agent_retention", "agent_thinking_tokens", "skills_file", "skills_dir",
                     "agent_args", "token_usage")
REPLAY_TOOL = Path(__file__).resolve().parent / "tests" / "replay_proposer.py"
REPLAY_DIR = "replay"


class SpecError(ValueError):
    """The spec cannot be turned into a campaign command."""


# --------------------------------------------------------------------------
# Spec


def load_spec(path):
    path = Path(path)
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise SpecError(f"cannot read spec {path}: {error}") from error
    if not isinstance(document, dict):
        raise SpecError("a spec is a JSON object")
    unknown = sorted(set(document) - set(SPEC_DEFAULTS))
    if unknown:
        raise SpecError("unknown spec keys: " + ", ".join(unknown))
    spec = dict(SPEC_DEFAULTS)
    spec.update(document)
    return spec


def _text(value, name, *, optional=False):
    if value is None and optional:
        return None
    if not isinstance(value, str) or not value or "\0" in value:
        raise SpecError(f"{name} must be a nonempty string")
    return value


def _number(value, name, *, integer=False):
    if value is None:
        return None
    if isinstance(value, bool) or not isinstance(value, (int, float)) or value <= 0:
        raise SpecError(f"{name} must be a positive number")
    if integer and int(value) != value:
        raise SpecError(f"{name} must be a whole number")
    return int(value) if integer else value


def _strings(value, name):
    if value is None:
        return []
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise SpecError(f"{name} must be a list of strings")
    return list(value)


def resolve_spec(spec):
    """Check every field and make every path absolute; nothing is created."""
    unknown = sorted(set(spec) - set(SPEC_DEFAULTS))
    if unknown:
        raise SpecError("unknown spec keys: " + ", ".join(unknown))
    resolved = dict(SPEC_DEFAULTS)
    resolved.update(spec)
    spec = dict(resolved)
    resolved["proposer"] = _text(spec.get("proposer"), "proposer")
    if resolved["proposer"] not in ("agent", "replay"):
        raise SpecError("proposer must be agent or replay")
    if resolved["proposer"] == "replay":
        for name in AGENT_ONLY_FIELDS:
            if spec.get(name) != SPEC_DEFAULTS[name]:
                raise SpecError(f"a replay proposer consults no model, so it takes no {name}")
            resolved[name] = None
        resolved["agent_args"] = []
    else:
        if spec.get("transcript") is not None:
            raise SpecError("transcript replay needs proposer: replay")
        if spec.get("answers") is not None:
            raise SpecError("answer replay needs proposer: replay")
        resolved["model"] = _text(spec.get("model"), "model")
        resolved["provider"] = _text(spec.get("provider"), "provider")
        if resolved["provider"] not in ("codex", "claude"):
            raise SpecError("provider must be codex or claude")
        resolved["reasoning_effort"] = _text(spec.get("reasoning_effort"), "reasoning_effort", optional=True)
        resolved["isolation"] = _text(spec.get("isolation"), "isolation")
        if resolved["isolation"] not in ("local", "bwrap"):
            raise SpecError("isolation must be local or bwrap")
        if resolved["token_usage"] not in USAGE_MODES:
            raise SpecError("token_usage must be one of: " + ", ".join(USAGE_MODES))
        if resolved["token_usage"] != "off" and (
                resolved["provider"] != "codex" or resolved["isolation"] != "bwrap"
                or resolved["agent_retention"] != "all"):
            raise SpecError("codex-rollout usage requires Codex, bwrap and agent_retention: all")
    resolved["name"] = _text(spec.get("name"), "name", optional=True)
    resolved["notes"] = spec.get("notes") if isinstance(spec.get("notes"), str) else ""
    inputs = _strings(spec.get("inputs"), "inputs")
    if bool(spec.get("all_inputs")) == bool(inputs):
        raise SpecError("give either a nonempty inputs list or all_inputs: true")
    resolved["inputs"] = inputs
    resolved["all_inputs"] = bool(spec.get("all_inputs"))
    repo = Path(_text(spec.get("repo"), "repo", optional=True) or PACKAGE_ROOT)
    repo = repo.expanduser()
    resolved["repo"] = str(repo.resolve())
    for name in ("verifier", "provider_cli", "output_root", "skills_file", "skills_dir", "transcript",
                 "answers"):
        value = _text(spec.get(name), name, optional=True)
        resolved[name] = None if value is None else str((repo / Path(value).expanduser()).resolve())
    if resolved["transcript"] and resolved["answers"]:
        raise SpecError("give transcript or answers, not both")
    if resolved["skills_file"] and resolved["skills_dir"]:
        raise SpecError("give skills_file or skills_dir, not both")
    if resolved["verifier"] is None:
        raise SpecError("verifier must name the whiel-symbolic executable")
    for name in ("search_limit_seconds", "certification_limit_seconds", "consultation_limit_seconds"):
        resolved[name] = _number(spec.get(name), name)
    for name in ("iteration_limit", "workers", "agent_thinking_tokens"):
        resolved[name] = _number(spec.get(name), name, integer=True)
    checked = [("retention", ("certificate-only", "all")),
               ("certify", ("inline", "deferred", "never"))]
    if resolved["proposer"] == "agent":
        checked.append(("agent_retention", ("events", "all")))
    for name, choices in checked:
        resolved[name] = _text(spec.get(name), name)
        if resolved[name] not in choices:
            raise SpecError(f"{name} must be one of " + ", ".join(choices))
    resolved["verifier_args"] = _strings(spec.get("verifier_args"), "verifier_args")
    resolved["agent_args"] = _strings(spec.get("agent_args"), "agent_args")
    return resolved


def safe_name(text):
    return NAME_PATTERN.sub("-", text).strip("-") or "run"


def run_directory_name(resolved, today=None):
    today = datetime.date.today() if today is None else today
    name = f"{safe_name(resolved['model'] or resolved['proposer'])}-{today:%Y%m%d}"
    if resolved.get("name"):
        name += "-" + safe_name(resolved["name"])
    return name


def allocate_run_directory(root, name):
    """A fresh `<root>/<name>`, or `<name>-2`, `-3`, ... when it is taken."""
    root = Path(root)
    root.mkdir(parents=True, exist_ok=True)
    for attempt in range(1, 1000):
        candidate = root / (name if attempt == 1 else f"{name}-{attempt}")
        try:
            candidate.mkdir(mode=0o755)
        except FileExistsError:
            continue
        return candidate
    raise SpecError(f"no free run directory name under {root} for {name}")


def build_command(resolved, run_dir):
    """The launcher command, its environment additions and its cwd."""
    run_dir = Path(run_dir)
    if resolved["proposer"] == "replay":
        # No launcher and no C endpoint: B starts the replay proposer itself,
        # exactly as it would start any other generic wire-3 executable. The
        # arguments stay absolute because the endpoint starts in a private
        # working directory; B records the ones inside the repository
        # relative to it, so the run's records carry no machine location.
        argv = [resolved["verifier"], "campaign", "run",
                "--proposer-executable", sys.executable,
                "--proposer-arg", str(REPLAY_TOOL),
                "--proposer-arg", "--repo", "--proposer-arg", resolved["repo"],
                "--proposer-arg", "--log",
                "--proposer-arg", str(run_dir / REPLAY_DIR / "endpoints.jsonl")]
        if resolved["transcript"]:
            argv += ["--proposer-arg", "--transcript", "--proposer-arg", resolved["transcript"]]
        if resolved["answers"]:
            argv += ["--proposer-arg", "--answers", "--proposer-arg", resolved["answers"]]
        argv += ["--repo", resolved["repo"]]
    else:
        argv = [sys.executable, "-m", "agent_houdini", "campaign", "run",
                "--verifier", resolved["verifier"],
                "--provider", resolved["provider"], "--model", resolved["model"]]
        if resolved["reasoning_effort"]:
            argv += ["--reasoning-effort", resolved["reasoning_effort"]]
        if resolved["provider_cli"]:
            argv += ["--provider-cli", resolved["provider_cli"]]
        argv += ["--isolation", resolved["isolation"],
                 "--agent-log-dir", str(run_dir / AGENT_DIR),
                 "--agent-retention", resolved["agent_retention"]]
        if resolved["agent_thinking_tokens"]:
            argv += ["--agent-thinking-tokens", str(resolved["agent_thinking_tokens"])]
        argv += resolved["agent_args"]
        argv += ["--", "--repo", resolved["repo"]]
    if resolved["all_inputs"]:
        argv += ["--all"]
    else:
        argv += ["--input", ",".join(resolved["inputs"])]
    argv += ["--destination", str(run_dir / VERIFIER_DIR), "--retention", resolved["retention"],
             "--certify", resolved["certify"]]
    for name, option in (("search_limit_seconds", "--search-limit"),
                         ("certification_limit_seconds", "--certification-limit"),
                         ("consultation_limit_seconds", "--consultation-limit"),
                         ("iteration_limit", "--iteration-limit"), ("workers", "--workers")):
        if resolved[name] is not None:
            argv += [option, str(resolved[name])]
    argv += resolved["verifier_args"]
    environment = {}
    skills = resolved["skills_dir"] or resolved["skills_file"]
    if skills:
        environment[SKILLS_ENV] = skills
    if resolved["proposer"] == "agent" and resolved["token_usage"] != "off":
        environment[USAGE_ENV] = resolved["token_usage"]
    return argv, environment, str(PACKAGE_ROOT)


def _git_revision(repo):
    try:
        output = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"], capture_output=True,
                                text=True, timeout=10, check=False)
    except (OSError, subprocess.SubprocessError):
        return None
    text = output.stdout.strip()
    return text if output.returncode == 0 and text else None


def _now():
    return datetime.datetime.now().astimezone().isoformat(timespec="seconds")


def _write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
                          encoding="utf-8")


def _recorded_spec(resolved):
    """`resolved`, with every path field made safe for a written record.

    The values `build_command` and the rest of `run` act on stay absolute so
    the launcher can actually start the campaign; only this copy, going into
    `run.json`, is repo-relative or placeholdered, so the file itself carries
    no machine location, home directory or user name.
    """
    repo = resolved["repo"]
    recorded = dict(resolved)
    for name in PATH_FIELDS:
        if name != "repo":
            recorded[name] = safe_path(resolved[name], repo,
                                       executable=name in ("verifier", "provider_cli"))
    recorded["repo"] = safe_path(repo, repo)
    return recorded


def _recorded_command(argv, resolved):
    """`argv`, with every absolute path token made safe for a written record."""
    repo = resolved["repo"]
    executables = {value for value in (sys.executable, resolved.get("verifier"), resolved.get("provider_cli"))
                   if isinstance(value, str)}
    return safe_argv(argv, repo, executables=executables)


def run(spec_path, *, dry_run=False, out=None):
    """Create the run directory, start the campaign, then write the digest."""
    out = sys.stdout if out is None else out
    spec_path = Path(spec_path)
    resolved = resolve_spec(load_spec(spec_path))
    name = run_directory_name(resolved)
    if dry_run:
        argv, environment, cwd = build_command(resolved, Path(resolved["output_root"]) / name)
        print(f"run directory: {Path(resolved['output_root']) / name}", file=out)
        print("command: " + " ".join(_quote(item) for item in argv), file=out)
        for key, value in environment.items():
            print(f"environment: {key}={value}", file=out)
        print(f"cwd: {cwd}", file=out)
        return 0
    run_dir = allocate_run_directory(resolved["output_root"], name)
    if resolved["proposer"] == "replay":
        (run_dir / REPLAY_DIR).mkdir(exist_ok=True)
    argv, environment, cwd = build_command(resolved, run_dir)
    repo = resolved["repo"]
    # Every path here is recorded relative to the repo, or placeholdered when
    # it falls outside it: a run directory is made to be exported to a
    # collaborator who never had this checkout at this location, and a
    # machine's home directory, user name or host name has no place in it.
    record = {
        "schema_version": 1, "spec_file": safe_path(spec_path, repo), "spec": _recorded_spec(resolved),
        "run_directory": safe_path(run_dir, repo), "command": _recorded_command(argv, resolved),
        "environment": safe_environment(environment, repo), "cwd": safe_path(cwd, repo),
        "python": safe_path(sys.executable, repo, executable=True),
        "git_revision": _git_revision(resolved["repo"]),
        "started_at": _now(), "finished_at": None, "exit_code": None, "status": "running",
        "pid": None,
    }
    _write_json(run_dir / RUN_FILE, record)
    print(f"experiment run: {run_dir}", file=out)
    child_environment = dict(os.environ)
    child_environment.pop(USAGE_ENV, None)
    child_environment.update(environment)
    status = 1
    with open(run_dir / LAUNCHER_LOG, "ab") as log:
        try:
            child = subprocess.Popen(argv, cwd=cwd, env=child_environment,
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        except OSError as error:
            record.update(status="failed", finished_at=_now(), exit_code=None,
                          failure=f"cannot start the launcher: {error}")
            _write_json(run_dir / RUN_FILE, record)
            print(f"experiment run: cannot start the launcher: {error}", file=sys.stderr)
            return 2
        record["pid"] = child.pid
        _write_json(run_dir / RUN_FILE, record)
        previous = {}
        interrupted = []

        def forward(number, _frame):
            interrupted.append(number)
            try:
                child.send_signal(number)
            except OSError:
                pass

        for number in (signal.SIGINT, signal.SIGTERM):
            previous[number] = signal.signal(number, forward)
        try:
            for line in child.stdout:
                log.write(line)
                log.flush()
                out.write(line.decode("utf-8", errors="replace"))
                out.flush()
            status = child.wait()
        finally:
            child.stdout.close()
            for number, handler in previous.items():
                signal.signal(number, handler)
    record.update(finished_at=_now(), exit_code=status,
                  status="interrupted" if interrupted else "finished")
    _write_json(run_dir / RUN_FILE, record)
    try:
        progress = write_report(run_dir)
        print(f"experiment report: {progress}", file=out)
    except Exception as error:  # the campaign's result stands whatever the digest does
        print(f"experiment report failed: {error}", file=sys.stderr)
    return status


def _quote(text):
    return text if re.fullmatch(r"[A-Za-z0-9_./:=,@+-]+", text) else "'" + text.replace("'", "'\\''") + "'"


# --------------------------------------------------------------------------
# Reading C's records


def _json(path):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None


TASK_HEADER = re.compile(r"^# Task (\S+)(?: — consultation (\d+))?", re.M)
CORE_HEADER = re.compile(r"^# Current Core \((\d+) clauses\)", re.M)
PENDING_HEADER = re.compile(r"^# Pending clauses \((\d+)\)", re.M)
LAST_ROUND_HEADER = re.compile(r"^# Last round \((\d+) clauses\)", re.M)
LATEST_LINE = re.compile(r"^# Latest result\n\n    (.+)$", re.M)
CLAUSE_LINE = re.compile(r"^    clause (\d+)  (.*)$")
CORRECTION_HEADER = "# Correction on your previous response"
PUSH_MARKER = "COMPLETE CONTROLLER PUSH"
SECTION_END = re.compile(r"^(?:# |={10,})", re.M)


def _section(text, header):
    """The body of one rendered `# ...` section, up to the next heading or rule."""
    match = header.search(text)
    if not match:
        return ""
    rest = text[match.end():]
    end = SECTION_END.search(rest)
    return rest if not end else rest[:end.start()]


def _clause_entries(section):
    """`    clause N  words` lines with their indented clause text beneath."""
    entries = []
    for line in section.split("\n"):
        match = CLAUSE_LINE.match(line)
        if match:
            entries.append({"id": int(match.group(1)), "words": match.group(2).strip(),
                            "source": [], "display": []})
        elif entries and line.startswith("        "):
            body = line[8:]
            if body.startswith("displayed: "):
                entries[-1]["display"].append(body[len("displayed: "):])
            else:
                entries[-1]["source"].append(body)
    for entry in entries:
        entry["text"] = "\n".join(entry["display"] or entry["source"])
        entry["outcome"] = entry["words"].split("  origin ")[0].strip()
    return entries


def parse_prompt(text):
    """What one rendered prompt says about its push.

    The rendered sections are the source: the task header, the Core, pending
    and last-round entries with the verifier's clause text, the latest result
    and any correction. A prompt recorded before 2026-09-17 also carried the
    whole observation as JSON; it is read too, for the same fields, so older
    runs digest the same way.
    """
    found = {"task": None, "consultation": None, "correction": CORRECTION_HEADER in text,
             "core": None, "pending": None, "last_round": None, "latest": None,
             "core_entries": [], "pending_entries": [], "last_round_entries": [],
             "correction_lines": [], "observation": None}
    match = TASK_HEADER.search(text)
    if match:
        found["task"] = match.group(1)
        found["consultation"] = int(match.group(2)) if match.group(2) else None
    for key, pattern in (("core", CORE_HEADER), ("pending", PENDING_HEADER),
                         ("last_round", LAST_ROUND_HEADER)):
        match = pattern.search(text)
        found[key] = int(match.group(1)) if match else None
        found[key + "_entries"] = _clause_entries(_section(text, pattern))
    match = LATEST_LINE.search(text)
    found["latest"] = match.group(1).strip() if match else None
    if found["correction"]:
        body = text[text.index(CORRECTION_HEADER) + len(CORRECTION_HEADER):]
        end = SECTION_END.search(body)
        body = body if not end else body[:end.start()]
        found["correction_lines"] = [line.strip() for line in body.split("\n")
                                     if line.startswith("    ") and not line.startswith("        ")]
    marker = text.rfind(PUSH_MARKER)
    if marker >= 0:
        start = text.find("{", marker)
        if start >= 0:
            try:
                found["observation"] = json.loads(text[start:])
            except ValueError:
                found["observation"] = None
    return found


def _clause_text(entry):
    clause = entry.get("clause") if isinstance(entry, dict) else None
    if not isinstance(clause, dict):
        return None, None
    identifier = clause.get("clause_id")
    text = clause.get("display") or clause.get("canonical_source")
    return (identifier if isinstance(identifier, int) else None), (text if isinstance(text, str) else None)


def prompt_clauses(prompt):
    """Clause texts by id, from the rendered sections and, if present, the observation."""
    texts = {}
    for key in ("core_entries", "pending_entries", "last_round_entries"):
        for entry in prompt.get(key) or []:
            if entry.get("text"):
                texts.setdefault(entry["id"], entry["text"])
    observation = prompt.get("observation")
    feedback = observation.get("feedback") if isinstance(observation, dict) else None
    if isinstance(feedback, dict):
        for key in ("core", "pending", "last_round"):
            for entry in feedback.get(key) or []:
                identifier, text = _clause_text(entry)
                if identifier is not None and text:
                    texts.setdefault(identifier, text)
    return texts


def agent_turn(entries):
    """The agent's own words and tool calls from the CLI stream (Codex or Claude)."""
    messages, calls = [], []
    for entry in entries:
        kind = entry.get("type")
        if kind == "item.completed":
            item = entry.get("item") if isinstance(entry.get("item"), dict) else {}
            if item.get("type") == "agent_message" and isinstance(item.get("text"), str):
                messages.append(item["text"])
            elif item.get("type") == "mcp_tool_call":
                error = item.get("error")
                calls.append({"tool": item.get("tool"), "arguments": item.get("arguments"),
                              "status": item.get("status"),
                              "error": None if error in (None, "") else str(error)[:300]})
        elif kind == "assistant":
            message = entry.get("message") if isinstance(entry.get("message"), dict) else {}
            for block in message.get("content") or []:
                if not isinstance(block, dict):
                    continue
                if block.get("type") == "text" and isinstance(block.get("text"), str):
                    messages.append(block["text"])
                elif block.get("type") == "tool_use":
                    name = str(block.get("name") or "")
                    calls.append({"tool": name.rsplit("__", 1)[-1], "arguments": block.get("input"),
                                  "status": "called", "error": None})
    return messages, calls


def mcp_calls(entries):
    """Tool calls with reply sizes, errors and the reply text, in call order."""
    replies = {entry.get("exchange"): entry for entry in entries if entry.get("direction") == "reply"}
    calls = []
    for entry in entries:
        if entry.get("direction") != "request" or entry.get("method") != "tools/call":
            continue
        reply = replies.get(entry.get("exchange"), {})
        calls.append({"tool": entry.get("tool") or "?", "sent": entry.get("bytes"),
                      "received": reply.get("bytes"), "error": reply.get("error"),
                      "time": entry.get("time"), "reply_time": reply.get("time"),
                      "reply_text": reply.get("text") or ""})
    return calls


def _tool_result_json(reply_text):
    """The JSON a query tool returned, unwrapped from its MCP envelope."""
    try:
        envelope = json.loads(reply_text)
        content = envelope.get("result", {}).get("content") or []
        text = content[0].get("text") if content and isinstance(content[0], dict) else None
        return json.loads(text) if isinstance(text, str) else None
    except (ValueError, AttributeError, TypeError):
        return None


def parse_submission(entry):
    payload = None
    try:
        payload = json.loads(entry.get("payload") or "")
    except ValueError:
        payload = None
    if not isinstance(payload, dict):
        payload = {}
    instance = payload.get("input") if isinstance(payload.get("input"), dict) else None
    relations = []
    if instance:
        for relation in instance.get("relations") or []:
            if isinstance(relation, dict):
                rows = relation.get("rows") if isinstance(relation.get("rows"), list) else []
                relations.append((str(relation.get("name")), rows))
    return {"kind": payload.get("kind") or "?",
            "clauses": [text for text in (payload.get("clauses") or []) if isinstance(text, str)],
            "dropped": len(payload.get("dropped") or []),
            "instance": relations if instance else None,
            "verdict": entry.get("verdict"), "detail": entry.get("detail"),
            "time": entry.get("time")}


def read_request(directory, events):
    """One consultation, from its retained files and its events."""
    request = {"directory": directory, "name": directory.name if directory else None,
               "prompt": None, "prompt_bytes": None, "messages": [], "native_calls": [],
               "calls": [], "submissions": [], "outcome": None, "diagnostic": None,
               "rejections": [], "started": None, "ended": None}
    for event in events:
        fields = event.get("fields") if isinstance(event.get("fields"), dict) else {}
        kind = event.get("kind")
        if kind == "request_started":
            request["prompt_bytes"] = fields.get("prompt_bytes")
        elif kind == "request_outcome":
            request["outcome"] = fields.get("outcome")
            request["diagnostic"] = fields.get("diagnostic_code")
        elif kind == "mcp_rejection":
            request["rejections"].append(str(fields.get("reason")))
        elif kind == "native_deadline":
            request["rejections"].append("deadline: " + json.dumps(fields, default=str)[:200])
    if directory is None or not directory.is_dir():
        return request
    prompt_path = directory / PROMPT_FILE
    if prompt_path.is_file():
        try:
            text = prompt_path.read_text(encoding="utf-8", errors="replace")
            request["prompt"] = parse_prompt(text)
            request["prompt_bytes"] = request["prompt_bytes"] or len(text.encode("utf-8"))
            request["started"] = prompt_path.stat().st_mtime
        except OSError:
            pass
    request["messages"], request["native_calls"] = agent_turn(
        read_entries(directory / STDOUT_FILE, maximum=MAXIMUM_ENTRIES))
    request["calls"] = mcp_calls(read_entries(directory / MCP_FILE, maximum=MAXIMUM_ENTRIES))
    request["submissions"] = [parse_submission(entry) for entry in
                              read_entries(directory / SUBMISSIONS_FILE, maximum=MAXIMUM_ENTRIES)]
    ends = [call["reply_time"] for call in request["calls"] if call.get("reply_time")]
    ends += [item["time"] for item in request["submissions"] if item.get("time")]
    for name in (SUBMISSIONS_FILE, MCP_FILE, STDOUT_FILE):
        path = directory / name
        if path.is_file():
            try:
                ends.append(path.stat().st_mtime)
            except OSError:
                pass
    request["ended"] = max(ends) if ends else None
    return request


def _request_number(name):
    match = re.fullmatch(r"request-(\d+)", name)
    return int(match.group(1)) if match else None


def read_agent_input(directory):
    """Everything C kept for one input: its identity, requests and outcome."""
    events = read_entries(directory / "events.jsonl", maximum=MAXIMUM_ENTRIES)
    by_request, current = {}, None
    identity = None
    configuration = {}
    traffic = None
    for event in events:
        kind = event.get("kind")
        fields = event.get("fields") if isinstance(event.get("fields"), dict) else {}
        if kind == "endpoint_configuration":
            configuration = fields
        elif kind == "input_identified" and isinstance(fields.get("canonical_id"), str):
            identity = fields["canonical_id"]
        elif kind == "agent_traffic":
            traffic = fields
        number = fields.get("request_id")
        if kind == "request_started":
            current = number
        key = number if number is not None else current
        if key is not None:
            by_request.setdefault(key, []).append(event)
        if kind == "request_outcome":
            current = None
    numbers = set(by_request)
    for child in directory.iterdir() if directory.is_dir() else []:
        number = _request_number(child.name)
        if number is not None and child.is_dir():
            numbers.add(number)
    requests = []
    for number in sorted(numbers):
        child = directory / f"request-{number}"
        requests.append(read_request(child if child.is_dir() else None, by_request.get(number, [])))
        requests[-1]["number"] = number
    if identity is None:
        for request in requests:
            prompt = request.get("prompt") or {}
            if prompt.get("task"):
                identity = prompt["task"]
                break
    if identity is None and re.fullmatch(r"Example[A-Za-z0-9]+(?:-\d+)?", directory.name):
        identity = directory.name.rsplit("-", 1)[0] if re.search(r"-\d+$", directory.name) else directory.name
    return {"directory": directory, "identity": identity, "requests": requests,
            "configuration": configuration, "traffic": traffic}


def find_agent_inputs(agent_dir):
    """Every per-input log directory under C's tree, new or old layout."""
    agent_dir = Path(agent_dir)
    if not agent_dir.is_dir():
        return []
    found = []
    for pattern in ("events.jsonl", "*/events.jsonl", "*/*/events.jsonl"):
        for path in sorted(agent_dir.glob(pattern)):
            if path.parent not in found:
                found.append(path.parent)
    return [read_agent_input(directory) for directory in found]


# --------------------------------------------------------------------------
# Reading B's records


def _artifact_bytes(run_dir, record):
    path = run_dir / str(record.get("relative_path"))
    try:
        if path.stat().st_size > MAXIMUM_FRAME_BYTES:
            return None
        return path.read_bytes()
    except OSError:
        return None


def _frame_payload(data):
    """The JSON record inside one consultation-record frame."""
    try:
        frame = json.loads(data)
        payload = frame.get("payload")
        if isinstance(payload, list):
            return json.loads(bytes(payload))
    except (ValueError, TypeError):
        return None
    return None


def read_verifier_input(directory):
    """B's verdict, certificate, ledger and final state for one input."""
    directory = Path(directory)
    # No file time is read here. The run's only time figure is the verifier's
    # own `search_seconds`, and a span derived from when a file happened to be
    # written measures the machine, not the search.
    found = {"directory": directory, "result": _json(directory / "result.json"),
             "certificate": None, "counterexample": None, "manifest": None, "run_dir": None,
             "attempt_history": None, "final_state": None, "artifacts_by_attempt": {}}
    certificate = directory / "Certificate"
    for name in ("Valid.lean", "Invalid.lean"):
        if (certificate / name).is_file():
            found["certificate"] = certificate / name
    if (directory / "Counterexample.json").is_file():
        found["counterexample"] = _json(directory / "Counterexample.json")
    runs = sorted((directory / "artifacts").glob("run-*")) if (directory / "artifacts").is_dir() else []
    if not runs:
        return found
    run_dir = runs[-1]
    manifest = _json(run_dir / "manifest.json")
    if not isinstance(manifest, dict):
        return found
    found["manifest"], found["run_dir"] = manifest, run_dir
    records = [record for record in manifest.get("artifacts") or [] if isinstance(record, dict)]
    for record in records:
        scope = record.get("scope") or []
        if len(scope) >= 2 and str(scope[1]).startswith("entailment-attempt:"):
            try:
                attempt = int(str(scope[1]).split(":", 1)[1])
            except ValueError:
                continue
            found["artifacts_by_attempt"].setdefault(attempt, []).append(record)
        if scope == ["root", "attempt-history"]:
            data = _artifact_bytes(run_dir, record)
            try:
                found["attempt_history"] = json.loads(data) if data else None
            except ValueError:
                pass
    frames = [record for record in records if (record.get("scope") or []) == ["root", "consultation-records"]]
    for record in reversed(frames[-3:]):
        data = _artifact_bytes(run_dir, record)
        payload = _frame_payload(data) if data else None
        event = payload.get("event") if isinstance(payload, dict) else None
        if isinstance(event, dict) and event.get("kind") == "final_owner_projection":
            projection = event.get("projection") if isinstance(event.get("projection"), dict) else {}
            state = projection.get("state")
            found["final_state"] = state if isinstance(state, dict) else None
            break
    return found


def catalog_texts(state):
    texts, protected = {}, set()
    catalog = state.get("catalog") if isinstance(state, dict) else None
    for record in (catalog.get("records") if isinstance(catalog, dict) else None) or []:
        if not isinstance(record, dict) or not isinstance(record.get("id"), int):
            continue
        text = record.get("display") or record.get("canonical_source")
        if isinstance(text, str):
            texts[record["id"]] = text
        if record.get("protected"):
            protected.add(record["id"])
    return texts, protected


def _pairs(value):
    """`[[id, level], ...]`, `[id, ...]` or `[{...}]` read as (id, detail) pairs."""
    pairs = []
    for item in value if isinstance(value, list) else []:
        if isinstance(item, list) and item and isinstance(item[0], int):
            pairs.append((item[0], item[1] if len(item) > 1 else None))
        elif isinstance(item, int):
            pairs.append((item, None))
        elif isinstance(item, dict):
            identifier = item.get("clause") if isinstance(item.get("clause"), int) else item.get("id")
            if isinstance(identifier, int):
                detail = {key: value for key, value in item.items() if key not in ("clause", "id")}
                pairs.append((identifier, detail))
    return pairs


def _standing_detail(detail, label):
    """`, last level 2` for a bare number, `, cause=refuted` for a record, else nothing."""
    if detail in (None, {}):
        return ""
    if isinstance(detail, dict):
        return ", " + ", ".join(f"{key}={value}" for key, value in detail.items()
                                if not isinstance(value, (dict, list)))
    return f", {label} {detail}"


def clause_table(verifier, texts):
    """Per clause: text, final standing and the checks the ledger recorded."""
    state = verifier.get("final_state") or {}
    history = verifier.get("attempt_history") or {}
    standing = {}
    for identifier, level in _pairs(state.get("committed")):
        standing[identifier] = f"Core, level {level}" if level is not None else "Core"
    for identifier, detail in _pairs(state.get("pending")):
        standing.setdefault(identifier, "pending" + _standing_detail(detail, "last level"))
    for identifier, detail in _pairs(state.get("dead")):
        standing.setdefault(identifier, "dead" + _standing_detail(detail, "cause"))
    checks = {}
    for row in history.get("ledger") or []:
        if not isinstance(row, dict) or row.get("row") not in (None, "attempt"):
            continue
        identifier = row.get("clause")
        outcome = row.get("outcome") if isinstance(row.get("outcome"), dict) else {}
        if not isinstance(identifier, int):
            continue
        word = str(outcome.get("kind") or "?")
        if outcome.get("reason"):
            word += f"({outcome['reason']})"
        if row.get("invalidated"):
            word += "~"
        role = str(row.get("role") or "?")[:4]
        checks.setdefault(identifier, []).append(f"L{row.get('level')} {role} {word}")
    identifiers = sorted(set(texts) | set(standing) | set(checks))
    return [(identifier, texts.get(identifier), standing.get(identifier), checks.get(identifier, []))
            for identifier in identifiers]


def termination_outcome(entry):
    """`proved`, `refuted (attempt N)` or `inconclusive (reason)` for one Term check."""
    result = entry.get("result") if isinstance(entry.get("result"), dict) else {}
    outcome = result.get("outcome") if isinstance(result.get("outcome"), dict) else {}
    if not outcome:
        return str(result.get("kind") or "recorded")
    words = str(outcome.get("kind") or "?")
    if outcome.get("reason"):
        words += f" ({outcome['reason']})"
    if outcome.get("attempt") is not None:
        words += f" (attempt {outcome['attempt']})"
    return words


def refutations(verifier):
    """Ledger rows the prover refuted, with the artifacts B kept for them."""
    history = verifier.get("attempt_history") or {}
    found = []
    for row in history.get("ledger") or []:
        outcome = row.get("outcome") if isinstance(row, dict) and isinstance(row.get("outcome"), dict) else {}
        if outcome.get("kind") == "refuted":
            attempt = outcome.get("attempt")
            artifacts = verifier.get("artifacts_by_attempt", {}).get(attempt, []) if isinstance(attempt, int) else []
            found.append({"clause": row.get("clause"), "level": row.get("level"), "role": row.get("role"),
                          "attempt": attempt, "outcome": outcome,
                          "artifacts": [(record.get("id"), record.get("kind"), record.get("relative_path"))
                                        for record in artifacts]})
    return found


# --------------------------------------------------------------------------
# Rendering


def _relative(path, start):
    try:
        return os.path.relpath(str(path), str(start))
    except ValueError:
        return str(path)


def _duration(seconds):
    if seconds is None:
        return "?"
    seconds = int(round(seconds))
    if seconds < 90:
        return f"{seconds} s"
    return f"{seconds // 60} min {seconds % 60:02d} s"


def _stamp(epoch):
    if not epoch:
        return "?"
    return datetime.datetime.fromtimestamp(epoch).strftime("%Y-%m-%d %H:%M:%S")


def _md(text):
    return str(text).replace("|", "\\|").replace("\n", " ")


def _instance_lines(relations):
    lines = []
    for name, rows in relations:
        cells = ", ".join("(" + ", ".join(str(cell) for cell in row) + ")" for row in rows[:12])
        if len(rows) > 12:
            cells += f", ... ({len(rows)} rows)"
        lines.append(f"    {name}: {{{cells}}}" if rows else f"    {name}: ∅")
    return lines


def render_example(identity, verifier, agent_inputs, run_dir, example_dir):
    """The per-input summary, from both record trees."""
    result = (verifier or {}).get("result") or {}
    status = result.get("status")
    if status is None:
        status = "running" if agent_inputs else "not started"
    lines = [f"# {identity} — {status}", ""]
    if str(status).endswith("_uncertified"):
        lines.append("The untrusted search accepted this input and its record is on disk; nothing is "
                     "certified yet. `campaign certify --run <verifier directory>` builds the "
                     "certificate from the record.")
        lines.append("")
    if result.get("record") and verifier:
        # The verifier names its records relative to the input's own
        # directory, so they are resolved against the directory the
        # `result.json` was read from, wherever that directory now is.
        record = verifier["directory"] / result["record"]
        lines.append(f"record: `{_relative(record, example_dir)}`")
    if result.get("detail"):
        lines.append(f"detail: {result['detail']}")
    if result.get("failure_kind"):
        lines.append(f"failure kind: {result['failure_kind']}")
    if verifier and verifier.get("certificate"):
        lines.append(f"certificate: `{_relative(verifier['certificate'], example_dir)}`")
    if verifier and verifier.get("counterexample") is not None:
        lines.append(f"counterexample: `{_relative(verifier['directory'] / 'Counterexample.json', example_dir)}`")
        instance = verifier["counterexample"].get("instance") if isinstance(verifier["counterexample"], dict) else None
        relations = [(str(relation.get("name")), relation.get("rows") or [])
                     for relation in (instance.get("relations") if isinstance(instance, dict) else []) or []
                     if isinstance(relation, dict)]
        if relations:
            lines.append("")
            lines.append("the checked counterexample instance:")
            lines.append("")
            lines.extend(_instance_lines(relations))
            lines.append("")
    history = (verifier or {}).get("attempt_history") or {}
    if history.get("iteration") is not None:
        lines.append(f"verifier consultations: {history.get('iteration')}"
                     + (f", failure: {history['failure']}" if history.get("failure") else ""))
    requests = [request for agent in agent_inputs for request in agent["requests"]]
    # The verifier's own search measurement is the only time this digest
    # reports. It stops when the search returns, before any record is written
    # and before certification, and the harness derives no second figure of
    # its own that a reader could mistake for it.
    if isinstance(result.get("search_seconds"), (int, float)) and not isinstance(
            result.get("search_seconds"), bool):
        lines.append(f"search time (verifier-measured, excludes certification): "
                     f"{_duration(result['search_seconds'])}")
    lines.append("")

    texts = {}
    if verifier and verifier.get("final_state"):
        texts, _ = catalog_texts(verifier["final_state"])
    for request in requests:
        for identifier, text in prompt_clauses(request.get("prompt") or {}).items():
            texts.setdefault(identifier, text)

    lines += ["## Consultations", ""]
    if not requests:
        lines += ["No agent consultation was recorded for this input.", ""]
    for agent in agent_inputs:
        if len(agent_inputs) > 1:
            lines += [f"### Endpoint `{agent['directory'].name}`", ""]
        for request in agent["requests"]:
            lines += render_request(request, texts, example_dir)

    lines += ["## Clauses, as the verifier recorded them", ""]
    if verifier and (verifier.get("attempt_history") or verifier.get("final_state")):
        table = clause_table(verifier, texts)
        if table:
            lines += ["| id | clause | final standing | checks (level, role, outcome; `~` = later invalidated) |",
                      "| --- | --- | --- | --- |"]
            for identifier, text, standing, checks in table:
                lines.append(f"| {identifier} | `{_md(text or '(text not recorded)')}` | {_md(standing or '?')} | "
                             + _md("; ".join(checks) or "none") + " |")
            lines.append("")
        else:
            lines += ["The ledger is empty: no clause check ran.", ""]
        state = verifier.get("final_state") or {}
        terminations = state.get("terminations") if isinstance(state.get("terminations"), list) else []
        if terminations:
            lines.append(f"termination checks (guard false + collapsed Core ⊨ postcondition): {len(terminations)}")
            lines.append("")
            for entry in terminations:
                if isinstance(entry, dict):
                    lines.append(f"- check {entry.get('ordinal')}: {termination_outcome(entry)}")
            lines.append("")
    else:
        lines += ["No verifier ledger was published for this input (retention was not `all`, "
                  "or the run has not settled yet).", ""]

    lines += ["## Countermodels", ""]
    found = refutations(verifier or {})
    fetched = [call for request in requests for call in request["calls"] if call["tool"] == "countermodel"]
    if not found and not fetched:
        lines += ["No check was refuted by the prover in this run, so no countermodel exists; "
                  "failed checks, if any, were inconclusive (see the ledger column).", ""]
    for item in found:
        lines.append(f"- clause {item['clause']} refuted at level {item['level']} ({item['role']}), "
                     f"attempt {item['attempt']}; verifier artifacts: "
                     + (", ".join(f"{kind} `{path}`" for _, kind, path in item["artifacts"]) or "none listed"))
    for call in fetched:
        payload = _tool_result_json(call["reply_text"])
        lines.append(f"- the agent fetched `countermodel` ({call['received']} bytes reply)"
                     + (f": {json.dumps(payload, ensure_ascii=False)[:1500]}" if payload else ""))
    if found or fetched:
        lines.append("")

    lines += ["## Files", ""]
    if verifier:
        lines.append(f"- verifier output: `{_relative(verifier['directory'], example_dir)}` "
                     "(result.json, Certificate/, artifacts/run-*/manifest.json)")
    for agent in agent_inputs:
        lines.append(f"- agent logs: `{_relative(agent['directory'], example_dir)}` "
                     "(events.jsonl, request-N/prompt.txt, native-stdout.jsonl, submissions.jsonl, mcp.jsonl)")
    lines.append("")
    return "\n".join(lines)


def render_request(request, texts, example_dir):
    prompt = request.get("prompt") or {}
    number = request.get("number")
    title = f"### Request {number}"
    if prompt.get("consultation") is not None:
        title += f" — consultation {prompt['consultation']}"
    if prompt.get("correction"):
        title += " (correction of the previous response)"
    outcome = request.get("outcome") or "no recorded outcome"
    if request.get("diagnostic"):
        outcome += f" [{request['diagnostic']}]"
    lines = [title, "", f"outcome: {outcome}"]
    # Per consultation, not per input: the harness's own estimate of how long
    # the model side of this one round took, from its log file timestamps and
    # including its own overhead. It is never summed into an input total, and
    # it is not search time — `search_seconds` is.
    if request.get("started"):
        lines[-1] += f"; started {_stamp(request['started'])}"
        if request.get("ended"):
            lines[-1] += (f", agent side {_duration(request['ended'] - request['started'])} "
                          "(harness estimate, not search time)")
    if request.get("prompt_bytes"):
        lines[-1] += f"; prompt {request['prompt_bytes']} bytes"
    if request.get("directory"):
        lines[-1] += f"; files in `{_relative(request['directory'], example_dir)}`"
    if prompt:
        push = (f"push: Core {prompt.get('core')}, pending {prompt.get('pending')}, "
                f"last round {prompt.get('last_round')}, latest: {prompt.get('latest') or '?'}")
        lines.append(push)
        last_round = prompt.get("last_round_entries") or []
        if last_round:
            lines.append("")
            lines.append("what became of the previous round's clauses:")
            lines.append("")
            for entry in last_round:
                lines.append(f"- clause {entry['id']}: {entry['outcome']} — "
                             f"`{entry.get('text') or texts.get(entry['id'], '?')}`")
        if prompt.get("correction_lines"):
            lines.append("")
            lines.append("correction: " + "; ".join(prompt["correction_lines"])[:600])
    lines.append("")
    if request.get("messages"):
        lines.append("the agent said:")
        lines.append("")
        for message in request["messages"]:
            lines.append("> " + " ".join(message.split())[:1200])
            lines.append(">")
        lines[-1:] = [""]
    calls = request.get("calls") or []
    if calls:
        lines.append("tool calls: " + ", ".join(
            f"`{call['tool']}`" + (f" ({call['error'][:80]})" if call.get("error") else "")
            for call in calls))
        lines.append("")
    for index, submission in enumerate(request.get("submissions") or [], start=1):
        verdict = submission.get("verdict") or "?"
        if submission.get("detail"):
            verdict += f" ({submission['detail']})"
        if submission.get("instance") is not None:
            lines.append(f"submission {index}: `candidate_counterexample`, verifier reply: {verdict}")
            lines.append("")
            lines.extend(_instance_lines(submission["instance"]))
        else:
            lines.append(f"submission {index}: {len(submission['clauses'])} clauses"
                         + (f", {submission['dropped']} dropped" if submission.get("dropped") else "")
                         + f", verifier reply: {verdict}")
            lines.append("")
            for clause in submission["clauses"]:
                lines.append(f"    {clause}")
        lines.append("")
    if request.get("rejections"):
        lines.append("refusals the agent received: " + "; ".join(request["rejections"])[:800])
        lines.append("")
    return lines


def _link(link, target):
    """A relative symlink, replaced only if it is already a symlink."""
    link = Path(link)
    if link.is_symlink():
        link.unlink()
    elif link.exists():
        return
    try:
        link.symlink_to(os.path.relpath(str(target), str(link.parent)), target_is_directory=True)
    except OSError:
        pass


def locate(run_dir, *, verifier_dir=None, agent_dir=None):
    """The verifier tree, the agent tree and the directory the digest goes to."""
    run_dir = Path(run_dir).resolve()
    if verifier_dir is not None or agent_dir is not None:
        return (Path(verifier_dir).resolve() if verifier_dir else None,
                Path(agent_dir).resolve() if agent_dir else None, run_dir)
    if (run_dir / VERIFIER_DIR).is_dir() or (run_dir / AGENT_DIR).is_dir() or (run_dir / RUN_FILE).is_file():
        verifier = run_dir / VERIFIER_DIR
        agent = run_dir / AGENT_DIR
        return (verifier if verifier.is_dir() else None, agent if agent.is_dir() else None, run_dir)
    artifacts = run_dir.parent.parent
    if (run_dir / "campaign-settings.json").is_file():
        sibling = artifacts / "agent-logs" / run_dir.name
        target = artifacts / "runs" / run_dir.name
    elif (run_dir / "launcher.jsonl").is_file() or list(run_dir.glob("*/launcher.jsonl")):
        sibling = artifacts / "campaigns" / run_dir.name
        target = artifacts / "runs" / run_dir.name
        run_dir, sibling = sibling, run_dir
    else:
        raise SpecError(f"{run_dir} is neither a run directory, a campaign directory nor an agent log directory")
    target.mkdir(parents=True, exist_ok=True)
    if run_dir.is_dir():
        _link(target / VERIFIER_DIR, run_dir)
    if sibling.is_dir():
        _link(target / AGENT_DIR, sibling)
    return (run_dir if run_dir.is_dir() else None, sibling if sibling.is_dir() else None, target)


def write_report(run_dir, *, verifier_dir=None, agent_dir=None):
    """Write progress.md, progress.json and examples/<ID>/summary.md; return progress.md."""
    verifier_root, agent_root, target = locate(run_dir, verifier_dir=verifier_dir, agent_dir=agent_dir)
    record = _json(target / RUN_FILE) or {}
    settings = _json(verifier_root / "campaign-settings.json") if verifier_root else None
    summary = _json(verifier_root / "summary.json") if verifier_root else None
    inputs = []
    if isinstance(settings, dict) and isinstance(settings.get("inputs"), list):
        inputs = [item for item in settings["inputs"] if isinstance(item, str)]
    elif isinstance(record.get("spec"), dict):
        inputs = [item for item in record["spec"].get("inputs") or [] if isinstance(item, str)]
    agents = find_agent_inputs(agent_root) if agent_root else []
    by_identity = {}
    for agent in agents:
        by_identity.setdefault(agent["identity"] or "(unidentified)", []).append(agent)
    if verifier_root:
        for child in sorted(verifier_root.iterdir()):
            if child.is_dir() and (child / "result.json").is_file() and child.name not in inputs:
                inputs.append(child.name)
    for identity in by_identity:
        if identity not in inputs and identity != "(unidentified)":
            inputs.append(identity)
    examples = target / EXAMPLES_DIR
    examples.mkdir(exist_ok=True)
    rows = []
    for identity in inputs:
        verifier = None
        if verifier_root and (verifier_root / identity).is_dir():
            verifier = read_verifier_input(verifier_root / identity)
        agent_inputs = by_identity.get(identity, [])
        example_dir = examples / identity
        example_dir.mkdir(exist_ok=True)
        (example_dir / SUMMARY_FILE).write_text(
            render_example(identity, verifier, agent_inputs, target, example_dir), encoding="utf-8")
        if verifier:
            _link(example_dir / VERIFIER_DIR, verifier["directory"])
        if len(agent_inputs) == 1:
            _link(example_dir / AGENT_DIR, agent_inputs[0]["directory"])
        row = progress_row(identity, verifier, agent_inputs)
        if row["rounds"]:
            _write_json(example_dir / ROUNDS_FILE, {
                "input": identity, "status": row["status"],
                "consultations": row["consultations"],
                "search_seconds": row["search_seconds"],
                "core": row["core"], "pending": row["pending"], "dead": row["dead"],
                "clauses_submitted": row["clauses_submitted"],
                "clauses_dropped": row["clauses_dropped"],
                "certificate": row["certificate"],
                "round_seconds_meaning": ROUND_SECONDS_MEANING,
                "rounds": row["rounds"],
            })
        rows.append(row)
    unidentified = by_identity.get("(unidentified)", [])
    # Whatever `run.json` already recorded, which is repo-relative or
    # placeholdered; there is no safe absolute form of `target` to fall back
    # to; a run directory built without `run.json` (the old campaign layout)
    # reports this as unknown rather than as an absolute path.
    progress = {"schema_version": 1, "run_directory": record.get("run_directory"), "generated_at": _now(),
                "status": record.get("status") or ("finished" if summary else "running"),
                "exit_code": record.get("exit_code"),
                "all_certified": summary.get("all_certified") if isinstance(summary, dict) else None,
                # Whether every search reached a verdict is a different
                # question from whether every verdict was certified; a
                # deferred run answers the first yes long before the second.
                "all_accepted": summary.get("all_accepted") if isinstance(summary, dict) else None,
                "unrun_inputs": summary.get("unrun_inputs") if isinstance(summary, dict) else None,
                "inputs": rows}
    _write_json(target / PROGRESS_JSON, progress)
    if record.get("spec", {}).get("token_usage") == "codex-rollout":
        write_usage_report(target, model=record["spec"].get("model"))
    (target / PROGRESS_FILE).write_text(
        render_progress(target, record, settings, summary, rows, unidentified), encoding="utf-8")
    return target / PROGRESS_FILE


def progress_row(identity, verifier, agent_inputs):
    result = (verifier or {}).get("result") or {}
    requests = [request for agent in agent_inputs for request in agent["requests"]]
    submitted = sum(len(item["clauses"]) for request in requests for item in request["submissions"])
    state = (verifier or {}).get("final_state") or {}
    core = pending = dead = None
    if state:
        core, pending, dead = (len(_pairs(state.get(key))) for key in ("committed", "pending", "dead"))
    elif requests:
        last = requests[-1].get("prompt") or {}
        core, pending = last.get("core"), last.get("pending")
    status = result.get("status") or ("running" if agent_inputs else "not started")
    # Layer B's own measurement, on a monotonic clock around the search loop,
    # read straight from result.json. It is the run's only time figure: the
    # harness derives none of its own from file timestamps, because a second
    # figure beside this one is read as a rival measure of the same thing. A
    # run directory that predates the measurement reports it absent.
    search_seconds = result.get("search_seconds")
    if not isinstance(search_seconds, (int, float)) or isinstance(search_seconds, bool):
        search_seconds = None
    return {"input": identity, "status": status, "detail": result.get("detail"),
            "consultations": len(requests), "clauses_submitted": submitted,
            "core": core, "pending": pending, "dead": dead,
            "certificate": str(verifier["certificate"]) if verifier and verifier.get("certificate") else None,
            "search_seconds": search_seconds,
            "final_state_known": bool(state),
            "rounds": round_stats(requests),
            "clauses_dropped": sum(item["dropped"] for request in requests
                                   for item in request["submissions"])}


def round_stats(requests):
    """Per-round breakdown extracted from the agent's request records.

    `agent_seconds` and `verifier_seconds` split one consultation between the
    model and the verifier: they are this harness's own estimate, taken from
    the timestamps of its log files, not a measurement either side made.
    `agent_seconds` spans the consultation's own request records and so
    carries the harness's overhead with it; `verifier_seconds` is the gap to
    the next request, and is null on the last round because no next request
    bounds it. Neither is search time, and no total is formed from them: the
    search time of an input is the verifier's `search_seconds` alone. The
    split is kept because it is the only model-versus-verifier division an
    experiment records.
    """
    rounds = []
    for index, request in enumerate(requests):
        prompt = request.get("prompt") or {}
        proposed = sum(len(item["clauses"]) for item in request["submissions"])
        dropped = sum(item["dropped"] for item in request["submissions"])
        agent_seconds = None
        if request.get("started") and request.get("ended"):
            agent_seconds = round(request["ended"] - request["started"], 2)
        verifier_seconds = None
        if index + 1 < len(requests) and request.get("ended") and requests[index + 1].get("started"):
            verifier_seconds = round(requests[index + 1]["started"] - request["ended"], 2)
        rounds.append({
            "round": index + 1,
            "agent_seconds": agent_seconds,
            "verifier_seconds": verifier_seconds,
            "clauses_proposed": proposed,
            "clauses_dropped": dropped,
            "core": prompt.get("core"),
            "pending": prompt.get("pending"),
            "latest": prompt.get("latest"),
        })
    return rounds


def render_progress(target, record, settings, summary, rows, unidentified):
    spec = record.get("spec") if isinstance(record.get("spec"), dict) else {}
    controls = settings.get("controls") if isinstance(settings, dict) else {}
    controls = controls if isinstance(controls, dict) else {}
    lines = [f"# Run `{target.name}`", ""]
    if spec:
        lines.append(f"model: `{spec.get('model')}` ({spec.get('provider')}, effort {spec.get('reasoning_effort') or 'default'}, "
                     f"isolation {spec.get('isolation')})")
    elif isinstance(settings, dict):
        proposer = settings.get("proposer") if isinstance(settings.get("proposer"), dict) else {}
        arguments = proposer.get("arguments") if isinstance(proposer.get("arguments"), list) else []
        pairs = {arguments[index]: arguments[index + 1] for index in range(len(arguments) - 1)
                 if str(arguments[index]).startswith("--")}
        lines.append(f"model: `{pairs.get('--model', '?')}` ({pairs.get('--provider', '?')}, effort "
                     f"{pairs.get('--reasoning-effort') or 'default'}, isolation {pairs.get('--isolation', '?')})")
    if controls:
        lines.append(f"limits: search {controls.get('search_limit_seconds')} s, certification "
                     f"{controls.get('certification_limit_seconds')} s, iterations "
                     f"{controls.get('iteration_limit') or 'unbounded'}, workers {controls.get('workers')}")
    if record.get("started_at"):
        lines.append(f"started {record['started_at']}"
                     + (f", finished {record['finished_at']}" if record.get("finished_at") else " (running)")
                     + (f", exit code {record['exit_code']}" if record.get("exit_code") is not None else ""))
    if record.get("git_revision"):
        lines.append(f"revision: `{record['git_revision']}`")
    if spec.get("notes"):
        lines.append(f"notes: {spec['notes']}")
    if isinstance(summary, dict):
        lines.append(f"verifier summary: all_accepted={summary.get('all_accepted')}, "
                     f"all_certified={summary.get('all_certified')}, interrupted="
                     f"{summary.get('interrupted')}, unrun={summary.get('unrun_inputs') or []}")
    else:
        lines.append("verifier summary: not written yet (the campaign has not finished)")
    if any(str(row["status"]).endswith("_uncertified") for row in rows):
        lines.append("Inputs reading `valid_uncertified` or `invalid_uncertified` were accepted by the "
                     "untrusted search and are not yet certified: their record is on disk and "
                     "`campaign certify --run <verifier directory>` finishes them.")
    lines += ["", "| input | status | rounds | proposed | dropped | Core | pending | dead | search | "
              "detail |",
              "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
    for row in rows:
        counts = [row["core"], row["pending"], row["dead"]]
        marks = ["?" if value is None else str(value) for value in counts]
        if not row["final_state_known"] and row["core"] is not None:
            marks[0] += "*"
        lines.append(f"| [{row['input']}]({EXAMPLES_DIR}/{row['input']}/{SUMMARY_FILE}) | {row['status']} | "
                     f"{row['consultations']} | {row['clauses_submitted']} | {row['clauses_dropped']} | "
                     f"{marks[0]} | {marks[1]} | {marks[2]} | "
                     f"{_duration(row['search_seconds']) if row['search_seconds'] is not None else '?'} | "
                     f"{_md((row['detail'] or '')[:160])} |")
    lines.append("")
    lines.append("`search` is the only time here, and it is the verifier's own measurement of the untrusted "
                 "search, on a monotonic clock around the search loop: it excludes runner and Lean worker "
                 "startup and all certification. The harness reports no second figure of its own. `?` means "
                 "the run directory predates that measurement, not that the search took no time.")
    lines.append("Core/pending/dead come from the verifier's final state; a `*` marks a count read from the "
                 "last prompt instead, because the run has not settled or was not recorded.")
    if unidentified:
        lines.append("")
        lines.append("agent log directories no push identified: " + ", ".join(
            f"`{agent['directory'].name}`" for agent in unidentified))
    lines.append("")
    return "\n".join(lines)


# --------------------------------------------------------------------------
# Entry


def main(argv=None):
    parser = argparse.ArgumentParser(prog="python -m agent_houdini experiment", allow_abbrev=False,
                                     description="Run a campaign from a spec file, or rewrite a run's digest.")
    commands = parser.add_subparsers(dest="command", required=True)
    runner = commands.add_parser("run", help="start a campaign from SPEC.json into a fresh run directory")
    runner.add_argument("spec", type=Path)
    runner.add_argument("--dry-run", action="store_true", help="print the run directory and command only")
    pool = commands.add_parser("pool", help="run each selected input once through a refillable campaign pool")
    pool.add_argument("spec", type=Path)
    pool.add_argument("--jobs", type=int, default=4, help="simultaneous single-input campaigns (default: 4)")
    pool.add_argument("--auth-root", type=Path, help="private root containing separately logged-in worker-1..N homes")
    pool.add_argument("--parallel", default="parallel", help="GNU Parallel executable")
    pool.add_argument("--dry-run", action="store_true", help="show the queue without creating files or launching work")
    reporter = commands.add_parser("report", help="write progress.md and examples/<ID>/summary.md for RUN_DIR")
    reporter.add_argument("run_dir", type=Path)
    reporter.add_argument("--verifier-dir", type=Path, help="B's campaign directory, when not under RUN_DIR")
    reporter.add_argument("--agent-dir", type=Path, help="C's log directory, when not under RUN_DIR")
    parsed = parser.parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if parsed.command == "run":
            return run(parsed.spec, dry_run=parsed.dry_run)
        if parsed.command == "pool":
            from .experiment_pool import run_pool

            return run_pool(parsed.spec, jobs=parsed.jobs, dry_run=parsed.dry_run,
                            auth_root=parsed.auth_root, parallel=parsed.parallel)
        progress = write_report(parsed.run_dir, verifier_dir=parsed.verifier_dir, agent_dir=parsed.agent_dir)
        print(f"experiment report: {progress}")
        return 0
    except SpecError as error:
        print(f"experiment: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
