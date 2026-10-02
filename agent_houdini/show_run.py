# Author: Fangzhu Shen
"""Offline reader for one recorded C run: `python3 -m agent_houdini show-run DIR`.

The owner of a run should not have to open JSONL to learn what happened in it.
This prints one block per consultation — outcome, prompt size, the tool calls
the agent made, what it submitted and what B answered, and, for a failure, the
reason with the side that ended the exchange and the CLI's last event.

It reads only C's own log directory. It contacts nothing, changes nothing and
reports what was retained, including a run recorded before retention existed.
"""

import argparse
import json
from pathlib import Path
import sys

from .run_records import MCP_FILE, SUBMISSIONS_FILE, read_entries


MAXIMUM_ENTRIES = 20000
MAXIMUM_INPUTS = 256
DETAIL_FIELDS = ("side", "phase", "error_class", "reason", "relay_diagnostic",
                 "last_mcp_method", "last_mcp_tool", "mcp_awaiting_reply",
                 "cli_last_event", "cli_last_event_subtype", "cli_stdout_bytes")


def find_inputs(directory):
    """Every per-input events log at or under the given path, in order."""
    directory = Path(directory)
    if directory.is_file() and directory.name.endswith(".jsonl"):
        return [directory]
    if not directory.is_dir():
        return []
    found = []
    if (directory / "events.jsonl").is_file():
        found.append(directory / "events.jsonl")
    for path in sorted(directory.glob("*/events.jsonl")):
        found.append(path)
    for path in sorted(directory.glob("*/*/events.jsonl")):
        found.append(path)
    return sorted(dict.fromkeys(found))[:MAXIMUM_INPUTS]


def _size(value):
    if type(value) is not int or value < 0:
        return "?"
    if value < 1024:
        return f"{value} B"
    if value < 1024 * 1024:
        return f"{value / 1024:.1f} KiB"
    return f"{value / (1024 * 1024):.1f} MiB"


def _fields(event):
    fields = event.get("fields")
    return fields if isinstance(fields, dict) else {}


def group_by_request(events):
    """Order the per-request events; endpoint-wide events keep key None."""
    groups, current = {}, None
    for event in events:
        kind, fields = event.get("kind"), _fields(event)
        identifier = fields.get("request_id")
        if kind == "request_started":
            current = identifier
        key = identifier if identifier is not None else current
        groups.setdefault(key, []).append(event)
        if kind == "request_outcome":
            current = None
    return groups


def _tool_calls(entries):
    """Pair the retained MCP requests with their replies, in call order."""
    replies = {entry.get("exchange"): entry for entry in entries
               if entry.get("direction") == "reply"}
    calls = []
    for entry in entries:
        if entry.get("direction") != "request" or entry.get("method") != "tools/call":
            continue
        reply = replies.get(entry.get("exchange"), {})
        calls.append((entry.get("tool") or "?", entry.get("bytes"), reply.get("bytes"),
                      reply.get("error")))
    return calls


def describe_request(out, identifier, events, directory):
    started = next((event for event in events if event.get("kind") == "request_started"), None)
    outcome = next((event for event in events if event.get("kind") == "request_outcome"), None)
    capture = next((event for event in events if event.get("kind") == "native_capture"), None)
    failures = [event for event in events
                if event.get("kind") in ("mcp_failure", "native_bridge_failure",
                                         "native_failure", "relay_diagnostic",
                                         "endpoint_failure")]
    fields = _fields(outcome) if outcome else {}
    label = fields.get("outcome", "no recorded outcome")
    code = fields.get("diagnostic_code")
    out(f"  request {identifier}: {label}" + (f" [{code}]" if code else ""))
    if started:
        begun = _fields(started)
        out(f"    prompt: {_size(begun.get('prompt_bytes'))}"
            f" sha256={str(begun.get('prompt_sha256'))[:16]}"
            f" tools={len(begun.get('tool_names') or [])}")
    if capture:
        counts = _fields(capture).get("counts") or {}
        events_seen = counts.get("events") or {}
        out(f"    cli: {_size(counts.get('stdout_bytes'))} stdout, events "
            + (", ".join(f"{name}x{count}" for name, count in sorted(events_seen.items()))
               or "none")
            + (f", last={counts.get('last_event')}" if counts.get("last_event") else ""))
        for text in (counts.get("provider_errors") or [])[:4]:
            out(f"    cli error: {text}")
        if counts.get("startup_failure"):
            out(f"    startup refused: {counts['startup_failure']}")
    retained = directory / str(fields.get("directory")) if fields.get("directory") else None
    if retained is not None and retained.is_dir():
        held = fields.get("files") or {}
        listed = ", ".join(f"{name} {_size((held.get(name) or {}).get('bytes'))}"
                           + (" (truncated)" if (held.get(name) or {}).get("truncated") else "")
                           for name in sorted(held))
        out("    retained: " + (listed or "(empty)"))
        calls = _tool_calls(read_entries(retained / MCP_FILE, maximum=MAXIMUM_ENTRIES))
        for name, request_bytes, reply_bytes, error in calls:
            out(f"      tool {name}: sent {_size(request_bytes)}, reply "
                + ("none" if reply_bytes is None else _size(reply_bytes))
                + (f", error {error}" if error else ""))
        if not calls:
            out("      no MCP tool calls retained")
        for entry in read_entries(retained / SUBMISSIONS_FILE, maximum=MAXIMUM_ENTRIES):
            out(f"      submission {entry.get('submission')}: "
                f"{_size(entry.get('payload_bytes'))} -> {entry.get('verdict')}"
                + (f" ({entry.get('detail')})" if entry.get("detail") else ""))
    elif fields.get("directory"):
        out(f"    retained: directory {fields['directory']} is missing")
    else:
        out("    retained: nothing (retention was not set to all for this run)")
    for event in failures:
        detail = _fields(event)
        parts = [f"{name}={detail[name]}" for name in DETAIL_FIELDS if detail.get(name) is not None]
        out(f"    {event.get('kind')}: " + ("; ".join(parts) if parts
                                            else json.dumps(detail, default=str)[:400]))


def describe_input(out, path):
    events = read_entries(path, maximum=MAXIMUM_ENTRIES)
    out(f"input {path.parent.name} ({path})")
    configuration = next((event for event in events
                          if event.get("kind") == "endpoint_configuration"), None)
    if configuration:
        fields = _fields(configuration)
        selection = fields.get("selection") or {}
        out(f"  provider={selection.get('provider')} model={selection.get('model')}"
            f" effort={selection.get('reasoning_effort')} isolation={fields.get('isolation')}"
            f" retention={fields.get('retention', 'events (not recorded)')}")
    groups = group_by_request(events)
    requests = sorted(key for key in groups if key is not None)
    for identifier in requests:
        describe_request(out, identifier, groups[identifier], path.parent)
    if not requests:
        out("  no consultations recorded")
    traffic = next((event for event in events if event.get("kind") == "agent_traffic"), None)
    if traffic:
        fields = _fields(traffic)
        out(f"  traffic: {_size(fields.get('bytes'))} in {fields.get('messages')} messages")
    out("")


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="python -m agent_houdini show-run", allow_abbrev=False, description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("directory", type=Path,
                        help="a C agent log directory, an input directory, or one events.jsonl")
    parsed = parser.parse_args(sys.argv[1:] if argv is None else argv)
    inputs = find_inputs(parsed.directory)
    if not inputs:
        print(f"show-run: no events.jsonl under {parsed.directory}", file=sys.stderr)
        return 1
    for path in inputs:
        describe_input(print, path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
