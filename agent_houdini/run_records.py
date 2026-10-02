# Author: Fangzhu Shen
"""C-owned per-consultation retention of what a real run actually exchanged.

A run that reaches the model and then fails leaves nothing behind unless the
bytes are kept while they pass through. This module keeps them: the rendered
prompt, the provider CLI's own stream, every MCP line the relay carried and
every submission payload, each under its own generous byte cap and each written
through the same credential redaction the argv provenance uses.

These are C diagnostics. They are never verifier evidence, never a proof record
and never an input to admission: nothing here is read back into a consultation.
Retention is off by default; `--agent-retention all` turns it on, and the
metadata this module tracks for failure reasons is collected either way.
"""

from collections.abc import Mapping
import json
import os
from pathlib import Path
import re
import time

from .agent_log import bounded_redacted_diagnostic


RETENTION_MODES = ("events", "all")
STREAM_BYTES = 8 * 1024 * 1024
STDERR_BYTES = 1024 * 1024
SUBMISSION_BYTES = 4 * 1024 * 1024
LINE_BYTES = 1024 * 1024
ENTRY_TEXT_BYTES = 256 * 1024
PARSE_BYTES = 4 * 1024 * 1024
TRUNCATED = "[truncated: C retention cap reached]"

PROMPT_FILE = "prompt.txt"
STDOUT_FILE = "native-stdout.jsonl"
STDERR_FILE = "native-stderr.txt"
DEBUG_FILE = "native-debug.txt"
DEBUG_BYTES = 4 * 1024 * 1024
MCP_FILE = "mcp.jsonl"
SUBMISSIONS_FILE = "submissions.jsonl"
USAGE_FILE = "usage.jsonl"
# The temporary name an input directory carries until the first push names the
# task it serves; `RunRecords.identify` replaces it with the task's canonical id.
UNNAMED_PREFIX = "input-"
IDENTITY_PATTERN = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,63}")
IDENTITY_ATTEMPTS = 1000


def redacted_line(text, maximum=LINE_BYTES):
    """One retained line, credential-withheld and bounded like a diagnostic."""
    return bounded_redacted_diagnostic(text, maximum)


class BoundedFile:
    """Append-only capped file; one truncation marker replaces the overflow."""

    def __init__(self, directory, name, maximum):
        self.name = name
        self.maximum = maximum
        self.written = 0
        self.truncated = False
        self.failed = False
        self.pending = bytearray()
        descriptor = os.open(Path(directory) / name,
                             os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC,
                             0o600)
        self._file = os.fdopen(descriptor, "wb")

    def _raw(self, data):
        if self._file.closed or self.failed:
            return
        if self.truncated:
            return
        room = self.maximum - self.written
        if len(data) > room:
            data, self.truncated = data[:max(0, room)], True
        try:
            self._file.write(data)
            if self.truncated:
                self._file.write(("\n" + TRUNCATED + "\n").encode())
            self._file.flush()
        except OSError:
            self.failed = True
            return
        self.written += len(data)

    def line(self, text):
        """Write one redacted line; foreign text never reaches the file raw."""
        self._raw((redacted_line(text) + "\n").encode("utf-8", errors="replace"))

    def chunk(self, data):
        """Tee a byte stream, redacting each complete line as it completes."""
        if self.truncated or self.failed:
            return
        for byte in data:
            if byte == 10:
                self.line(bytes(self.pending).decode("utf-8", errors="replace"))
                self.pending.clear()
            elif len(self.pending) < LINE_BYTES:
                self.pending.append(byte)

    def close(self):
        if self.pending:
            self.line(bytes(self.pending).decode("utf-8", errors="replace"))
            self.pending.clear()
        if not self._file.closed:
            try:
                self._file.close()
            except OSError:
                self.failed = True

    def summary(self):
        return {"bytes": self.written, "truncated": self.truncated, "write_failed": self.failed}


def _envelope(line):
    """Best-effort C-local view of one MCP line; never a semantic check."""
    if len(line) > PARSE_BYTES:
        return None
    try:
        value = json.loads(line.decode("utf-8"))
    except (ValueError, UnicodeError):
        return None
    return value if isinstance(value, dict) else None


def _tool(value):
    params = value.get("params") if isinstance(value, dict) else None
    name = params.get("name") if isinstance(params, dict) else None
    return name if isinstance(name, str) else None


def _reply_error(value):
    if not isinstance(value, dict):
        return None
    error = value.get("error")
    if isinstance(error, dict):
        return redacted_line(str(error.get("message") or "error"), 1024)
    result = value.get("result")
    if isinstance(result, dict) and result.get("isError"):
        content = result.get("content")
        text = ""
        if isinstance(content, list) and content and isinstance(content[0], dict):
            text = str(content[0].get("text") or "")
        return redacted_line(text or "tool reported isError", 1024)
    return None


class ConsultationRecord:
    """One consultation's retained files and the metadata a failure needs.

    Without a directory this keeps only the metadata: the exchange counts and
    the last MCP method in flight, which every failure reason reports whether
    or not the owner asked for retained bytes.
    """

    def __init__(self, request_id, directory=None):
        self.request_id = request_id
        self.directory = None if directory is None else Path(directory)
        self.started = time.monotonic()
        self.exchanges = 0
        self.awaiting_reply = False
        self.last_method = None
        self.last_tool = None
        self.last_request_bytes = 0
        self.last_reply_bytes = 0
        self.submissions = 0
        self.prompt_bytes = 0
        self._files = {}
        self._pending = None

    def _file(self, name, maximum):
        if self.directory is None:
            return None
        existing = self._files.get(name)
        if existing is None:
            try:
                existing = self._files[name] = BoundedFile(self.directory, name, maximum)
            except OSError:
                self._files[name] = False
                return None
        return existing or None

    def prompt(self, data):
        self.prompt_bytes = len(data)
        handle = self._file(PROMPT_FILE, STREAM_BYTES)
        if handle is not None:
            handle.chunk(data)
            handle.close()

    def stdout(self, data):
        handle = self._file(STDOUT_FILE, STREAM_BYTES)
        if handle is not None:
            handle.chunk(data)

    def usage(self, value):
        """Numeric-only native usage snapshots, never prompts or credentials."""
        handle = self._file(USAGE_FILE, STREAM_BYTES)
        if handle is not None:
            handle.line(json.dumps(value, sort_keys=True))

    def stderr(self, data):
        handle = self._file(STDERR_FILE, STDERR_BYTES)
        if handle is not None:
            handle.chunk(data)
            handle.close()

    def native_debug(self, path):
        """Copy the CLI's own debug log if it wrote one, bounded and redacted.

        The provider CLI is launched with this file as its debug log only when
        retention is on; the copy is made after the turn has been joined, so
        the file is complete, and the source stays in C's scratch.
        """
        path = Path(path)
        if self.directory is None or not path.is_file():
            return
        handle = self._file(DEBUG_FILE, DEBUG_BYTES)
        if handle is None:
            return
        try:
            with open(path, "rb") as source:
                while not handle.truncated and not handle.failed:
                    data = source.read(65536)
                    if not data:
                        break
                    handle.chunk(data)
        except OSError:
            pass
        handle.close()

    def _entry(self, handle, fields):
        if handle is None:
            return
        try:
            handle.line(json.dumps(fields, ensure_ascii=False, allow_nan=False,
                                   separators=(",", ":"), default=str))
        except (TypeError, ValueError):
            handle.line('{"entry":"unencodable"}')

    def mcp_request(self, line):
        """Record one complete MCP line the relay carried to the coordinator."""
        value = _envelope(line)
        method = value.get("method") if value else None
        self.exchanges += 1
        self.awaiting_reply = True
        self.last_method = method if isinstance(method, str) else None
        self.last_tool = _tool(value) if value else None
        self.last_request_bytes = len(line)
        self._pending = (self.exchanges, self.last_method, self.last_tool, value)
        self._entry(self._file(MCP_FILE, STREAM_BYTES), {
            "exchange": self.exchanges, "direction": "request", "time": round(time.time(), 3),
            "elapsed": round(time.monotonic() - self.started, 6), "bytes": len(line),
            "method": self.last_method, "tool": self.last_tool,
            "text": redacted_line(line.decode("utf-8", errors="replace"), ENTRY_TEXT_BYTES)})

    def mcp_reply(self, line):
        """Record the coordinator's reply, or a notification's absent reply."""
        self.awaiting_reply = False
        self.last_reply_bytes = 0 if line is None else len(line)
        value = None if line is None else _envelope(line)
        self._entry(self._file(MCP_FILE, STREAM_BYTES), {
            "exchange": self.exchanges, "direction": "reply", "time": round(time.time(), 3),
            "elapsed": round(time.monotonic() - self.started, 6),
            "bytes": self.last_reply_bytes, "method": self.last_method, "tool": self.last_tool,
            "error": None if value is None else _reply_error(value),
            "text": "" if line is None else redacted_line(
                line.decode("utf-8", errors="replace"), ENTRY_TEXT_BYTES)})
        pending = self._pending
        self._pending = None
        if pending is not None and pending[2] == "submit" and pending[3] is not None:
            self._submission(pending, value, self.last_reply_bytes)

    def _submission(self, pending, reply, reply_bytes):
        """The payload a submit call carried, and what became of it.

        `forwarded` separates the two outcomes an analyst counts differently:
        a payload handed to B, which spends the consultation's one round, and
        one the coordinator refused locally, which never left this process and
        spent nothing. Only the first is a round.
        """
        params = pending[3].get("params")
        arguments = params.get("arguments") if isinstance(params, dict) else None
        payload = arguments.get("payload") if isinstance(arguments, dict) else None
        if not isinstance(payload, str):
            return
        self.submissions += 1
        error = None if reply is None else _reply_error(reply)
        forwarded = reply is not None and error is None
        self._entry(self._file(SUBMISSIONS_FILE, SUBMISSION_BYTES), {
            "submission": self.submissions, "exchange": pending[0],
            "time": round(time.time(), 3), "payload_bytes": len(payload.encode("utf-8")),
            "accepted": forwarded, "forwarded": forwarded,
            "verdict": "receipt" if forwarded else
                       ("refused_locally" if error is not None else "no_reply"),
            "detail": error, "reply_bytes": reply_bytes,
            "payload": redacted_line(payload, ENTRY_TEXT_BYTES)})

    def exchange_fields(self):
        """What a failure reason says about the MCP traffic at the failure."""
        return {"mcp_exchanges": self.exchanges, "mcp_awaiting_reply": self.awaiting_reply,
                "last_mcp_method": self.last_method, "last_mcp_tool": self.last_tool,
                "last_mcp_request_bytes": self.last_request_bytes,
                "last_mcp_reply_bytes": self.last_reply_bytes}

    def close(self):
        """Close every retained file and describe what the directory holds."""
        for handle in self._files.values():
            if handle:
                handle.close()
        if self.directory is None:
            return {}
        return {"directory": self.directory.name,
                "files": {name: handle.summary() for name, handle in sorted(self._files.items())
                          if handle}}


class RunRecords:
    """Per-input retention policy and the consultation directories under it."""

    def __init__(self, directory, retention="events"):
        if retention not in RETENTION_MODES:
            raise ValueError("retention must be events or all")
        self.retention = retention
        self.directory = Path(directory)

    def identify(self, canonical_id):
        """Rename this input's temporary `input-*` directory after its task.

        B starts one C endpoint per input and tells it nothing about which
        input that is; the first push does, in its task identity. The
        directory is therefore created under a temporary name and renamed
        here, once, to the canonical id (`Example0001`). A later endpoint for
        the same input -- B's recovery after a failed one -- finds the name
        taken and becomes `Example0001-2`, and so on. An unusable id, a
        directory that was never C's temporary one, or a rename the host
        refuses leaves the temporary name in place; nothing else changes and
        the open event log keeps writing through its descriptor.
        """
        if not isinstance(canonical_id, str) or not IDENTITY_PATTERN.fullmatch(canonical_id):
            return None
        directory = self.directory
        if not directory.name.startswith(UNNAMED_PREFIX) or not directory.is_dir():
            return None
        for attempt in range(1, IDENTITY_ATTEMPTS + 1):
            target = directory.parent / (canonical_id if attempt == 1 else f"{canonical_id}-{attempt}")
            if target.exists() or target.is_symlink():
                continue
            try:
                os.rename(directory, target)
            except OSError:
                return None
            self.directory = target
            return target.name
        return None

    def consultation(self, request_id):
        if self.retention != "all":
            return ConsultationRecord(request_id)
        name = "request-" + str(request_id if type(request_id) is int else 0)
        target = self.directory / name
        try:
            target.mkdir(mode=0o700)
        except OSError:
            return ConsultationRecord(request_id)
        return ConsultationRecord(request_id, target)


def null_records():
    """Metadata-only records for a caller that configured no log directory."""
    return RunRecords(Path("."), "events")


def read_entries(path, *, maximum=None):
    """Read one retained JSONL file offline; a bad line becomes a marker."""
    entries = []
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as source:
            for line in source:
                line = line.strip()
                if not line:
                    continue
                if maximum is not None and len(entries) >= maximum:
                    break
                try:
                    value = json.loads(line)
                except ValueError:
                    value = {"entry": "unparsed", "text": line[:200]}
                entries.append(value if isinstance(value, Mapping) else {"entry": "unparsed"})
    except OSError:
        return []
    return entries
