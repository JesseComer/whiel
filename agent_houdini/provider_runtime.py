# Author: Fangzhu Shen
"""C-owned native provider supervision and bounded output summaries."""

from dataclasses import asdict, dataclass
import hashlib
import os
from pathlib import Path
import stat
from types import MappingProxyType
from collections.abc import Mapping

from .json_wire import decode
from .agent_log import WITHHELD, bounded_redacted_diagnostic
from .process_tree import OwnedProcess


DIAGNOSTIC_BYTES = 64 * 1024
CAPTURE_DIAGNOSTIC_BYTES = 24 * 1024
STDERR_EXCERPT_BYTES = 8 * 1024
IDENTITY_TEXT_BYTES = 512
UNKNOWN_VERSION = "unknown"
VERSION_TEXT_BYTES = 256


IDENTITY_PATH_FIELDS = ("executable", "configuration_directory")


def redacted_selection(selection):
    """`selection` (the decoded, not-yet-verified provider choice) with its
    executable path reduced to a file name, for a log record that is read on
    a machine other than the one that ran the campaign.

    `native_identity_fields` makes the analogous reduction for a *verified*
    identity; an endpoint or launcher that has not verified yet (or logs its
    own configuration before or beside that verification) redacts the same
    field here, so no call site is left recording the full path.
    """
    if isinstance(selection, dict) and isinstance(selection.get("executable"), str):
        return dict(selection, executable=Path(selection["executable"]).name)
    return selection


def native_identity_fields(identity):
    """Bounded C provenance from the selection, never auth or model payloads.

    `executable` and `configuration_directory` are resolved absolute paths on
    the machine that ran the campaign; once the ordinary credential redaction
    and byte bound below have cleared a field, a path field is reduced once
    more to its own file name, never the directory that led to it, so this
    record carries no home directory or user name when it is read on a
    different machine.
    """
    fields = {}
    for name, value in asdict(identity).items():
        if type(value) is int:
            fields[name] = value
            continue
        text = bounded_redacted_diagnostic(str(value), IDENTITY_TEXT_BYTES)
        if name in IDENTITY_PATH_FIELDS and value is not None and text != WITHHELD:
            text = bounded_redacted_diagnostic(Path(str(value)).name, IDENTITY_TEXT_BYTES)
        fields[name] = text
    return fields


def file_hash(path):
    """Digest one C-owned runtime file; provider CLIs are not pinned by hash."""
    descriptor = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
    with os.fdopen(descriptor, "rb") as source:
        if not stat.S_ISREG(os.fstat(source.fileno()).st_mode):
            raise NativeError("native_setup", "a native launch resource is not a regular file")
        return hashlib.file_digest(source, "sha256").hexdigest()


class NativeError(RuntimeError):
    def __init__(self, code, message):
        super().__init__(message)
        self.code = code


async def verify_provider(options, stop=None):
    from .provider_config import validate_configuration
    from .providers import codex, claude

    selection = validate_configuration(decode(options.selection_json, maximum=16384))
    if options.isolation not in ("local", "bwrap"):
        raise NativeError("isolation", "unsupported native isolation; there is no fallback")
    if selection["provider"] == "claude":
        return await claude.verify(selection["model"], selection["reasoning_effort"],
                                   selection["executable"], stop)
    return await codex.verify(selection["model"], selection["reasoning_effort"],
                              selection["executable"], stop)


def capture_diagnostic(result, capture):
    from .json_wire import encode

    # Keep the bounded stderr beside the exit status: a CLI that refuses its own
    # launch explains that refusal on stderr and nowhere else. Both excerpts stay
    # well inside one log record so the whole diagnostic survives the log bound.
    stderr = bounded_redacted_diagnostic(
        result.stderr.decode("utf-8", errors="replace"), STDERR_EXCERPT_BYTES)
    detail = f"provider exited: {result.returncode}"
    detail = f"stderr={stderr}; {detail}" if stderr else detail
    events = encode(capture.summary()).decode()
    return bounded_redacted_diagnostic(f"cli_events={events}; {detail}", CAPTURE_DIAGNOSTIC_BYTES)


@dataclass(frozen=True, slots=True)
class CommandSpec:
    argv: tuple[str, ...]
    environment: Mapping[str, str]
    cwd: Path

    def __post_init__(self):
        object.__setattr__(self, "environment", MappingProxyType(dict(self.environment)))


async def probe(command, stop=None, *, maximum=DIAGNOSTIC_BYTES,
                stderr_maximum=DIAGNOSTIC_BYTES, timeout=15):
    if stop is not None and stop.requested():
        raise NativeError(await stop.wait(), "native verification stopped before launch")
    child = await OwnedProcess.start(command.argv, command.environment, command.cwd,
                                    stdout_limit=maximum, stderr_limit=stderr_maximum or 0)
    result = await child.run(stop, timeout=timeout, fail_on_stdout_overflow=True,
                             fail_on_stderr_overflow=stderr_maximum is not None)
    if result.reason not in ("exited", "capture_failed"):
        raise NativeError(result.reason, "native verification stopped; process cleanup joined")
    if (result.capture_failed or result.stdout_bytes > maximum or result.returncode != 0
            or (stderr_maximum is not None and result.stderr_bytes > stderr_maximum)):
        raise NativeError("native_setup", "the provider CLI failed its version probe or exceeded its output bound")
    return result.stdout


async def probe_version(path, environment, stop=None):
    """Record what the selected CLI calls itself; never compare it with a pin.

    A CLI that does not answer `--version` is still usable: the provenance
    simply records an unknown version. Only an owner stop propagates.
    """
    command = CommandSpec((str(path), "--version"), environment, path.parent)
    try:
        output = await probe(command, stop, maximum=1024, stderr_maximum=None)
    except NativeError:
        if stop is not None and stop.requested():
            raise
        return UNKNOWN_VERSION
    text = output.decode("utf-8", errors="replace").strip()
    return bounded_redacted_diagnostic(text, VERSION_TEXT_BYTES) if text else UNKNOWN_VERSION


class CliEventCapture:
    """Incremental bounded lines; count each reported event type once."""

    MAXIMUM_EVENT_NAMES = 64

    def __init__(self, tool_names=(), startup=None, sink=None):
        self.startup = startup
        # An optional retention tee for the CLI's own stream. It never changes
        # what the gate observes, the counts, or whether the turn succeeds.
        self.sink = sink
        self.line = bytearray()
        self.truncated = False
        self.stdout_bytes = self.invalid_lines = self.unknown_events = 0
        self.startup_rejected = False
        self.startup_failure = None
        self.last_event = None
        self.last_event_subtype = None
        self.events = {}

    def _observe(self):
        if self.truncated or not self.line.strip():
            self.invalid_lines += self.truncated
            return
        try:
            value = decode(bytes(self.line), maximum=DIAGNOSTIC_BYTES)
        except ValueError:
            self.invalid_lines += 1
            return
        if not isinstance(value, dict):
            self.unknown_events += 1
            return
        if self.startup is not None:
            try:
                self.startup.observe(value)
            except NativeError as error:
                # An owner stop can latch the same gate while the turn ends; only
                # the gate's own refusal of a reported capability is a rejection.
                self.startup_rejected |= getattr(self.startup, "refused", True)
                if self.startup_failure is None:
                    self.startup_failure = bounded_redacted_diagnostic(str(error))
                raise
        kind = value.get("type")
        if (not isinstance(kind, str) or not kind or len(kind) > 64
                or (kind not in self.events and len(self.events) >= self.MAXIMUM_EVENT_NAMES)):
            self.unknown_events += 1
            return
        self.events[kind] = min((1 << 64) - 1, self.events.get(kind, 0) + 1)
        # The last event type the CLI reported before it stopped is the single
        # most useful thing to know about a turn that ended in a transport
        # failure: startup, tool use and completion look nothing alike.
        subtype = value.get("subtype")
        self.last_event = kind
        self.last_event_subtype = subtype if isinstance(subtype, str) and len(subtype) <= 64 else None

    def feed(self, data):
        self.stdout_bytes += len(data)
        if self.sink is not None:
            try:
                self.sink(data)
            except Exception:
                self.sink = None
        rejected = False
        for byte in data:
            if byte == 10:
                try:
                    self._observe()
                except NativeError:
                    rejected = True
                self.line.clear()
                self.truncated = False
            elif len(self.line) < DIAGNOSTIC_BYTES:
                self.line.append(byte)
            else:
                self.truncated = True
        if rejected:
            raise NativeError("native_setup", self.startup_failure
                              or "the native startup check refused this session")

    def finish(self):
        try:
            self._observe()
        finally:
            self.line.clear()

    def summary(self):
        summary = {"stdout_bytes": self.stdout_bytes, "invalid_lines": self.invalid_lines,
                   "unknown_events": self.unknown_events, "startup_rejected": self.startup_rejected,
                   "startup_failure": self.startup_failure, "last_event": self.last_event,
                   "last_event_subtype": self.last_event_subtype, "events": dict(self.events)}
        # A provider-specific gate may also have collected the CLI's own error
        # text; a gate without that detail simply reports none.
        diagnostics = getattr(self.startup, "diagnostics", None)
        if diagnostics is not None:
            summary["provider_errors"] = diagnostics()
        return summary
