# Author: Fangzhu Shen
"""Bounded C diagnostics and event records; never verifier or proof evidence."""

from collections.abc import Mapping
import json
import os
from pathlib import Path
import re
import threading


DIAGNOSTIC_BYTES = 64 * 1024
WITHHELD = "provider diagnostic withheld by credential redaction"
_SECRET_NAMES = ("api_key", "api-key", "apikey", "access_token", "refresh_token",
                 "authorization", "password", "client_secret", "openai_api_key")
_SECRET_PATTERN = re.compile(
    r"sk-|bearer |https?://[^/\s:@]+:[^/\s@]+@|(?:"
    + "|".join(_SECRET_NAMES) + r"\b)[\s\"']*[:=]|--(?:"
    + "|".join(_SECRET_NAMES) + r")[\s\x00]+", re.IGNORECASE)


def _sensitive(value: str) -> bool:
    return _SECRET_PATTERN.search(value) is not None


def bounded_redacted_diagnostic(value: str, maximum: int = DIAGNOSTIC_BYTES) -> str:
    if not isinstance(value, str) or type(maximum) is not int or maximum < 0:
        raise ValueError("diagnostic needs text and a nonnegative byte bound")
    if _sensitive(value):
        value = WITHHELD
    return value.encode("utf-8", errors="replace")[:maximum].decode("utf-8", errors="ignore")


class AgentLog:
    """Exclusive JSONL file with bounded records, total bytes and event counts.

    Overflow or an unencodable record suppresses that record and increments
    dropped_events. Every caller passes fields C built from its own typed
    values; foreign text passes bounded_redacted_diagnostic before it arrives.
    Logging cannot grant API authority or convert a native outcome into a
    proposal.
    """

    def __init__(self, path: Path, *, maximum_bytes=8 * 1024 * 1024,
                 maximum_events=16384, record_bytes=DIAGNOSTIC_BYTES):
        if any(type(n) is not int or n < 1 for n in (maximum_bytes, maximum_events, record_bytes)):
            raise ValueError("log limits must be positive integers")
        parent = Path(path).parent.resolve(strict=True)
        descriptor = os.open(parent / Path(path).name,
                             os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC,
                             0o600)
        self._file = os.fdopen(descriptor, "wb")
        self._lock = threading.Lock()
        self.maximum_bytes = maximum_bytes
        self.maximum_events = maximum_events
        self.record_bytes = record_bytes
        self.bytes_written = self.events_written = self.dropped_events = 0

    def emit(self, kind: str, fields: Mapping[str, object]) -> None:
        if (not isinstance(kind, str) or not re.fullmatch(r"[a-z][a-z0-9_.-]{0,63}", kind)
                or _sensitive(kind)):
            kind = "unknown_event"
        with self._lock:
            if self._file.closed:
                raise ValueError("agent log is closed")
            value = {"schema_version": 1, "sequence": self.events_written,
                     "kind": kind, "fields": dict(fields)}
            try:
                encoded = (json.dumps(value, ensure_ascii=False, allow_nan=False,
                                      separators=(",", ":"), default=str) + "\n").encode("utf-8")
            except (TypeError, ValueError):
                self.dropped_events = min(self.dropped_events + 1, 2**64 - 1)
                return
            if (len(encoded) > self.record_bytes
                    or len(encoded) > self.maximum_bytes - self.bytes_written
                    or self.events_written >= self.maximum_events):
                self.dropped_events = min(self.dropped_events + 1, 2**64 - 1)
                return
            self._file.write(encoded)
            self._file.flush()
            self.bytes_written += len(encoded)
            self.events_written += 1

    def close(self):
        with self._lock:
            self._file.close()

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()
