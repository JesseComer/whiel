# Author: Fangzhu Shen
"""Input-cumulative C agent traffic and owned native workspace allowances.

These operational limits are independent of B's API and certificate limits.
They never establish a semantic verdict or grant access to another workspace.
"""

from dataclasses import dataclass
from pathlib import Path
import shutil
import threading


U64_MAX = (1 << 64) - 1
TRAFFIC_LEGS = ("prompt", "mcp_request", "canonical_request", "canonical_reply", "mcp_reply")


class AgentResourceError(RuntimeError):
    """A latched C allowance failure; not a rejected invariant or proof."""

    def __init__(self, code):
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True)
class AgentLimits:
    traffic_bytes: int = 1024 * 1024 * 1024
    messages: int = 16384
    workspace_bytes: int = 8 * 1024 * 1024 * 1024
    minimum_free_bytes: int = 2 * 1024 * 1024 * 1024
    native_seconds: float | None = None
    # Claude only: the CLI's cap on thinking tokens per model turn, so a turn
    # cannot spend its whole consultation budget thinking without acting.
    thinking_tokens: int | None = None

    def __post_init__(self):
        for name in ("traffic_bytes", "messages", "workspace_bytes", "minimum_free_bytes"):
            if type(getattr(self, name)) is not int or not 0 <= getattr(self, name) <= U64_MAX:
                raise ValueError("agent allowances must be nonnegative u64 integers")
        if self.thinking_tokens is not None and (type(self.thinking_tokens) is not int
                                                 or not 0 < self.thinking_tokens <= U64_MAX):
            raise ValueError("thinking token allowance must be a positive u64 integer")
        if self.native_seconds is not None:
            import math
            if (type(self.native_seconds) not in (int, float) or not math.isfinite(self.native_seconds)
                    or self.native_seconds < 0):
                raise ValueError("native time allowance must be finite and nonnegative")


class AgentTrafficBudget:
    """Bare construction accounts without applying campaign defaults."""

    def __init__(self, limits: AgentLimits | None = None):
        self.maximum_bytes = U64_MAX if limits is None else limits.traffic_bytes
        self.maximum_messages = U64_MAX if limits is None else limits.messages
        self._bytes = self._messages = 0
        self._legs = {leg: [0, 0] for leg in TRAFFIC_LEGS}
        self._failure = None
        self._lock = threading.Lock()

    def charge(self, leg, byte_count, messages=0):
        if (leg not in TRAFFIC_LEGS or type(byte_count) is not int or type(messages) is not int
                or not 0 <= byte_count <= U64_MAX or not 0 <= messages <= U64_MAX):
            raise ValueError("invalid agent traffic charge")
        with self._lock:
            if self._failure is not None:
                raise AgentResourceError(self._failure)
            next_bytes, next_messages = self._bytes + byte_count, self._messages + messages
            if next_bytes > self.maximum_bytes or next_messages > self.maximum_messages:
                self._failure = "agent_traffic_exhausted"
                raise AgentResourceError(self._failure)
            self._bytes, self._messages = next_bytes, next_messages
            self._legs[leg][0] += byte_count
            self._legs[leg][1] += messages

    def failure(self):
        with self._lock:
            return self._failure

    def usage(self):
        with self._lock:
            return {"bytes": self._bytes, "messages": self._messages,
                    "legs": {name: tuple(counts) for name, counts in self._legs.items()}}


class NativeAllowance:
    """C's optional cumulative native time plus a cheap scratch-space guard."""

    def __init__(self, limits: AgentLimits | None = None):
        self.limits = limits
        self.native_seconds = 0.0
        self._free_at_start = None
        self._failure = None

    def failure(self):
        return self._failure

    def _fail(self, code):
        if self._failure is None:
            self._failure = code
        raise AgentResourceError(self._failure)

    def checkpoint(self, *, elapsed=0):
        if self._failure:
            raise AgentResourceError(self._failure)
        if (self.limits is not None and self.limits.native_seconds is not None
                and self.native_seconds + elapsed >= self.limits.native_seconds):
            self._fail("agent_native_time_exhausted")

    def record_native_time(self, seconds):
        self.native_seconds += seconds

    def check_workspace(self, root: Path):
        """Bound scratch growth by free space, without walking the agent's tree.

        The cap measures how much room the scratch filesystem lost since the
        first observation, so an unrelated writer on the same filesystem counts
        toward it. This is an operational stop, never a semantic verdict.
        """
        self.checkpoint()
        if self.limits is None:
            return
        try:
            free = shutil.disk_usage(root).free
        except OSError:
            self._fail("agent_workspace_exhausted")
        if self._free_at_start is None:
            self._free_at_start = free
        if (free < self.limits.minimum_free_bytes
                or self._free_at_start - free > self.limits.workspace_bytes):
            self._fail("agent_workspace_exhausted")
