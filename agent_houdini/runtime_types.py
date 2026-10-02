# Author: Fangzhu Shen
"""Shared C values passed between the API client, native runner and launcher.

These are C implementation types, not additions to the verifier API. Opaque API
bytes remain immutable; only the API client owns receipt state.
"""

from collections.abc import Callable, Mapping
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Literal


class CleanupError(RuntimeError):
    """C-owned work or resources could not be joined and released."""


@dataclass(frozen=True, slots=True)
class RequestView:
    request_id: int
    observation: bytes
    response_example: bytes
    remaining_budget_ns: int | None


@dataclass(frozen=True, slots=True)
class NativeOptions:
    selection_json: bytes
    isolation: str
    scratch_parent: Path


@dataclass(frozen=True, slots=True)
class McpLaunch:
    argv: tuple[str, ...]
    environment: Mapping[str, str]
    readonly_resources: tuple[Path, ...]

    def __post_init__(self) -> None:
        object.__setattr__(self, "environment", MappingProxyType(dict(self.environment)))


@dataclass(frozen=True, slots=True)
class NativeTurn:
    prompt: bytes
    tool_names: tuple[str, ...]
    # Called with C's readiness gate; returns the turn's MCP line handler.
    make_mcp_handler: Callable
    stop: object
    # True once B's submission receipt arrived; never semantic admission.
    submitted: Callable[[], bool] = lambda: False
    # B's remaining request budget; C's own deadline is never later than it.
    remaining_budget_ns: int | None = None
    # C's retention record for this consultation. Diagnostics only: nothing
    # written through it is read back into a prompt, a query or a submission.
    record: object | None = None


@dataclass(frozen=True, slots=True)
class NativeResult:
    outcome: Literal["clean_exit", "cancelled", "failed"]
    submission_delivered: bool
    diagnostic_code: str | None

