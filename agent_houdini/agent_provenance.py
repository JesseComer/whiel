# Author: Fangzhu Shen
"""Bounded C-owned provenance snapshots, never verifier attestations.

Digests identify observed bytes, not loaded Python objects or a trusted runtime.
No prompt, command, source content, environment or credential value is emitted.
"""

import hashlib
import json
import re

from .agent_log import WITHHELD, bounded_redacted_diagnostic


def prompt_provenance(prompt: bytes) -> dict:
    return {"prompt_bytes": len(prompt), "prompt_sha256": hashlib.sha256(prompt).hexdigest()}


_SECRET_OPTION = re.compile(r"token|credential|password|secret|authorization|api[-_]?key", re.I)
_MCP_ENV = re.compile(r"mcp_servers\.[^.]+\.env(?:\.|\s*=)")


def native_command_provenance(argv, *, isolation) -> dict:
    """Hash the ordered sanitized argv; never inspect or serialize an environment.

    Native MCP JSON and TOML environment arguments are withheld in their
    entirety, including opaque tokens which cannot be recognized by their value.
    The provider CLI is identified by its path and reported version, not by a
    hash of its bytes, and C's own relay is checked separately before launch.
    """
    sanitized, skip = [], False
    for argument in map(str, argv):
        if skip:
            sanitized.append(WITHHELD)
            skip = False
        elif argument in ("--mcp-config", "--env", "--environment"):
            sanitized.append(argument)
            skip = True
        elif (_MCP_ENV.search(argument) or argument.startswith("--mcp-config=")
              or _SECRET_OPTION.search(argument)):
            sanitized.append(WITHHELD)
            skip = argument.startswith("-") and "=" not in argument
        else:
            sanitized.append(bounded_redacted_diagnostic(argument, 65536))
    encoded = json.dumps(sanitized, ensure_ascii=True, separators=(",", ":")).encode()
    return {"command_scope": "sanitized_native_argv_v1",
            "command_sha256": hashlib.sha256(encoded).hexdigest(),
            "command_arguments": len(sanitized),
            "isolation": bounded_redacted_diagnostic(str(isolation), 64)}
