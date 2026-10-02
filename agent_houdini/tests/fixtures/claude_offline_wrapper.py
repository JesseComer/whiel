#!/usr/bin/env python3
# Author: Fangzhu Shen
"""Standalone pinned-Claude wrapper for the optional macOS offline fixture."""

import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys
from urllib.parse import urlsplit

CLAUDE_SHA256 = "553d1b9e9e7068b275c0a783c7e139ff6503096f286e674c8c919379fb0eca62"
SOCKET_ENV = "WHIEL_AGENT_MCP_SOCKET"
TOKEN_ENV = "WHIEL_AGENT_MCP_TOKEN"


def base_profile(port):
    return ('(version 1)\n(allow default)\n(deny network*)\n'
            f'(allow network-outbound (remote tcp "localhost:{port}"))\n')


def digest(path):
    with open(path, "rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def prepare(config, arguments, environment):
    """Validate fixture inputs before constructing the exact Seatbelt invocation."""
    executable = Path(config["executable"]).resolve(strict=True)
    if digest(executable) != CLAUDE_SHA256:
        raise ValueError("expected pinned public Claude 2.1.266 binary")
    url = urlsplit(config["url"])
    if (url.scheme != "http" or url.hostname != "127.0.0.1" or url.username is not None
            or url.password is not None or url.path or url.query or url.fragment
            or url.port is None or not 0 < url.port <= 65535
            or config["url"] != f"http://127.0.0.1:{url.port}"):
        raise ValueError("fixture URL must be an exact loopback endpoint")
    profile = Path(config["profile"])
    text = base_profile(url.port)
    if profile.read_text() != text:
        raise ValueError("fixture base network policy changed")
    if arguments != ["--version"]:
        if arguments.count("--mcp-config") != 1:
            raise ValueError("expected one explicit MCP configuration")
        offset = arguments.index("--mcp-config")
        if offset + 1 >= len(arguments):
            raise ValueError("missing MCP configuration")
        configuration = json.loads(arguments[offset + 1])
        if set(configuration) != {"mcpServers"} or set(configuration["mcpServers"]) != {"whiel"}:
            raise ValueError("only the fixture MCP server is allowed")
        server = configuration["mcpServers"]["whiel"]
        if (set(server) != {"type", "command", "args", "env"} or server["type"] != "stdio"
                or server["command"] != config["interpreter"] or server["args"] != [config["relay"]]
                or set(server["env"]) != {SOCKET_ENV, TOKEN_ENV}
                or not isinstance(server["env"][TOKEN_ENV], str)
                or re.fullmatch("[0-9a-f]{64}", server["env"][TOKEN_ENV]) is None):
            raise ValueError("unexpected C relay configuration")
        socket_path = Path(server["env"][SOCKET_ENV])
        if not socket_path.is_absolute() or not stat.S_ISSOCK(socket_path.stat().st_mode):
            raise ValueError("MCP socket must be an existing absolute Unix socket")
        # macOS can report /tmp as /private/tmp. Permit those two spellings
        # of the same socket, never its parent directory or arbitrary sockets.
        for spelling in sorted({str(socket_path), str(socket_path.resolve(strict=True))}):
            text += f'(allow network-outbound (remote unix-socket (path-literal {json.dumps(spelling)})))\n'
    selected_profile = profile.with_name(profile.stem + "-native.sb")
    selected_profile.write_text(text)
    home = Path(config["home"]).resolve(strict=True)
    child_environment = {name: environment[name] for name in (
        "PATH", "LANG", "TMPDIR", "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC",
        "CLAUDE_CODE_DISABLE_CLAUDE_MDS", "CLAUDE_CODE_DISABLE_ATTACHMENTS",
        "CLAUDE_CODE_DISABLE_AUTO_MEMORY", "CLAUDE_CODE_DISABLE_OFFICIAL_MARKETPLACE_AUTOINSTALL",
        "CLAUDE_CODE_DISABLE_GIT_INSTRUCTIONS", "ENABLE_CLAUDEAI_MCP_SERVERS", "ENABLE_TOOL_SEARCH",
    ) if name in environment}
    child_environment.update(HOME=str(home), CLAUDE_CONFIG_DIR=str(home / ".claude"),
                             ANTHROPIC_API_KEY="OFFLINE-SYNTHETIC-NOT-A-CREDENTIAL",
                             ANTHROPIC_BASE_URL=config["url"])
    command = ["/usr/bin/sandbox-exec", "-f", str(selected_profile), str(executable), *arguments]
    return command, child_environment


def main():
    config = json.loads(Path(__file__).with_suffix(".json").read_text())
    command, environment = prepare(config, sys.argv[1:], os.environ)
    os.execve(command[0], command, environment)


if __name__ == "__main__":
    main()
