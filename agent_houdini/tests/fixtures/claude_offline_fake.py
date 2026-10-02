#!/usr/bin/env python3
# Author: Fangzhu Shen
"""Synthetic native CLI for exercising the optional fixture's real C plumbing."""

import json
import os
from pathlib import Path
import subprocess
import sys

if sys.argv[1:] == ["--version"]:
    print("9.9.9 (fixture CLI)")
    raise SystemExit(0)

configuration = json.loads(sys.argv[sys.argv.index("--mcp-config") + 1])["mcpServers"]["whiel"]
relay = subprocess.Popen([configuration["command"], *configuration["args"]],
                         env={**os.environ, **configuration["env"]},
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE)


def call(number, method, params):
    relay.stdin.write(json.dumps({"jsonrpc": "2.0", "id": number, "method": method, "params": params}).encode() + b"\n")
    relay.stdin.flush()
    response = json.loads(relay.stdout.readline())
    if "error" in response or response.get("id") != number:
        raise RuntimeError("synthetic relay exchange failed")
    return response["result"]


try:
    call(1, "initialize", {"protocolVersion": "2024-11-05", "capabilities": {}, "clientInfo": {"name": "fixture", "version": "1"}})
    inventory = call(2, "tools/list", {})
    names = sorted("mcp__whiel__" + tool["name"] for tool in inventory["tools"])
    # An installed CLI also lists its own built-in tools and the MCP servers
    # the account loaded, and reports its error fields as null.
    print(json.dumps({"type": "system", "subtype": "init",
                      "tools": ["Bash", "Read", "Write", "EndConversation", *names],
                      "model": sys.argv[sys.argv.index("--model") + 1],
                      "claude_code_version": "2.1.273", "apiKeySource": "none",
                      "permissionMode": "dontAsk", "plugins": [],
                      "plugin_errors": None, "mcp_server_errors": None,
                      "mcp_servers": [{"name": "connector-a", "status": "connected"},
                                      {"name": "whiel", "status": "connected"}]}), flush=True)
    call(3, "tools/call", {"name": "ledger", "arguments": {}})
    call(4, "tools/call", {"name": "submit", "arguments": {"payload": " {offline exact λ}\n"}})
finally:
    relay.stdin.close()
    relay.stdout.close()
    relay.wait(timeout=2)
