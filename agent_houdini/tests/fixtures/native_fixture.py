#!/usr/bin/env python3
# Author: Fangzhu Shen
"""Synthetic native CLI fixture; knows native argv/MCP, not the proposer API.

Copy this script and a same-stem .json into a private fixture directory. The
configuration must contain synthetic_fixture=true and fixture-owned events path.
No actual provider, network, authentication or repository API code is invoked.
"""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import tomllib


def load_configuration(path):
    value = json.loads(Path(path).read_text())
    if type(value) is not dict or value.get("synthetic_fixture") is not True:
        raise ValueError("explicit synthetic fixture configuration required")
    return value


def native_mcp(arguments):
    if "--mcp-config" in arguments:
        server = json.loads(arguments[arguments.index("--mcp-config") + 1])["mcpServers"]["whiel"]
        return True, [server["command"], *server.get("args", [])], server.get("env", {})
    if not arguments or arguments[0] != "exec":
        raise ValueError("fixture expects Codex exec or Claude MCP arguments")
    fragments = {}
    for index, item in enumerate(arguments[:-1]):
        if item == "-c":
            key, raw = arguments[index + 1].split("=", 1)
            fragments[key] = tomllib.loads("value=" + raw)["value"]
    command = fragments["mcp_servers.whiel.command"]
    return False, [command, *fragments.get("mcp_servers.whiel.args", [])], fragments.get("mcp_servers.whiel.env", {})


def claude_init(names, configuration, arguments):
    """The shape an installed Claude Code CLI reports: built-in tools beside the
    whiel tools, whatever MCP servers the account loaded, null error fields."""
    return {"type": "system", "subtype": "init",
            "tools": ["Bash", "Read", "Write", "WebFetch", "EndConversation", *names],
            "model": configuration.get("model", arguments[arguments.index("--model") + 1]),
            "claude_code_version": "2.1.273", "apiKeySource": "none", "permissionMode": "dontAsk",
            "plugins": [], "plugin_errors": None, "mcp_server_errors": None,
            "mcp_servers": [{"name": "connector-b", "status": "connected"},
                            {"name": "whiel", "status": "connected"}]}


def run(configuration, arguments):
    events = Path(configuration["events"])
    def record(value):
        with events.open("a") as stream:
            stream.write(json.dumps(value, ensure_ascii=False) + "\n")
    behavior = configuration.get("behavior", "rpc")
    if arguments == ["--capture-test"]:
        os.write(2, b"y" * 200000)
        print(json.dumps({"type": "system", "subtype": "init", "model": "wrong"}), flush=True)
        time.sleep(120)
        return 0
    if arguments == ["--process-test"] or (arguments == ["--version"] and behavior == "version_stall"):
        record({"pid": os.getpid()})
        if behavior in ("escaped", "version_stall", "exit_with_child"):
            child = subprocess.Popen([sys.executable, "-c",
                "import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(120)"],
                start_new_session=True)
            record({"escaped_child_pid": child.pid})
        if behavior == "flood":
            os.write(1, b"x" * 200000)
            os.write(2, b"y" * 200000)
            return 0
        if behavior == "exit_with_child":
            time.sleep(.2)
            return 0
        if behavior == "quick":
            return 0
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        time.sleep(120)
        return 0
    if arguments == ["--version"]:
        text = configuration.get("version", "fixture-cli 9.9.9\n")
        sys.stdout.write(text)
        sys.stderr.write(configuration.get("version_stderr", ""))
        return configuration.get("version_exit", 0)
    claude, command, environment = native_mcp(arguments)
    prompt = sys.stdin.read()
    record({"pid": os.getpid(), "argv": arguments, "prompt": prompt,
            "mcp_command": command, "mcp_environment": environment})
    if behavior.startswith("runtime_"):
        if claude:
            allowed = arguments[arguments.index("--allowedTools") + 1].split(",")
            init = claude_init(allowed, configuration, arguments)
            init.update(configuration.get("init_override", {}))
            print(json.dumps(init), flush=True)
        if behavior == "runtime_prose":
            print("ordinary prose is never an invariant proposal", flush=True)
            return 0
        if behavior == "runtime_nonzero":
            time.sleep(configuration.get("delay", .2))
            return 17
        if behavior == "runtime_workspace":
            Path("native-large-file").write_bytes(b"x" * configuration.get("bytes", 4096))
        if configuration.get("escaped_child"):
            child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(120)"], start_new_session=True)
            record({"escaped_child_pid": child.pid})
        time.sleep(120)
        return 0
    if behavior == "nonzero":
        return 17
    if behavior == "stall":
        child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(120)"], start_new_session=True)
        record({"escaped_child_pid": child.pid})
        if configuration.get("ignore_term"):
            signal.signal(signal.SIGTERM, signal.SIG_IGN)
        time.sleep(120)
        return 0
    if behavior == "oversized_stdout":
        sys.stdout.write("x" * configuration.get("bytes", 70000) + "\n")
        return 0
    child_environment = dict(os.environ)
    child_environment.update(environment)
    child = subprocess.Popen(command, env=child_environment, stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    sequence = 0
    def rpc(method, params=None):
        nonlocal sequence
        sequence += 1
        request = {"jsonrpc": "2.0", "id": sequence, "method": method}
        if params is not None:
            request["params"] = params
        wire = (json.dumps(request, ensure_ascii=False) + "\n").encode()
        fragment = configuration.get("fragment_bytes", len(wire))
        if type(fragment) is not int or fragment < 1:
            raise ValueError("positive fixture fragment size required")
        for offset in range(0, len(wire), fragment):
            child.stdin.write(wire[offset:offset + fragment])
            child.stdin.flush()
        response = child.stdout.readline()
        if not response.endswith(b"\n"):
            raise ValueError("fixture expected a complete MCP reply")
        value = json.loads(response)
        record({"method": method, "request": request, "reply": value,
                "reply_hex": response.hex()})
        return value
    try:
        rpc("initialize", {"protocolVersion": "2025-06-18", "capabilities": {},
                           "clientInfo": {"name": "synthetic", "version": "1"}})
        listed = rpc("tools/list")["result"]["tools"]
        if claude:
            init = claude_init(["mcp__whiel__" + tool["name"] for tool in listed],
                               configuration, arguments)
            init.update(configuration.get("init_override", {}))
            print(json.dumps(init), flush=True)
        for action in configuration.get("actions", []):
            rpc(action["method"], action.get("params"))
        if configuration.get("post_event"):
            print(json.dumps(configuration["post_event"]), flush=True)
        print("ordinary closing prose is not a proposal", flush=True)
        child.stdin.close()
        code = child.wait(timeout=3)
        if code != 0:
            raise ValueError("fixture MCP child failed")
    finally:
        if child.poll() is None:
            child.kill()
        child.wait()
    return configuration.get("exit", 0)


if __name__ == "__main__":
    raise SystemExit(run(load_configuration(Path(__file__).with_suffix(".json")), sys.argv[1:]))
