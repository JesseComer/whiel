#!/usr/bin/env python3
# Author: Fangzhu Shen
# Invariant-synthesis native CLI transport fixture; no provider account is used.
"""Optional offline native-Claude acceptance using only the Python C runtime.

Run from the repository root with `python3 -m agent_houdini.tests.claude_offline_fixture
--claude /absolute/claude --model <model> --output /fresh/output`. Requires macOS
and the pinned public Claude darwin-arm64 binary this fixture was recorded
against. No install, account or real model is used: Seatbelt denies networking
except the synthetic loopback API and exact C-owned MCP socket. Exit 77 means
this optional binary/platform is unavailable.
"""
from __future__ import annotations

import argparse
import asyncio
from contextlib import contextmanager
from dataclasses import asdict
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import shlex
import signal
import sys
import tempfile
import threading
import time

from agent_houdini.agent_log import AgentLog
from agent_houdini.agent_runtime import NativeAgentRuntime
from agent_houdini.agent_transport import McpTransport, MeteredRequestAccess
from agent_houdini.json_wire import decode, encode
from agent_houdini.mcp_client import McpClient
from agent_houdini.resource_limits import AgentLimits, AgentTrafficBudget
from agent_houdini.runtime_types import NativeOptions, NativeTurn, RequestView
from agent_houdini.tests.fixtures import claude_offline_wrapper as wrapper
from agent_houdini.tool_catalog import KNOWN_QUERIES, default_catalog

CLAUDE_SHA256 = wrapper.CLAUDE_SHA256
TOOLS = ["countermodel", "evaluate_clauses", "history", "ledger", "strongest_refutations", "submit", "validate_clauses"]
MODEL = "model-a"
EFFORT = "medium"
PAYLOAD = " {offline exact λ}\n"
CANARY = "OFFLINE_AMBIENT_CONTEXT_CANARY"
MAX_REQUEST_BYTES = 8 * 1024 * 1024


def response_events(query):
    calls = sum(block.get("type") == "tool_result" for message in query.get("messages", [])
                for block in message.get("content", []) if isinstance(block, dict))
    if calls < 2:
        name = "ledger" if calls == 0 else "submit"
        content = {"type": "tool_use", "id": f"toolu_offline_{calls}", "name": f"mcp__whiel__{name}",
                   "input": {} if calls == 0 else {"payload": PAYLOAD}}
        reason = "tool_use"
    else:
        content = {"type": "text", "text": "Offline fixture complete"}
        reason = "end_turn"
    message = {"id": "msg_offline", "type": "message", "role": "assistant", "model": query.get("model"),
               "content": [], "stop_reason": None, "stop_sequence": None,
               "usage": {"input_tokens": 100, "output_tokens": 0}}
    start = {**content, "input": {}} if content["type"] == "tool_use" else {**content, "text": ""}
    delta = ({"type": "input_json_delta", "partial_json": json.dumps(content["input"])}
             if content["type"] == "tool_use" else {"type": "text_delta", "text": content["text"]})
    return [("message_start", {"type": "message_start", "message": message}),
            ("content_block_start", {"type": "content_block_start", "index": 0, "content_block": start}),
            ("content_block_delta", {"type": "content_block_delta", "index": 0, "delta": delta}),
            ("content_block_stop", {"type": "content_block_stop", "index": 0}),
            ("message_delta", {"type": "message_delta", "delta": {"stop_reason": reason, "stop_sequence": None},
                               "usage": {"output_tokens": 10}}),
            ("message_stop", {"type": "message_stop"})]


class OfflineServer:
    """Bounded synthetic Anthropic SSE endpoint, with joined HTTP workers."""
    def __init__(self):
        self.requests = []
        owner = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *_):
                pass

            def setup(self):
                super().setup()
                self.connection.settimeout(2)

            def do_POST(self):
                try:
                    size = int(self.headers.get("Content-Length", "-1"))
                    if not 0 <= size <= MAX_REQUEST_BYTES:
                        self.send_error(413)
                        return
                    if len(owner.requests) >= 32:
                        self.send_error(429)
                        return
                    query = json.loads(self.rfile.read(size))
                    if not isinstance(query, dict):
                        raise ValueError("expected request object")
                    owner.requests.append({"path": self.path, "body": query})
                    if self.path.endswith("/count_tokens"):
                        content = b'{"input_tokens":100}'
                        self.send_response(200)
                        self.send_header("Content-Type", "application/json")
                        self.send_header("Content-Length", str(len(content)))
                        self.end_headers()
                        self.wfile.write(content)
                        return
                    self.send_response(200)
                    self.send_header("Content-Type", "text/event-stream")
                    self.end_headers()
                    for name, event in response_events(query):
                        self.wfile.write(("event: " + name + "\ndata: " + json.dumps(event) + "\n\n").encode())
                        self.wfile.flush()
                except (ValueError, TypeError, TimeoutError, BrokenPipeError, ConnectionResetError):
                    self.close_connection = True

        self.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.server.daemon_threads = False
        self.thread = threading.Thread(target=self.server.serve_forever, kwargs={"poll_interval": .05})

    @property
    def url(self):
        return f"http://127.0.0.1:{self.server.server_port}"

    def __enter__(self):
        self.thread.start()
        return self

    def __exit__(self, *_):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join()


class Stop:
    def __init__(self):
        self.event = asyncio.Event()
        self.reason = "cancelled"

    def requested(self):
        return self.event.is_set()

    def set(self, reason="cancelled"):
        if not self.requested():
            self.reason = reason
            self.event.set()

    async def wait(self):
        await self.event.wait()
        return self.reason


class FixtureAccess:
    """Synthetic API boundary only; its receipt does not claim admission."""
    view = RequestView(1, b"{}", b"{}", 25_000_000_000)
    query_names = KNOWN_QUERIES

    def __init__(self):
        self.ledger_calls = 0
        self.proposals = []

    async def query(self, name, arguments):
        if name != "ledger" or decode(arguments) != {}:
            raise AssertionError("offline fixture expected only an empty ledger query")
        self.ledger_calls += 1
        return encode({"name": "ledger", "round": 7, "clauses": [], "checks": []})

    async def submit(self, proposal):
        if self.ledger_calls != 1 or self.proposals or proposal != PAYLOAD.encode():
            raise AssertionError("offline submission order or exact bytes changed")
        self.proposals.append(proposal)


@contextmanager
def private_environment(home):
    saved = dict(os.environ)
    selected = {key: saved[key] for key in ("PATH", "LANG") if key in saved}
    selected.update(HOME=str(home), CLAUDE_CONFIG_DIR=str(home / ".claude"))
    os.environ.clear()
    os.environ.update(selected)
    try:
        yield
    finally:
        os.environ.clear()
        os.environ.update(saved)


def make_wrapper(out, cli, home, server):
    profile = out / "network.sb"
    profile.write_text(wrapper.base_profile(server.server.server_port))
    target = out / "claude-wrapper.py"
    source = Path(wrapper.__file__).read_text().split("\n", 1)[1]
    target.write_text("#!" + sys.executable + "\n" + source)
    target.chmod(0o700)
    relay = Path(__file__).resolve().parents[1] / "mcp_stdio.py"
    target.with_suffix(".json").write_text(json.dumps({
        "executable": str(cli), "home": str(home), "profile": str(profile), "url": server.url,
        "interpreter": str(Path(sys.executable).resolve()), "relay": str(relay),
    }))
    return target


async def run_composition(executable, scratch_parent, events, model=MODEL, effort=EFFORT):
    """Exercise production identity, native supervision, MCP and receipt paths."""
    access = FixtureAccess()
    limits = AgentLimits(traffic_bytes=32 * 1024 * 1024, messages=256, minimum_free_bytes=0)
    budget = AgentTrafficBudget(limits)
    metered = MeteredRequestAccess(access, budget)
    stop = Stop()
    bridges, clients = [], []
    catalog = default_catalog()

    async def bridge_factory(work, handler, signal, allowance, sink):
        bridge = await McpTransport.create(work, handler, signal, allowance, sink)
        bridges.append(bridge)
        return bridge

    def make_handler(ready):
        client = McpClient(catalog, access.query_names, metered, native_ready=ready)
        clients.append(client)
        return client.line

    options = NativeOptions(encode({"provider": "claude", "model": model, "reasoning_effort": effort,
                                    "executable": str(executable)}), "local", scratch_parent)
    runtime = NativeAgentRuntime(options, budget, events, bridge_factory, limits=limits)
    prompt = b"Offline fixture: call ledger, then submit the exact payload supplied by the tool-use response."
    budget.charge("prompt", len(prompt), 1)
    turn = NativeTurn(prompt, tuple(catalog.inventory(access.query_names)), make_handler, stop,
                      lambda: metered.receipt_received, remaining_budget_ns=25_000_000_000)
    loop = asyncio.get_running_loop()
    timer = loop.call_later(25, stop.set, "deadline")
    handlers = []
    try:
        for signum in (signal.SIGINT, signal.SIGTERM):
            loop.add_signal_handler(signum, stop.set, "cancelled")
            handlers.append(signum)
        result = await runtime.run(turn)
    finally:
        timer.cancel()
        try:
            await runtime.shutdown()
        finally:
            for signum in handlers:
                loop.remove_signal_handler(signum)
    return {
        "native": asdict(result), "ledger_calls": access.ledger_calls,
        "opaque_payload_exact": access.proposals == [PAYLOAD.encode()],
        "receipt_received": metered.receipt_received,
        "one_bridge": len(bridges) == 1,
        "resource_failure": budget.failure() or runtime.allowance.failure(),
        "scratch_removed": runtime.root is None or not runtime.root.exists(),
        "traffic": budget.usage(), "cancelled": stop.requested(),
    }


def assess(requests, composition, hook_ran, model=MODEL, effort=EFFORT):
    messages = [r["body"] for r in requests if not r["path"].endswith("/count_tokens")]
    inventories = [sorted(tool["name"] for tool in message.get("tools", [])) for message in messages]
    selections = [{"model": message.get("model"), "effort": message.get("output_config", {}).get("effort")}
                  for message in messages]
    expected = [f"mcp__whiel__{name}" for name in TOOLS]
    checks = {
        "native_joined_success": composition.get("native") == {
            "outcome": "clean_exit", "submission_delivered": True, "diagnostic_code": None},
        "one_ledger": composition.get("ledger_calls") == 1,
        "opaque_payload_exact": composition.get("opaque_payload_exact") is True,
        "receipt_received": composition.get("receipt_received") is True and composition.get("one_bridge") is True,
        "scratch_removed": composition.get("scratch_removed") is True,
        "no_resource_failure": composition.get("resource_failure") is None,
        "not_cancelled": composition.get("cancelled") is False,
        "exact_tools": bool(inventories) and all(names == expected for names in inventories),
        "exact_model_effort": bool(selections) and all(s == {"model": model, "effort": effort} for s in selections),
        "hook_disabled": not hook_ran,
        "ambient_context_absent": CANARY not in json.dumps(requests),
    }
    return {"passed": all(checks.values()), "checks": checks, "inventories": inventories, "selections": selections}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--claude", type=Path, required=True)
    parser.add_argument("--model", required=True, help="exact model string the CLI reports back")
    parser.add_argument("--reasoning-effort", default=EFFORT)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(mode=0o700)
    try:
        cli = args.claude.resolve(strict=True)
        available = sys.platform == "darwin" and wrapper.digest(cli) == CLAUDE_SHA256
    except OSError:
        available = False
    if not available:
        receipt = {"status": "unavailable", "passed": False,
                   "reason": "requires macOS and the pinned public Claude darwin-arm64 binary",
                   "expected_sha256": CLAUDE_SHA256}
        (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(json.dumps(receipt, indent=2))
        return 77
    home = out / "home"
    home.mkdir(mode=0o700)
    (home / ".claude").mkdir(mode=0o700)
    hook_marker = out / "unexpected-hook"
    (home / ".claude" / "settings.json").write_text(json.dumps({"hooks": {"SessionStart": [
        {"hooks": [{"type": "command", "command": "touch " + shlex.quote(str(hook_marker))}]}]}}))
    (home / ".claude" / "CLAUDE.md").write_text(CANARY)
    start = time.monotonic()
    with OfflineServer() as server, tempfile.TemporaryDirectory(prefix="c-offline-", dir="/tmp") as scratch:
        executable = make_wrapper(out, cli, home, server)
        with private_environment(home), AgentLog(out / "agent.jsonl") as events:
            try:
                composition = asyncio.run(run_composition(executable, Path(scratch), events,
                                                          args.model, args.reasoning_effort))
            except Exception as error:
                # Diagnostics stay bounded in C's log; do not publish native
                # streams, credentials or arbitrary exception payloads.
                composition = {"error_type": type(error).__name__}
        receipt = assess(server.requests, composition, hook_marker.exists(),
                         args.model, args.reasoning_effort)
        receipt.update(status="passed" if receipt["passed"] else "failed", composition=composition,
                       request_count=len(server.requests), seconds=time.monotonic() - start,
                       sha256={str(path): wrapper.digest(path) for path in (
                           cli, executable, Path(__file__), Path(wrapper.__file__))})
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))
    return 0 if receipt["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
