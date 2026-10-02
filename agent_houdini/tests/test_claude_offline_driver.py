# Author: Fangzhu Shen
"""Portable checks of the optional driver; no installed Claude or model needed."""

import asyncio
import copy
import http.client
import json
import os
from pathlib import Path
import socket
import sys
import tempfile
import unittest
from unittest.mock import patch

from agent_houdini.tests import claude_offline_fixture as fixture
from agent_houdini.tests.fixtures import claude_offline_wrapper as wrapper


class Events:
    def __init__(self):
        self.items = []

    def emit(self, kind, fields):
        self.items.append((kind, dict(fields)))


class WrapperTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(dir="/tmp")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.native = self.root / "native"
        self.native.write_bytes(b"synthetic native file")
        self.profile = self.root / "network.sb"
        self.profile.write_text(wrapper.base_profile(32145))
        self.config = {"executable": str(self.native), "home": str(self.root),
                       "profile": str(self.profile), "url": "http://127.0.0.1:32145",
                       "interpreter": str(Path(sys.executable).resolve()), "relay": "/synthetic/exact-relay.py"}
        self.socket = socket.socket(socket.AF_UNIX)
        self.addCleanup(self.socket.close)
        self.path = self.root / "relay.sock"
        self.socket.bind(str(self.path))
        self.server = {"type": "stdio", "command": self.config["interpreter"],
                       "args": [self.config["relay"]],
                       "env": {wrapper.SOCKET_ENV: str(self.path), wrapper.TOKEN_ENV: "a" * 64}}

    def args(self):
        return ["-p", "--restricted", "--mcp-config", json.dumps({"mcpServers": {"whiel": self.server}})]

    def prepare(self, args=None, environment=None):
        with patch.object(wrapper, "digest", return_value=wrapper.CLAUDE_SHA256):
            return wrapper.prepare(self.config, self.args() if args is None else args, environment or {})

    def test_pin_is_enforced_before_native_or_sandbox_launch(self):
        with self.assertRaisesRegex(ValueError, "pinned"):
            wrapper.prepare(self.config, ["--version"], {})

    def test_version_uses_base_sandbox_and_synthetic_private_environment(self):
        command, environment = self.prepare(["--version"], {
            "HOME": "/real/home", "ANTHROPIC_API_KEY": "real-credential",
            "HTTP_PROXY": "http://external", "WHIEL_PROPOSER_TOKEN": "engine-token", "PATH": "/usr/bin",
        })
        self.assertEqual(command[:2], ["/usr/bin/sandbox-exec", "-f"])
        self.assertEqual(command[3:], [str(self.native.resolve()), "--version"])
        self.assertEqual(Path(command[2]).read_text(), wrapper.base_profile(32145))
        self.assertEqual(environment["HOME"], str(self.root.resolve()))
        self.assertEqual(environment["ANTHROPIC_API_KEY"], "OFFLINE-SYNTHETIC-NOT-A-CREDENTIAL")
        self.assertEqual(environment["ANTHROPIC_BASE_URL"], self.config["url"])
        self.assertNotIn("HTTP_PROXY", environment)
        self.assertNotIn("WHIEL_PROPOSER_TOKEN", environment)

    def test_native_argv_unchanged_and_only_exact_socket_spellings_added(self):
        args = self.args()
        command, _ = self.prepare(args)
        self.assertEqual(command[4:], args)
        text = Path(command[2]).read_text()
        sockets = sorted({str(self.path), str(self.path.resolve())})
        expected = wrapper.base_profile(32145) + "".join(
            f'(allow network-outbound (remote unix-socket (path-literal {json.dumps(path)})))\n' for path in sockets)
        self.assertEqual(text, expected)
        self.assertNotIn("subpath", text)

    def test_changed_profile_url_and_relay_configuration_are_rejected(self):
        original = copy.deepcopy(self.config)
        for url in ("https://127.0.0.1:32145", "http://example.com:32145", "http://127.0.0.1:32145/",
                    "http://user@127.0.0.1:32145", "http://127.0.0.1:32145?x=1"):
            self.config = {**original, "url": url}
            with self.subTest(url=url), self.assertRaises(ValueError):
                self.prepare()
        self.config = original
        self.profile.write_text(wrapper.base_profile(32145) + "(allow network*)\n")
        with self.assertRaisesRegex(ValueError, "policy changed"):
            self.prepare()
        self.profile.write_text(wrapper.base_profile(32145))
        original_server = copy.deepcopy(self.server)
        for change in ({"command": "/unexpected/python"}, {"args": ["/unexpected/relay"]},
                       {"env": {wrapper.SOCKET_ENV: str(self.path), wrapper.TOKEN_ENV: "bad"}},
                       {"env": {**self.server["env"], "WHIEL_PROPOSER_TOKEN": "forbidden"}}):
            self.server = {**original_server, **change}
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.prepare()
        self.server = original_server
        self.server["env"][wrapper.SOCKET_ENV] = str(self.native)
        with self.assertRaisesRegex(ValueError, "Unix socket"):
            self.prepare()


class DriverTests(unittest.TestCase):
    def test_sse_stages_ledger_then_exact_submit_then_completion(self):
        for count in range(3):
            query = {"model": fixture.MODEL, "messages": [{"content": [{"type": "tool_result"}] * count}]}
            events = fixture.response_events(query)
            self.assertEqual(events[0][0], "message_start")
            self.assertEqual(events[-1][0], "message_stop")
            block = events[1][1]["content_block"]
            if count < 2:
                self.assertEqual(block["name"], "mcp__whiel__" + ("ledger" if count == 0 else "submit"))
                data = json.loads(events[2][1]["delta"]["partial_json"])
                self.assertEqual(data, {} if count == 0 else {"payload": fixture.PAYLOAD})
            else:
                self.assertEqual(block["type"], "text")

    def test_loopback_http_sse_token_endpoint_and_join(self):
        with fixture.OfflineServer() as server:
            connection = http.client.HTTPConnection("127.0.0.1", server.server.server_port, timeout=2)
            try:
                connection.request("POST", "/v1/messages/count_tokens", b"{}")
                response = connection.getresponse()
                self.assertEqual((response.status, json.loads(response.read())), (200, {"input_tokens": 100}))
                connection.request("POST", "/v1/messages", json.dumps({"model": fixture.MODEL, "messages": []}))
                response = connection.getresponse()
                payload = response.read()
                self.assertEqual(response.status, 200)
                self.assertIn(b"mcp__whiel__ledger", payload)
                self.assertIn(b"event: message_stop", payload)
            finally:
                connection.close()
        self.assertFalse(server.thread.is_alive())
        self.assertEqual(len(server.requests), 2)

    def test_receipt_checks_do_not_accept_prose_or_a_changed_payload(self):
        requests = [{"path": "/v1/messages", "body": {
            "tools": [{"name": "mcp__whiel__" + name} for name in fixture.TOOLS],
            "model": fixture.MODEL, "output_config": {"effort": fixture.EFFORT}}}]
        good = {"native": {"outcome": "clean_exit", "submission_delivered": True, "diagnostic_code": None},
                "ledger_calls": 1, "opaque_payload_exact": True, "receipt_received": True,
                "one_bridge": True, "scratch_removed": True, "resource_failure": None, "cancelled": False}
        self.assertTrue(fixture.assess(requests, good, False)["passed"])
        for name, value in (("one_bridge", False), ("receipt_received", False),
                            ("opaque_payload_exact", False), ("cancelled", True), ("ledger_calls", 2),
                            ("resource_failure", "agent_traffic_exhausted"), ("scratch_removed", False)):
            with self.subTest(name=name):
                self.assertFalse(fixture.assess(requests, {**good, name: value}, False)["passed"])
        self.assertFalse(fixture.assess(requests, good, True)["passed"])
        self.assertFalse(fixture.assess([], good, False)["passed"])
        requests[0]["body"]["system"] = fixture.CANARY
        self.assertFalse(fixture.assess(requests, good, False)["passed"])

    def test_optional_missing_binary_has_explicit_unavailable_receipt(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as directory:
            out = Path(directory) / "out"
            with patch.object(sys, "argv", ["fixture", "--claude", str(out / "absent"), "--model",
                                            fixture.MODEL, "--output", str(out)]), patch("builtins.print"):
                self.assertEqual(fixture.main(), 77)
            self.assertEqual(json.loads((out / "receipt.json").read_text())["status"], "unavailable")


class CompositionTests(unittest.IsolatedAsyncioTestCase):
    async def test_actual_python_runtime_client_bridge_and_relay_with_synthetic_native(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as directory:
            root = Path(directory)
            home = root / "home"
            home.mkdir()
            (home / ".claude").mkdir()
            source = Path(__file__).parent / "fixtures" / "claude_offline_fake.py"
            executable = root / "synthetic-claude"
            executable.write_text("#!" + sys.executable + "\n" + source.read_text().split("\n", 1)[1])
            executable.chmod(0o700)
            events = Events()
            with fixture.private_environment(home):
                result = await asyncio.wait_for(fixture.run_composition(executable, root, events), 10)
            self.assertEqual(result["native"], {"outcome": "clean_exit", "submission_delivered": True, "diagnostic_code": None})
            self.assertEqual(result["ledger_calls"], 1)
            for name in ("opaque_payload_exact", "receipt_received", "one_bridge", "scratch_removed"):
                self.assertTrue(result[name], (name, result))
            self.assertIsNone(result["resource_failure"])
            self.assertGreater(result["traffic"]["bytes"], len(fixture.PAYLOAD.encode()))
            self.assertFalse(any(root.glob("wa-*")))
            identities = [fields for kind, fields in events.items if kind == "native_identity"]
            self.assertEqual(len(identities), 1)
            # The recorded identity carries the CLI's own file name, never
            # the directory that led to it: this event is read on machines
            # other than the one the campaign ran on.
            self.assertEqual(identities[0]["executable"], executable.name)
            self.assertEqual(identities[0]["version"], "9.9.9 (fixture CLI)")
            self.assertEqual(identities[0]["model"], fixture.MODEL)
