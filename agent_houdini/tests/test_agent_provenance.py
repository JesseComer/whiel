# Author: Fangzhu Shen
"""C provenance changes with content while keeping transport/auth values private."""

import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from agent_houdini.agent_log import AgentLog
from agent_houdini.agent_provenance import native_command_provenance, prompt_provenance
from agent_houdini.tests.test_frontend import Host, Runner
from agent_houdini.tests import test_native_owner_stop as owner_stop


class ProvenanceTests(unittest.TestCase):
    def command(self, arguments, **changes):
        return native_command_provenance(arguments, **{"isolation": "local", **changes})

    def test_equal_length_prompt_changes_exact_digest_without_content(self):
        left, right = prompt_provenance(b"alpha"), prompt_provenance(b"bravo")
        self.assertEqual(left["prompt_bytes"], right["prompt_bytes"])
        self.assertNotEqual(left["prompt_sha256"], right["prompt_sha256"])
        self.assertEqual(left["prompt_sha256"], hashlib.sha256(b"alpha").hexdigest())
        self.assertNotIn("alpha", json.dumps(left))

    def test_command_digest_changes_with_equal_length_configuration(self):
        left = self.command(["/own/cli", "--model", "alpha"])
        right = self.command(["/own/cli", "--model", "bravo"])
        self.assertEqual(left["command_arguments"], right["command_arguments"])
        self.assertNotEqual(left["command_sha256"], right["command_sha256"])
        self.assertNotEqual(left, self.command(["/own/cli", "--model", "alpha"], isolation="bwrap"))

    def test_command_sanitization_precedes_hashing_even_for_opaque_tokens(self):
        def arguments(secret):
            return ["/own/cli", "--password", secret, "--api-key=" + secret,
                    "--mcp-config", json.dumps({"mcpServers": {"whiel": {"env": {"OPAQUE": secret}}}}),
                    "-c", 'mcp_servers.whiel.env={WHIEL_AGENT_MCP_TOKEN="' + secret + '"}']
        first, second = self.command(arguments("unique-value-a")), self.command(arguments("unique-value-b"))
        self.assertEqual(first, second)
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "events.jsonl"
            with AgentLog(path) as log:
                log.emit("native_command", first)
            data = path.read_bytes()
            self.assertNotIn(b"unique-value", data)
            self.assertNotIn(b"OPAQUE", data)
            self.assertNotIn(b"WHIEL_AGENT_MCP_TOKEN", data)
            fields = json.loads(data)["fields"]
            self.assertEqual(fields["command_sha256"], first["command_sha256"])


class FrontendProvenanceTests(unittest.IsolatedAsyncioTestCase):
    async def test_actual_native_relay_records_command_and_verified_resource_identities(self):
        case = owner_stop.OwnerStopTests()
        try:
            result, events = await case.run_native("    time.sleep(120)")
            self.assertEqual(result["native"]["outcome"], "clean_exit")
            commands = [fields for kind, fields in events if kind == "native_command"]
            identities = [fields for kind, fields in events if kind == "native_identity"]
            self.assertEqual(len(commands), 1)
            self.assertNotIn("executable_sha256", commands[0])
            self.assertEqual(identities[0]["version"], "9.9.9 (fixture CLI)")
            self.assertEqual(len(commands[0]["command_sha256"]), 64)
            self.assertNotIn("WHIEL_AGENT_MCP_TOKEN", json.dumps(commands))
            self.assertTrue(any(kind == "native_capture" for kind, _ in events))
        finally:
            await case.asyncTearDown()

    async def test_real_wire_request_records_the_exact_prompt_digest(self):
        with tempfile.TemporaryDirectory() as temporary:
            host = Host(Path(temporary))
            runner = Runner()
            try:
                with patch("agent_houdini.frontend.render_prompt", side_effect=[b"alpha", b"bravo"]):
                    await host.start(lambda *_: runner)
                    for number in (1, 2):
                        await host.request(number)
                        await host.complete("no_response", number)
                    self.assertEqual(await host.shutdown(), 0)
                requests = [fields for kind, fields in host.events.items if kind == "request_started"]
                self.assertEqual([fields["prompt_bytes"] for fields in requests], [5, 5])
                self.assertNotEqual(requests[0]["prompt_sha256"], requests[1]["prompt_sha256"])
                self.assertEqual([turn.prompt for turn in runner.turns], [b"alpha", b"bravo"])
                self.assertFalse(any(kind == "source_provenance" for kind, _ in host.events.items))
            finally:
                await host.close()


if __name__ == "__main__":
    unittest.main()
