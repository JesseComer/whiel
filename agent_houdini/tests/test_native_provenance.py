# Author: Fangzhu Shen
"""Verified identity events remain bounded C-only metadata."""

from dataclasses import replace
import json
from pathlib import Path
import unittest
from unittest.mock import AsyncMock, patch

from agent_houdini.agent_log import WITHHELD
from agent_houdini.agent_runtime import NativeAgentRuntime
from agent_houdini.provider_runtime import NativeError, native_identity_fields, redacted_selection
from agent_houdini.providers.claude import ClaudeIdentity
from agent_houdini.resource_limits import AgentTrafficBudget
from agent_houdini.runtime_types import NativeOptions, NativeTurn
from agent_houdini.tests.claude_offline_fixture import Stop
from agent_houdini.tests.test_claude_offline_driver import Events
from agent_houdini.tests.test_native_providers import identity as codex_identity


class IdentityFieldsTests(unittest.TestCase):
    def test_fixed_metadata_bounds_and_redacts_selection_fields_before_sink(self):
        identity = replace(codex_identity(), executable="/" + "λ" * 10000,
                           version="Authorization: Bearer example-secret")
        fields = native_identity_fields(identity)
        self.assertEqual(set(fields), {"schema_version", "provider", "version", "model",
                                       "reasoning_effort", "executable"})
        self.assertLessEqual(len(fields["executable"].encode()), 512)
        self.assertEqual(fields["version"], WITHHELD)
        self.assertLess(len(json.dumps(fields).encode()), 16 * 1024)

    def test_claude_private_directory_metadata_is_redacted(self):
        identity = ClaudeIdentity("/cli", "model-a", "medium", Path("/private/api_key=secret/config"),
                                  version="fixture-cli 9.9.9")
        fields = native_identity_fields(identity)
        self.assertEqual(fields["configuration_directory"], WITHHELD)
        self.assertEqual((fields["model"], fields["version"]), ("model-a", "fixture-cli 9.9.9"))


class RedactedSelectionTests(unittest.TestCase):
    def test_an_executable_path_is_reduced_to_its_file_name(self):
        selection = {"provider": "claude", "model": "model-a", "executable": "/opt/tools/bin/claude"}
        self.assertEqual(redacted_selection(selection),
                         {"provider": "claude", "model": "model-a", "executable": "claude"})

    def test_a_missing_or_non_string_executable_is_left_alone(self):
        self.assertEqual(redacted_selection({"provider": "codex"}), {"provider": "codex"})
        self.assertEqual(redacted_selection({"executable": None}), {"executable": None})
        self.assertEqual(redacted_selection("not a mapping"), "not a mapping")


class IdentityEventTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        self.events = Events()
        self.factory = AsyncMock()
        self.runtime = NativeAgentRuntime(
            NativeOptions(b'{"provider":"claude","model":"model-a"}', "local", Path("/tmp")),
            AgentTrafficBudget(), self.events, self.factory)
        self.identity = ClaudeIdentity("/fixture", "model-a", "medium", Path("/private/home"))
        self.turn = NativeTurn(b"fixture", ("submit",), lambda ready: None, Stop())

    async def asyncTearDown(self):
        await self.runtime.shutdown()

    async def test_once_per_verified_endpoint_not_per_request(self):
        # End each turn after verification to isolate event lifetime. The
        # offline composition test additionally exercises this with real I/O.
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=self.identity)) as verify:
            with patch.object(self.runtime, "_scratch", side_effect=NativeError("fixture_end", "stop before native")):
                await self.runtime.run(self.turn)
                await self.runtime.run(self.turn)
        verify.assert_awaited_once()
        records = [fields for kind, fields in self.events.items if kind == "native_identity"]
        self.assertEqual(records, [native_identity_fields(self.identity)])
        self.factory.assert_not_called()

    async def test_failed_verification_never_emits_successful_identity(self):
        with patch("agent_houdini.agent_runtime.verify_provider",
                   AsyncMock(side_effect=NativeError("not_installed", "no provider CLI"))):
            result = await self.runtime.run(self.turn)
        self.assertEqual(result.diagnostic_code, "not_installed")
        self.assertFalse(any(kind == "native_identity" for kind, _ in self.events.items))
        self.assertIsNone(self.runtime.identity)
        self.factory.assert_not_called()

    async def test_sink_failure_cannot_skip_cleanup_or_start_native(self):
        def broken(*_):
            raise OSError("synthetic sink unavailable")
        self.events.emit = broken
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=self.identity)):
            result = await self.runtime.run(self.turn)
        self.assertEqual(result.outcome, "failed")
        self.assertIsNone(self.runtime.identity)
        self.assertIsNone(self.runtime.root)
        self.assertIsNone(self.runtime.active)
        self.factory.assert_not_called()
