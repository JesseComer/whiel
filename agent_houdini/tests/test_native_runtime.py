# Author: Fangzhu Shen
"""Native turn lifecycle against a fake C MCP bridge and real fake CLI children."""

import asyncio
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import AsyncMock, patch

from agent_houdini.agent_runtime import NativeAgentRuntime
from agent_houdini.json_wire import encode
from agent_houdini.providers import claude, codex
from agent_houdini.provider_runtime import file_hash
from agent_houdini.resource_limits import AgentLimits, AgentTrafficBudget
from agent_houdini.runtime_types import CleanupError, McpLaunch, NativeOptions, NativeTurn
from agent_houdini.tests.test_native_process_tree import (
    Stop, alive, await_events, make_fixture, terminate,
)
from agent_houdini.tests.test_native_providers import MODEL


class Sink:
    def __init__(self):
        self.events = []

    def emit(self, kind, fields):
        self.events.append((kind, dict(fields)))


class Bridge:
    def __init__(self, work):
        relay = work / "relay.py"
        relay.write_text("# synthetic unused relay\n")
        python = Path(sys.executable).resolve()
        self.launch = McpLaunch((str(python), str(relay)), {"C_RELAY": "fixture"}, (python, relay))
        self.delivered = False
        self.code = None
        self.closed = False
        self.cleanup_failure = False

    def submission_delivered(self):
        return self.delivered

    def failure(self):
        return self.code

    def begin_owner_stop(self):
        if not self.delivered or self.code is not None:
            raise ValueError("intentional stop requires healthy delivery")

    async def close_and_join(self):
        self.closed = True
        if self.cleanup_failure:
            raise CleanupError("synthetic bridge cleanup failure")


class Factory:
    def __init__(self):
        self.bridges = []
        self.gate = None

    async def __call__(self, *args):
        bridge = Bridge(args[0])
        self.bridges.append(bridge)
        if self.gate is not None:
            await self.gate.wait()
        return bridge


class NativeRuntimeTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        self.directory = tempfile.TemporaryDirectory(dir="/tmp")
        self.root = Path(self.directory.name)
        self.factory = Factory()
        self.sink = Sink()
        self.stop = Stop()
        self.submitted = False
        self.runtimes = []
        self.patcher = patch("agent_houdini.agent_runtime.RECEIPT_GRACE_SECONDS", .12)
        self.patcher.start()

    async def asyncTearDown(self):
        for runtime in self.runtimes:
            try:
                await runtime.shutdown()
            except CleanupError:
                # Synthetic failed-cleanup tests physically joined their fake bridge.
                runtime.cleanup_error = None
                await runtime.shutdown()
        self.patcher.stop()
        self.directory.cleanup()

    def make(self, provider="codex", behavior="runtime_idle", limits=None, **configuration):
        script = make_fixture(self.root, behavior=behavior, **configuration)
        script.write_text("#!" + sys.executable + "\n" + script.read_text())
        script.chmod(0o700)
        if provider == "claude":
            selected = claude.ClaudeIdentity(str(script), MODEL, "medium", self.root / ".claude")
        else:
            selected = codex.CodexIdentity(str(script), MODEL, "medium")
        budget = AgentTrafficBudget(limits)
        options = NativeOptions(encode({"provider": provider, "model": MODEL}), "local", self.root)
        runtime = NativeAgentRuntime(options, budget, self.sink, self.factory, limits=limits)
        self.runtimes.append(runtime)
        return runtime, selected

    def turn(self, stop=None):
        self.ready = None
        self.submitted = False

        def make_handler(ready):
            self.ready = ready

            async def handler(data):
                await ready()
                return None
            return handler

        return NativeTurn(b"native fixture prompt", ("submit", "ledger"), make_handler,
                          stop or self.stop, lambda: self.submitted)

    async def started(self):
        events = await await_events(self.root, 1)
        for _ in range(100):
            if self.factory.bridges:
                return events
            await asyncio.sleep(.01)
        self.fail("fake bridge did not start")

    async def test_constructor_and_pre_cancel_never_start_native(self):
        runtime, selected = self.make()
        self.assertIsNone(runtime.root)
        self.stop.set("deadline")
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)) as verify:
            result = await runtime.run(self.turn())
            verify.assert_not_called()
        self.assertEqual((result.outcome, result.diagnostic_code), ("cancelled", "deadline"))
        self.assertEqual(self.factory.bridges, [])

    async def test_receipt_allows_a_joined_owner_stop_for_both_providers(self):
        for provider in ("codex", "claude"):
            with self.subTest(provider=provider):
                (self.root / "events").unlink(missing_ok=True)
                runtime, selected = self.make(provider=provider)
                with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
                    task = asyncio.create_task(runtime.run(self.turn()))
                    events = await self.started()
                    if provider == "claude":
                        await asyncio.wait_for(self.ready(), 2)
                    self.submitted = True
                    result = await asyncio.wait_for(task, 3)
                self.assertEqual((result.outcome, result.submission_delivered), ("clean_exit", True))
                self.assertTrue(self.factory.bridges[-1].closed)
                self.assertEqual(runtime.budget.usage()["bytes"], 0, "N must not double-charge the prompt")
                self.assertFalse(alive(events[0]["pid"]))

    async def test_nonzero_during_receipt_grace_still_fails(self):
        runtime, selected = self.make(behavior="runtime_nonzero", delay=.05)
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
            task = asyncio.create_task(runtime.run(self.turn()))
            await self.started()
            self.submitted = True
            result = await asyncio.wait_for(task, 3)
        self.assertEqual((result.outcome, result.submission_delivered), ("failed", False))

    async def test_prose_and_zero_exit_do_not_supply_a_proposal(self):
        runtime, selected = self.make(behavior="runtime_prose")
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
            result = await runtime.run(self.turn())
        self.assertEqual((result.outcome, result.submission_delivered), ("clean_exit", False))
        with self.assertRaises(Exception):
            await self.ready()

    async def test_transport_changed_before_launch_is_rejected_before_native(self):
        runtime, selected = self.make()
        observed = []

        def changed(path):
            digest = file_hash(path)
            observed.append(Path(path))
            relay = Path(self.factory.bridges[-1].launch.argv[1])
            if Path(path) == relay and observed.count(relay) == 1:
                relay.write_text("# changed\n")
            return digest

        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)), \
                patch("agent_houdini.agent_runtime.file_hash", changed):
            result = await asyncio.wait_for(runtime.run(self.turn()), 2)
        self.assertEqual(result.diagnostic_code, "native_setup")
        self.assertFalse((self.root / "events").exists())
        self.assertTrue(self.factory.bridges[-1].closed)

    async def test_fresh_requests_reuse_the_selected_identity(self):
        runtime, selected = self.make(behavior="runtime_prose")
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)) as verify:
            first = await runtime.run(self.turn())
            second = await runtime.run(self.turn())
            self.assertEqual((first.outcome, second.outcome), ("clean_exit", "clean_exit"))
            verify.assert_awaited_once()
            self.assertEqual(runtime.request_number, 2)
            self.assertNotEqual(self.factory.bridges[-2].launch.argv[1], self.factory.bridges[-1].launch.argv[1])
            # A CLI replaced between turns is no longer an identity failure.
            script = Path(selected.executable)
            script.write_text(script.read_text() + "\n# changed after two turns\n")
            third = await runtime.run(self.turn())
            self.assertEqual(third.outcome, "clean_exit")
            self.assertEqual(len((self.root / "events").read_text().splitlines()), 3)

    async def test_missing_receipt_and_latched_bridge_failure_cannot_complete(self):
        for code in ("missing_receipt", "unexpected_post_submission_traffic"):
            (self.root / "events").unlink(missing_ok=True)
            runtime, selected = self.make()
            with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
                task = asyncio.create_task(runtime.run(self.turn()))
                await self.started()
                self.submitted = code != "missing_receipt"
                self.factory.bridges[-1].code = code
                result = await asyncio.wait_for(task, 3)
            self.assertEqual((result.outcome, result.submission_delivered), ("failed", False))
            self.assertEqual(result.diagnostic_code, code)

    async def test_c_deadline_joins_the_bridge_first_and_is_reported_as_the_deadline(self):
        """A real run's CLI shuts its MCP server down when it is told to stop, so a
        bridge left open at C's deadline recorded the relay's exit as `mcp_failure`
        and hid the deadline that ended the turn."""
        runtime, selected = self.make(provider="claude", behavior="runtime_idle")
        turn = self.turn()
        timed = NativeTurn(turn.prompt, turn.tool_names, turn.make_mcp_handler, turn.stop,
                           turn.submitted, 1_000_000_000)
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
            task = asyncio.create_task(runtime.run(timed))
            events = await self.started()
            result = await asyncio.wait_for(task, 6)
        self.assertEqual((result.outcome, result.submission_delivered, result.diagnostic_code),
                         ("failed", False, "deadline"))
        self.assertTrue(self.factory.bridges[0].closed)
        self.assertFalse(alive(events[0]["pid"]))
        kinds = [kind for kind, _ in self.sink.events]
        self.assertIn("native_deadline", kinds)
        self.assertNotIn("native_bridge_failure", kinds)
        self.assertEqual(self.sink.events[kinds.index("native_deadline")][1],
                         {"seconds": 1, "submission_attempted": False})

    async def test_authoritative_cancel_racing_receipt_wins_and_joins_the_group(self):
        runtime, selected = self.make(escaped_child=True)
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
            task = asyncio.create_task(runtime.run(self.turn()))
            events = await await_events(self.root, 2)
            await asyncio.sleep(.05)
            self.submitted = True
            self.stop.set("deadline")
            result = await asyncio.wait_for(task, 3)
        self.assertEqual((result.outcome, result.submission_delivered, result.diagnostic_code),
                         ("cancelled", False, "deadline"))
        self.assertFalse(alive(events[0]["pid"]))
        terminate(events[1]["escaped_child_pid"])

    async def test_cleanup_failure_dominates_cancel_and_latches_shutdown(self):
        runtime, selected = self.make()
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
            task = asyncio.create_task(runtime.run(self.turn()))
            await self.started()
            self.factory.bridges[-1].cleanup_failure = True
            self.stop.set()
            with self.assertRaises(CleanupError):
                await asyncio.wait_for(task, 3)
        self.assertTrue(self.factory.bridges[-1].closed)
        with self.assertRaises(CleanupError):
            await runtime.shutdown()
        with self.assertRaises(CleanupError):
            await runtime.run(self.turn())

    async def test_task_cancellation_cannot_skip_the_bridge_join(self):
        runtime, selected = self.make()
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
            task = asyncio.create_task(runtime.run(self.turn()))
            await self.started()
            task.cancel()
            with self.assertRaises(asyncio.CancelledError):
                await asyncio.wait_for(task, 3)
        self.assertTrue(self.factory.bridges[-1].closed)

    async def test_stop_before_launch_spawns_nothing_and_joins_the_bridge(self):
        runtime, selected = self.make()
        self.factory.gate = asyncio.Event()
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
            task = asyncio.create_task(runtime.run(self.turn()))
            while not self.factory.bridges:
                await asyncio.sleep(.01)
            self.stop.set()
            self.factory.gate.set()
            result = await asyncio.wait_for(task, 2)
        self.assertEqual(result.outcome, "cancelled")
        self.assertFalse((self.root / "events").exists())
        self.assertTrue(self.factory.bridges[-1].closed)

    async def test_traffic_budget_remains_exhausted_on_later_turn(self):
        runtime, selected = self.make(limits=AgentLimits(traffic_bytes=1, minimum_free_bytes=0))
        runtime.budget.charge("prompt", 1, 1)
        with self.assertRaises(Exception):
            runtime.budget.charge("mcp_request", 1, 0)
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)) as verify:
            for _ in range(2):
                result = await runtime.run(self.turn())
                self.assertEqual(result.outcome, "failed")
                self.assertEqual(result.diagnostic_code, "agent_traffic_exhausted")
            verify.assert_not_called()
        self.assertEqual(runtime.budget.usage()["bytes"], 1)

    async def test_native_workspace_growth_stops_and_latches_input(self):
        runtime, selected = self.make(behavior="runtime_workspace", bytes=4096,
                                      limits=AgentLimits(workspace_bytes=1024, minimum_free_bytes=0))
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
            result = await asyncio.wait_for(runtime.run(self.turn()), 3)
            self.assertEqual(result.outcome, "failed")
            self.assertEqual(runtime.allowance.failure(), "agent_workspace_exhausted")
            second = await runtime.run(self.turn())
            self.assertEqual(second.outcome, "failed")

    async def test_shutdown_joins_active_native_then_removes_its_owned_scratch(self):
        runtime, selected = self.make()
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
            task = asyncio.create_task(runtime.run(self.turn()))
            await self.started()
            owned = runtime.root
            await asyncio.wait_for(runtime.shutdown(), 3)
            self.assertEqual((await task).outcome, "cancelled")
        self.assertFalse(owned.exists())


if __name__ == "__main__":
    unittest.main()
