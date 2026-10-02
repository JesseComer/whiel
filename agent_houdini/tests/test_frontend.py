# Author: Fangzhu Shen
"""Full C composition against a deterministic B wire endpoint, without models."""

import asyncio
import json
import os
from pathlib import Path
import signal
import sys
import tempfile
import unittest
from unittest.mock import AsyncMock, patch

from agent_houdini.agent_runtime import NativeAgentRuntime
from agent_houdini.agent_runtime import DEADLINE_DIAGNOSTIC, deadline_seconds
from agent_houdini.frontend import run_endpoint
from agent_houdini.json_wire import decode, encode
from agent_houdini.tests.test_native_process_tree import alive
from agent_houdini.prompt import render_prompt
from agent_houdini.protocol import API_VERSION, QUERY_NAMES, encode_packet, read_packet
from agent_houdini.providers import claude, codex
from agent_houdini.resource_limits import AgentLimits, AgentTrafficBudget
from agent_houdini.runtime_types import CleanupError, NativeOptions, NativeResult
from agent_houdini.tool_catalog import default_catalog
from agent_houdini.tests.test_native_providers import MODEL


TOKEN = "ab" * 32
NATIVE_FIXTURE = Path(__file__).parent / "fixtures/native_fixture.py"
# A submission the coordinator forwards untouched: it echoes the binding of
# the response example these tests send, so no local check answers it in C's
# place and the bytes reach the wire exactly as written.
FORWARDED_PAYLOAD = (b'{"binding":{"unchanged":true},"clauses":[],"dropped":[],'
                     b'"kind":"candidate_clauses","schema_version":4}')


class Sink:
    def __init__(self):
        self.items = []

    def emit(self, kind, fields):
        self.items.append((kind, dict(fields)))


class Host:
    def __init__(self, root):
        self.root = root
        self.accepted = asyncio.get_running_loop().create_future()
        self.writer = self.reader = self.server = self.endpoint = None
        self.bseq = self.cseq = 0
        self.environment = {"WHIEL_PROPOSER_SOCKET": str(root / "b.sock"), "WHIEL_PROPOSER_TOKEN": TOKEN}
        self.budget = AgentTrafficBudget()
        self.events = Sink()

    async def start(self, factory, *, budget=None, options=None, operations=QUERY_NAMES,
                    records=None):
        def accepted(reader, writer):
            if self.accepted.done():
                writer.close()
            else:
                self.accepted.set_result((reader, writer))
        self.server = await asyncio.start_unix_server(accepted, self.environment["WHIEL_PROPOSER_SOCKET"])
        if budget is not None:
            self.budget = budget
        options = options or NativeOptions(encode({"provider": "codex", "model": MODEL}), "local", self.root)
        self.endpoint = asyncio.create_task(run_endpoint(
            options, self.budget, self.events, runner_factory=factory,
            environment=self.environment, records=records))
        self.reader, self.writer = await asyncio.wait_for(self.accepted, 2)
        packet, _ = await self.receive()
        assert packet["operation"]["kind"] == "hello"
        await self.send(None, {"kind": "ready", "api": {"version": API_VERSION, "operations": list(operations)}})
        return self

    async def send(self, request_id, operation, parts=()):
        for part in encode_packet(TOKEN, self.bseq, request_id, operation, parts):
            self.writer.write(part)
        await self.writer.drain()
        self.bseq += 1

    async def receive(self):
        value = await asyncio.wait_for(read_packet(self.reader, TOKEN, self.cseq, "to_b"), 5)
        self.cseq += 1
        return value

    async def request(self, number=1, *, observation=None, example=None, budget=None):
        observation = ({"schema_version": 15, "operation": "proposer_observation",
                        "feedback": {"remaining_search_budget_ns": "30000000000"},
                        "future_optional": {"λ": [1, 2]}} if observation is None else observation)
        example = b' {"kind":"candidate_clauses","binding":{"unchanged":true}} ' if example is None else example
        parts = (encode(observation), example)
        await self.send(number, {"kind": "request", "observation_bytes": len(parts[0]),
                                "response_example_bytes": len(parts[1]), "remaining_request_budget_ns": budget}, parts)
        return observation, example

    async def complete(self, expected, number=1):
        packet, parts = await self.receive()
        assert packet["operation"] == {"kind": "complete", "outcome": expected}, packet
        assert parts == ()
        await self.send(number, {"kind": "request_closed"})

    async def shutdown(self, reason="complete"):
        await self.send(None, {"kind": "shutdown", "reason": reason})
        packet, _ = await self.receive()
        assert packet["operation"] == {"kind": "closed"}
        return await asyncio.wait_for(self.endpoint, 3)

    async def close(self):
        if self.endpoint is not None and not self.endpoint.done():
            self.endpoint.cancel()
        if self.endpoint is not None:
            await asyncio.gather(self.endpoint, return_exceptions=True)
        if self.writer is not None:
            self.writer.close()
            try:
                await self.writer.wait_closed()
            except (OSError, ConnectionError):
                pass
        if self.server is not None:
            self.server.close()
            await self.server.wait_closed()
        (self.root / "b.sock").unlink(missing_ok=True)


class Runner:
    def __init__(self, actions=None):
        self.turns = []
        self.actions = actions
        self.shutdowns = 0
        self.stopped = asyncio.Event()
        self.cleanup_failure = False

    async def run(self, turn):
        self.turns.append(turn)
        if self.actions is not None:
            return await self.actions(turn)
        return NativeResult("clean_exit", False, None)

    async def shutdown(self):
        self.shutdowns += 1
        self.stopped.set()
        if self.cleanup_failure:
            raise CleanupError("synthetic native cleanup failure")

    def factory(self, *_):
        return self


class FrontendTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="c-end-", dir=os.path.realpath("/tmp"))
        self.root = Path(self.temporary.name)
        self.addCleanup(self.temporary.cleanup)
        self.hosts = []

    async def host(self, factory, **options):
        host = Host(self.root)
        self.hosts.append(host)
        self.addAsyncCleanup(host.close)
        return await host.start(factory, **options)

    def native_factory(self, provider, actions, **settings):
        script = self.root / "native.py"
        script.write_text("#!" + sys.executable + "\n" + NATIVE_FIXTURE.read_text())
        script.chmod(0o700)
        (self.root / "native.json").write_text(json.dumps({
            "synthetic_fixture": True, "events": str(self.root / "native-events"),
            "actions": actions, **settings}))
        if provider == "claude":
            selected = claude.ClaudeIdentity(str(script), MODEL, "medium", self.root / ".claude")
        else:
            selected = codex.CodexIdentity(str(script), MODEL, "medium")
        holder = []
        def factory(*arguments):
            runner = NativeAgentRuntime(*arguments)
            holder.append(runner)
            return runner
        return factory, selected, holder

    def native_events(self):
        path = self.root / "native-events"
        return [] if not path.exists() else [json.loads(line) for line in path.read_text().splitlines()]

    async def test_actual_frontend_prompt_query_and_opaque_submit_for_both_providers(self):
        payload = ' \n{"broken":"λ", "broken":1}\t'
        actions = [{"method": "tools/call", "params": {"name": "ledger", "arguments": {"cursor": None}}},
                   {"method": "tools/call", "params": {"name": "submit", "arguments": {"payload": payload}}}]
        for provider in ("codex", "claude"):
            with self.subTest(provider=provider):
                factory, selected, holder = self.native_factory(provider, actions, fragment_bytes=3)
                with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
                    host = await self.host(factory, operations=("ledger",),
                                           options=NativeOptions(encode({"provider": provider, "model": MODEL}),
                                                                 "local", self.root))
                    observation, example = await host.request(budget="0")
                    packet, parts = await host.receive()
                    self.assertEqual(packet["operation"]["name"], "ledger")
                    self.assertEqual(parts, (b'{"cursor":null}',))
                    reply = b'{"operation":"ledger","data":{"clauses":[]}}'
                    await host.send(1, {"kind": "query_result", "query_id": 1, "result_bytes": len(reply)}, (reply,))
                    packet, parts = await host.receive()
                    self.assertEqual(packet["operation"]["kind"], "submit")
                    self.assertEqual(parts, (payload.encode(),))
                    await host.send(1, {"kind": "submitted"})
                    await host.complete("response")
                    self.assertEqual(await host.shutdown(), 0)
                records = self.native_events()
                start = next(row for row in records if "pid" in row)
                # C advertises exactly the tools this request authorized, so
                # the expected rendering names the same policy.
                self.assertEqual(start["prompt"].encode(),
                                 render_prompt(observation, example,
                                               tools=default_catalog().tools_for_policy(("ledger",))))
                self.assertTrue(any(row.get("method") == "tools/call" and
                                    row["reply"]["result"]["content"][0]["text"] == "Submission received."
                                    for row in records))
                self.assertFalse(alive(start["pid"]))
                self.assertIsNone(holder[0].root)
                self.assertTrue(holder[0].closed)
                self.assertEqual(host.budget.usage()["legs"]["prompt"][1], 1)
                await host.close()
                (self.root / "native-events").unlink()

    async def test_no_mcp_receipt_before_complete_canonical_receipt(self):
        # A payload the coordinator forwards: it carries the response
        # example's own binding, so no local check answers it in C's place.
        payload = FORWARDED_PAYLOAD.decode("utf-8")
        actions = [{"method": "tools/call", "params": {"name": "submit", "arguments": {"payload": payload}}}]
        factory, selected, holder = self.native_factory("codex", actions)
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
            host = await self.host(factory)
            await host.request()
            packet, parts = await host.receive()
            self.assertEqual(packet["operation"]["kind"], "submit")
            self.assertEqual(parts, (FORWARDED_PAYLOAD,))
            await asyncio.sleep(.04)
            self.assertFalse(any(row.get("method") == "tools/call" for row in self.native_events()))
            host.writer.transport.abort()
            self.assertEqual(await asyncio.wait_for(host.endpoint, 3), 1)
        self.assertTrue(holder[0].closed)
        self.assertIsNone(holder[0].root)

    async def test_per_request_skills_are_frozen_local_and_reload_on_next_request(self):
        path = self.root / "skills.json"
        path.write_bytes(b'{"guide":"before"}')
        values = []
        async def act(turn):
            path.write_bytes(b'{"guide":"after"}')
            async def ready():
                raise AssertionError("local skill must not await native readiness")
            handler = turn.make_mcp_handler(ready)
            await handler(encode({"jsonrpc": "2.0", "id": 1, "method": "initialize"}) + b"\n")
            result = decode(await handler(encode({"jsonrpc": "2.0", "id": 2, "method": "tools/call",
                                                  "params": {"name": "get_skill", "arguments": {"id": "guide"}}}) + b"\n"))
            values.append(decode(result["result"]["content"][0]["text"].encode())["content"])
            return NativeResult("clean_exit", False, None)
        runner = Runner(act)
        host = Host(self.root)
        host.environment["WHIEL_AGENT_SKILLS_FILE"] = str(path)
        self.addAsyncCleanup(host.close)
        await host.start(runner.factory, operations=())
        for request_id in (1, 2):
            await host.request(request_id)
            await host.complete("no_response", request_id)
        self.assertEqual(values, ["before", "after"])
        self.assertEqual(await host.shutdown(), 0)
        self.assertTrue(all("get_skill" in turn.tool_names for turn in runner.turns))
        self.assertEqual(host.budget.usage()["legs"]["canonical_request"], (0, 0))

    async def test_native_deadline_comes_from_the_request_budget_b_sent(self):
        runner = Runner()
        host = await self.host(runner.factory)
        await host.request(budget="2500000000")
        await host.complete("no_response")
        await host.request(2)
        await host.complete("no_response", 2)
        # The observation body still carries a search-budget hint; C ignores it.
        self.assertEqual([turn.remaining_budget_ns for turn in runner.turns], [2500000000, None])
        self.assertEqual(deadline_seconds(2500000000), 2)
        self.assertIsNone(deadline_seconds(None))
        self.assertEqual(deadline_seconds(1), 1)
        self.assertEqual(await host.shutdown(), 0)

    async def test_c_s_own_deadline_completes_no_response_not_a_transport_failure(self):
        """C stopping its own turn is "finished without submitting", not a fault.

        C floors B's remaining request budget to whole seconds, so C's timer can
        fire up to a second before B's. Completing that as `failure` had B
        record a transport failure -- the retryable class -- for a consultation
        whose clock had simply run out, while the same event was recorded as
        `cancelled` whenever B's exact timer won the race instead. A deadline
        reached with a submission attempted stays a failure.
        """
        attempted = [False, True]
        async def act(turn):
            return NativeResult("failed", attempted.pop(0), DEADLINE_DIAGNOSTIC)
        runner = Runner(act)
        host = await self.host(runner.factory)
        for request_id, expected in enumerate(("no_response", "failure"), start=1):
            await host.request(request_id, budget="5000000000")
            await host.complete(expected, request_id)
        self.assertEqual([fields["diagnostic_code"] for kind, fields in host.events.items
                          if kind == "request_outcome"], [DEADLINE_DIAGNOSTIC] * 2)
        self.assertEqual(await host.shutdown(), 0)

    async def test_a_provider_that_cannot_run_ends_the_input_after_three_failures(self):
        """A CLI that fails every consultation at once is not retried forever.

        The verifier reopens a failed consultation immediately, so a provider
        that cannot start would be launched thousands of times per input. After
        three consecutive native failures with nothing submitted the endpoint
        leaves without completing the open request; one good consultation in
        between resets the count.
        """
        results = [NativeResult("failed", False, "native_failure")] * 2
        async def act(turn):
            if results:
                return results.pop(0)
            return NativeResult("failed", False, "native_failure")
        runner = Runner(act)
        host = await self.host(runner.factory)
        for request_id in (1, 2):
            await host.request(request_id)
            await host.complete("failure", request_id)
        # A consultation that ends any other way resets the count.
        runner.actions = None
        await host.request(3)
        await host.complete("no_response", 3)
        runner.actions = act
        for request_id in (4, 5):
            await host.request(request_id)
            await host.complete("failure", request_id)
        await host.request(6)
        self.assertEqual(await asyncio.wait_for(host.endpoint, 3), 1)
        self.assertEqual([fields["consecutive_native_failures"]
                          for kind, fields in host.events.items if kind == "provider_unusable"], [3])

    async def test_cancellation_during_native_work_completes_failure_and_can_continue(self):
        async def act(turn):
            reason = await turn.stop.wait()
            return NativeResult("cancelled", False, reason)
        runner = Runner(act)
        host = await self.host(runner.factory)
        await host.request(budget="0")
        while not runner.turns:
            await asyncio.sleep(0)
        await host.send(1, {"kind": "cancel", "reason": "cancelled"})
        await host.complete("failure")
        self.assertEqual(await runner.turns[0].stop.wait(), "cancelled")
        runner.actions = None
        await host.request(2)
        await host.complete("no_response", 2)
        self.assertEqual(await host.shutdown(), 0)

    async def test_shutdown_during_native_work_joins_before_closed(self):
        ended = asyncio.Event()
        async def act(turn):
            reason = await turn.stop.wait()
            ended.set()
            return NativeResult("cancelled", False, reason)
        runner = Runner(act)
        host = await self.host(runner.factory)
        await host.request()
        while not runner.turns:
            await asyncio.sleep(0)
        self.assertEqual(await host.shutdown("cancelled"), 0)
        self.assertTrue(ended.is_set())
        self.assertEqual(runner.shutdowns, 1)

    async def test_resource_latch_starts_no_later_native_work(self):
        runner = Runner()
        budget = AgentTrafficBudget(AgentLimits(traffic_bytes=0))
        host = await self.host(runner.factory, budget=budget)
        for number in (1, 2, 3):
            await host.request(number)
            await host.complete("source_exhausted", number)
        self.assertEqual(runner.turns, [])
        self.assertEqual(await host.shutdown(), 0)
        self.assertEqual(budget.failure(), "agent_traffic_exhausted")

    async def test_resource_after_submission_uses_failure_then_source_exhausted(self):
        async def act(turn):
            async def ready():
                pass
            handler = turn.make_mcp_handler(ready)
            await handler(encode({"jsonrpc": "2.0", "id": 1, "method": "initialize"}) + b"\n")
            await handler(encode({"jsonrpc": "2.0", "id": 2, "method": "tools/call",
                                  "params": {"name": "submit",
                                             "arguments": {"payload": FORWARDED_PAYLOAD.decode()}}})
                          + b"\n")
            return NativeResult("failed", False, "agent_native_time_exhausted")
        runner = Runner(act)
        host = await self.host(runner.factory)
        await host.request()
        packet, _ = await host.receive()
        self.assertEqual(packet["operation"]["kind"], "submit")
        await host.send(1, {"kind": "submitted"})
        await host.complete("failure")
        await host.request(2)
        await host.complete("source_exhausted", 2)
        self.assertEqual(len(runner.turns), 1)
        self.assertEqual(await host.shutdown(), 0)

    async def test_cleanup_failure_never_acknowledges_closed_or_returns_success(self):
        runner = Runner()
        runner.cleanup_failure = True
        host = await self.host(runner.factory)
        await host.request()
        await host.complete("no_response")
        await host.send(None, {"kind": "shutdown", "reason": "complete"})
        self.assertEqual(await asyncio.wait_for(host.endpoint, 3), 1)
        self.assertEqual(await host.reader.read(), b"")

    async def test_direct_local_sigint_joins_and_returns_130(self):
        async def act(turn):
            await turn.stop.wait()
            return NativeResult("cancelled", False, "cancelled")
        runner = Runner(act)
        host = await self.host(runner.factory)
        await host.request()
        while not runner.turns:
            await asyncio.sleep(0)
        os.kill(os.getpid(), signal.SIGINT)
        self.assertEqual(await asyncio.wait_for(host.endpoint, 3), 130)
        self.assertEqual(runner.shutdowns, 1)
        self.assertTrue(runner.stopped.is_set())

    async def test_invalid_bootstrap_and_broken_prompt_do_not_echo_secrets(self):
        runner, sink = Runner(), Sink()
        options = NativeOptions(b'{"provider":"codex","model":"model-a"}', "local", self.root)
        status = await run_endpoint(options, AgentTrafficBudget(), sink, runner_factory=runner.factory,
                                    environment={"WHIEL_PROPOSER_TOKEN": "private-secret"})
        self.assertEqual(status, 1)
        self.assertNotIn("private-secret", repr(sink.items))
        host = await self.host(runner.factory)
        with patch("agent_houdini.frontend.render_prompt", side_effect=ValueError("private-secret")):
            await host.request()
            await host.complete("failure")
        self.assertEqual(runner.turns, [])
        self.assertEqual(await host.shutdown(), 0)
        self.assertNotIn("private-secret", repr(host.events.items))


if __name__ == "__main__":
    unittest.main()
