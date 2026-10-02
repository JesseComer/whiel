# Author: Fangzhu Shen
"""Real C relay/bridge exchanges, accounting and joined cleanup."""

import asyncio
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from agent_houdini import mcp_stdio as relay
from agent_houdini.agent_transport import AgentTrafficExhausted, McpTransport, MeteredRequestAccess
from agent_houdini.protocol import QueryUnavailable, RequestRevoked, SubmissionRejected
from agent_houdini.runtime_types import CleanupError, RequestView


class Stop:
    def __init__(self):
        self.event = asyncio.Event()
        self.reason = "cancelled"

    def requested(self):
        return self.event.is_set()

    async def wait(self):
        await self.event.wait()
        return self.reason

    def set(self, reason="cancelled"):
        self.reason = reason
        self.event.set()


class Budget:
    def __init__(self, refuse=None):
        self.charges = []
        self.refuse = refuse

    def charge(self, leg, length, messages=0):
        self.charges.append((leg, length, messages))
        if leg == self.refuse:
            raise RuntimeError("private resource detail")


class Events:
    def __init__(self):
        self.items = []

    def emit(self, kind, fields):
        self.items.append((kind, dict(fields)))


class Access:
    view = RequestView(1, b"{}", b"{}", None)
    query_names = ("history",)

    def __init__(self):
        self.calls = []
        self.submit_gate = asyncio.Event()
        self.submit_gate.set()

    async def query(self, name, arguments):
        self.calls.append((name, arguments))
        return b' {"status":"ok"} '

    async def submit(self, proposal):
        self.calls.append(("submit", proposal))
        await self.submit_gate.wait()


class MeteredTests(unittest.IsolatedAsyncioTestCase):
    async def test_exact_payloads_and_receipt_are_counted_once_without_changing_bytes(self):
        source, budget = Access(), Budget()
        access = MeteredRequestAccess(source, budget)
        self.assertIs(access.view, source.view)
        self.assertEqual(access.query_names, source.query_names)
        result = await access.query("history", b' {"bad":true} ')
        self.assertEqual(result, b' {"status":"ok"} ')
        proposal = b' {"bad":"\xff"} '
        source.submit_gate.clear()
        task = asyncio.create_task(access.submit(proposal))
        await asyncio.sleep(0)
        self.assertFalse(access.receipt_received)
        self.assertTrue(access.submission_attempted)
        source.submit_gate.set()
        await task
        self.assertTrue(access.receipt_received)
        self.assertEqual(source.calls, [("history", b' {"bad":true} '), ("submit", proposal)])
        self.assertEqual(budget.charges, [("canonical_request", 14, 1), ("canonical_reply", len(result), 1),
                                          ("canonical_request", len(proposal), 1), ("canonical_reply", 0, 1)])

    async def test_refusal_receipt_and_cancellation_are_distinct(self):
        source, budget = Access(), Budget()
        access = MeteredRequestAccess(source, budget)
        async def unavailable(*_):
            raise QueryUnavailable("not negotiated")
        source.query = unavailable
        with self.assertRaises(QueryUnavailable):
            await access.query("other", b"{}")
        async def rejected(*_):
            raise SubmissionRejected("too_large")
        source.submit = rejected
        with self.assertRaises(SubmissionRejected):
            await access.submit(b"x")
        self.assertFalse(access.receipt_received)
        async def revoked(*_):
            raise RequestRevoked("deadline")
        source.submit = revoked
        with self.assertRaises(RequestRevoked):
            await access.submit(b"y")
        self.assertEqual(budget.charges, [("canonical_request", 2, 1), ("canonical_reply", 0, 1),
                                          ("canonical_request", 1, 1), ("canonical_reply", 0, 1),
                                          ("canonical_request", 1, 1)])

    async def test_canonical_budget_failure_cannot_manufacture_receipt(self):
        source, budget = Access(), Budget(refuse="canonical_reply")
        access = MeteredRequestAccess(source, budget)
        with self.assertRaises(AgentTrafficExhausted):
            await access.submit(b"{}")
        self.assertEqual(source.calls, [("submit", b"{}")])
        self.assertFalse(access.receipt_received)
        self.assertTrue(access.submission_attempted)
        untouched = Access()
        access = MeteredRequestAccess(untouched, Budget(refuse="canonical_request"))
        with self.assertRaises(AgentTrafficExhausted):
            await access.submit(b"{}")
        self.assertFalse(access.submission_attempted)
        self.assertEqual(untouched.calls, [])


class BridgeTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="c-mcp-", dir=os.path.realpath("/tmp"))
        self.addCleanup(self.directory.cleanup)
        self.work = Path(self.directory.name)
        self.stop, self.budget, self.events = Stop(), Budget(), Events()
        self.access = MeteredRequestAccess(Access(), self.budget)
        self.lines = []
        self.bridges = []

    async def create(self, handler=None, **options):
        async def default_handler(line):
            self.lines.append(line)
            return b"reply\n"
        bridge = await McpTransport.create(self.work, handler or default_handler,
                                          self.stop, self.budget, self.events, **options)
        self.bridges.append(bridge)
        self.addAsyncCleanup(bridge.close_and_join)
        return bridge

    async def peer(self, bridge, token=None):
        reader, writer = await asyncio.open_unix_connection(bridge.launch.environment[relay.SOCKET_ENV])
        identity = relay.token_bytes(token or bridge.launch.environment[relay.TOKEN_ENV])
        writer.write(relay.encode_header(relay.HELLO, 0, 32) + identity)
        await writer.drain()
        header = relay.decode_header(await reader.readexactly(relay.HEADER.size))
        self.assertEqual(header, (relay.READY, 0, 0))
        self.addAsyncCleanup(self.close_peer, writer)
        return reader, writer

    @staticmethod
    async def close_peer(writer):
        writer.close()
        try:
            await writer.wait_closed()
        except (OSError, ConnectionError):
            pass

    async def exchange(self, reader, writer, sequence, data):
        writer.write(relay.encode_header(relay.BEGIN, sequence, len(data)))
        await writer.drain()
        self.assertEqual(relay.decode_header(await reader.readexactly(relay.HEADER.size)),
                         (relay.RESERVED, sequence, 0))
        writer.write(data)
        await writer.drain()
        kind, actual, length = relay.decode_header(await reader.readexactly(relay.HEADER.size))
        self.assertEqual((kind, actual), (relay.RESULT, sequence))
        return await reader.readexactly(length)

    async def wait_failure(self, bridge):
        async def wait():
            while bridge.failure() is None:
                await asyncio.sleep(0.001)
            return bridge.failure()
        return await asyncio.wait_for(wait(), 1)

    async def test_truncation_after_a_completed_receipt_still_latches_failure(self):
        async def handler(_line):
            await self.access.submit(b"opaque")
            return b"submission receipt\n"

        bridge = await self.create(handler)
        reader, writer = await self.peer(bridge)
        await self.exchange(reader, writer, 1, b"submit\n")
        self.assertTrue(self.access.receipt_received)
        writer.transport.abort()
        self.assertEqual(await self.wait_failure(bridge), "mcp_failure")

    async def test_real_standalone_relay_and_all_five_legs_exactly_once(self):
        async def handler(line):
            self.lines.append(line)
            if line == b"query\n":
                await self.access.query("history", b"{}")
                return b"query result\n"
            await self.access.submit(b' {"proposal":"opaque"} ')
            return b"submission receipt\n"
        # Copy only the executable script; its isolated interpreter cannot import
        # the package or any B code, and receives only the two C bootstrap values.
        standalone = self.work / "relay.py"
        shutil.copyfile(Path(relay.__file__), standalone)
        standalone.chmod(0o755)
        bridge = await self.create(handler, relay_path=standalone)
        self.budget.charge("prompt", 6, 1)
        process = await asyncio.create_subprocess_exec(
            bridge.launch.argv[0], "-I", bridge.launch.argv[1],
            stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE, env=dict(bridge.launch.environment), cwd=self.work)
        output, errors = await asyncio.wait_for(process.communicate(b"query\nsubmit\n"), 3)
        self.assertEqual(process.returncode, 0, errors)
        self.assertEqual(output, b"query result\nsubmission receipt\n")
        self.assertEqual(errors, b"")
        self.assertEqual(self.lines, [b"query\n", b"submit\n"])
        self.assertTrue(self.access.receipt_received)
        self.assertIsNone(bridge.failure())
        self.assertEqual(set(bridge.launch.environment), {relay.SOCKET_ENV, relay.TOKEN_ENV})
        self.assertEqual(bridge.launch.readonly_resources, (Path(bridge.launch.argv[0]), standalone))
        self.assertEqual(self.budget.charges,
                         [("prompt", 6, 1), ("mcp_request", 6, 1),
                          ("canonical_request", 2, 1), ("canonical_reply", len(b' {"status":"ok"} '), 1),
                          ("mcp_reply", len(b"query result\n"), 1), ("mcp_request", 7, 1),
                          ("canonical_request", len(b' {"proposal":"opaque"} '), 1),
                          ("canonical_reply", 0, 1), ("mcp_reply", len(b"submission receipt\n"), 1)])
        await bridge.close_and_join()
        self.assertFalse(Path(bridge.launch.environment[relay.SOCKET_ENV]).exists())
        self.assertTrue(all(task.done() for task in bridge._connections))

    async def test_raw_eof_inside_a_pending_exchange_fails_closed(self):
        source = self.access._access
        source.submit_gate.clear()
        async def handler(line):
            await self.access.submit(line)
            return b"receipt\n"
        bridge = await self.create(handler)
        reader, writer = await self.peer(bridge)
        writer.write(relay.encode_header(relay.BEGIN, 1, 7))
        await writer.drain()
        self.assertEqual(relay.decode_header(await reader.readexactly(relay.HEADER.size)),
                         (relay.RESERVED, 1, 0))
        # The raw peer ends its input while the canonical submission is still
        # pending. EOF cannot synthesize a receipt or complete the exchange.
        writer.write(b"submit\n" + relay.encode_header(relay.EOF, 1))
        await writer.drain()
        async def submitted():
            while not source.calls:
                await asyncio.sleep(0)
        await asyncio.wait_for(submitted(), 1)
        incoming = asyncio.create_task(reader.read(1))
        try:
            done, _ = await asyncio.wait((incoming,), timeout=.02)
            self.assertFalse(done)
            self.assertTrue(self.access.submission_attempted)
            self.assertFalse(self.access.receipt_received)
            source.submit_gate.set()
            self.assertEqual(await self.wait_failure(bridge), "mcp_failure")
            self.assertTrue(self.access.receipt_received)
            await bridge.close_and_join()
            self.assertTrue(all(task.done() for task in bridge._connections))
        finally:
            incoming.cancel()
            await asyncio.gather(incoming, return_exceptions=True)

    async def test_fragmentation_empty_notifications_and_opaque_lines(self):
        async def handler(line):
            self.lines.append(line)
            return None if line == b"notify\n" else b"\xffreply\n"
        bridge = await self.create(handler)
        reader, writer = await self.peer(bridge)
        self.assertEqual(await self.exchange(reader, writer, 1, b"\xffopa"), b"")
        self.assertEqual(await self.exchange(reader, writer, 2, b"que\n"), b"\xffreply\n")
        self.assertEqual(await self.exchange(reader, writer, 3, b"notify\n"), b"")
        self.assertEqual(self.lines, [b"\xffopaque\n", b"notify\n"])
        self.assertEqual(self.budget.charges, [("mcp_request", 4, 1), ("mcp_request", 4, 0),
                                              ("mcp_reply", 7, 1), ("mcp_request", 7, 1)])
        writer.write(relay.encode_header(relay.EOF, 4))
        await writer.drain()
        self.assertEqual(relay.decode_header(await reader.readexactly(relay.HEADER.size)), (relay.CLOSED, 4, 0))
        self.assertIsNone(bridge.failure())

    async def test_observed_over_cap_chunk_is_charged_before_body_is_refused(self):
        bridge = await self.create()
        reader, writer = await self.peer(bridge)
        with patch.object(relay, "MAX_LINE_BYTES", 8):
            await self.exchange(reader, writer, 1, b"1234")
            await self.exchange(reader, writer, 2, b"5678")
            writer.write(relay.encode_header(relay.BEGIN, 3, 2))
            await writer.drain()
            self.assertEqual(await self.wait_failure(bridge), "mcp_failure")
            self.assertEqual(await reader.read(), b"")
        self.assertEqual(self.budget.charges, [("mcp_request", 4, 1), ("mcp_request", 4, 0),
                                              ("mcp_request", 2, 0)])
        self.assertEqual(self.lines, [])

    async def test_raw_and_canonical_resource_failures_latch_once(self):
        self.budget.refuse = "mcp_request"
        bridge = await self.create()
        reader, writer = await self.peer(bridge)
        writer.write(relay.encode_header(relay.BEGIN, 1, 2))
        await writer.drain()
        self.assertEqual(await self.wait_failure(bridge), "agent_traffic_exhausted")
        self.assertEqual(await reader.read(), b"")
        self.budget.refuse = "canonical_reply"
        async def handler(line):
            await self.access.submit(line)
            return b"receipt\n"
        other = await self.create(handler)
        reader, writer = await self.peer(other)
        writer.write(relay.encode_header(relay.BEGIN, 1, 2))
        await writer.drain()
        await reader.readexactly(relay.HEADER.size)
        writer.write(b"x\n")
        await writer.drain()
        self.assertEqual(await self.wait_failure(other), "agent_traffic_exhausted")

    async def test_cancel_joins_a_blocked_handler_without_conflating_it_with_failure(self):
        entered, ended = asyncio.Event(), asyncio.Event()
        async def handler(_):
            entered.set()
            try:
                await asyncio.Event().wait()
            finally:
                ended.set()
        bridge = await self.create(handler)
        reader, writer = await self.peer(bridge)
        writer.write(relay.encode_header(relay.BEGIN, 1, 2))
        await writer.drain()
        await reader.readexactly(relay.HEADER.size)
        writer.write(b"x\n")
        await writer.drain()
        await entered.wait()
        self.stop.set("deadline")
        await asyncio.wait_for(bridge.close_and_join(), 1)
        self.assertTrue(ended.is_set())
        self.assertIsNone(bridge.failure())
        self.assertEqual(await reader.read(), b"")

    async def test_reply_budget_refusal_and_a_disconnected_peer_both_latch(self):
        self.budget.refuse = "mcp_reply"
        bridge = await self.create()
        reader, writer = await self.peer(bridge)
        writer.write(relay.encode_header(relay.BEGIN, 1, 2))
        await writer.drain()
        await reader.readexactly(relay.HEADER.size)
        writer.write(b"x\n")
        await writer.drain()
        self.assertEqual(await self.wait_failure(bridge), "agent_traffic_exhausted")
        self.assertEqual(await reader.read(), b"")
        self.budget.refuse = None
        async def handler(line):
            await self.access.submit(line)
            return b"receipt\n"
        other = await self.create(handler)
        reader, writer = await self.peer(other)
        await self.exchange(reader, writer, 1, b"x\n")
        await self.close_peer(writer)
        self.assertEqual(await self.wait_failure(other), "mcp_failure")

    async def test_unjoined_handler_is_a_distinct_cleanup_error(self):
        entered, ignored, release = asyncio.Event(), asyncio.Event(), asyncio.Event()
        async def handler(_):
            entered.set()
            try:
                await asyncio.Event().wait()
            except asyncio.CancelledError:
                ignored.set()
                await release.wait()
            return b"late\n"
        bridge = await McpTransport.create(self.work, handler, self.stop, self.budget, self.events,
                                          cleanup_timeout=0.02)
        try:
            reader, writer = await self.peer(bridge)
            writer.write(relay.encode_header(relay.BEGIN, 1, 2))
            await writer.drain()
            await reader.readexactly(relay.HEADER.size)
            writer.write(b"x\n")
            await writer.drain()
            await entered.wait()
            with self.assertRaises(CleanupError):
                await asyncio.wait_for(bridge.close_and_join(), 1)
            self.assertTrue(ignored.is_set())
            self.assertTrue(any(not task.done() for task in bridge._connections))
        finally:
            # Release the intentionally uncooperative fixture and join it so the
            # negative test itself leaves no tasks after proving the error.
            release.set()
            await asyncio.gather(*bridge._connections, return_exceptions=True)
            Path(bridge.launch.environment[relay.SOCKET_ENV]).unlink(missing_ok=True)

    async def test_wrong_identity_phase_multiple_lines_and_truncation_fail_closed(self):
        bridge = await self.create()
        reader, writer = await asyncio.open_unix_connection(bridge.launch.environment[relay.SOCKET_ENV])
        writer.write(relay.encode_header(relay.HELLO, 0, 32) + b"z" * 32)
        await writer.drain()
        self.assertEqual(await self.wait_failure(bridge), "mcp_failure")
        self.assertEqual(await reader.read(), b"")
        await self.close_peer(writer)
        other = await self.create()
        reader, writer = await self.peer(other)
        writer.write(relay.encode_header(relay.BEGIN, 1, 4))
        await writer.drain()
        await reader.readexactly(relay.HEADER.size)
        writer.write(b"x\ny\n")
        await writer.drain()
        self.assertEqual(await self.wait_failure(other), "mcp_failure")
        self.assertEqual(self.lines, [])
        third = await self.create()
        reader, writer = await self.peer(third)
        writer.write(relay.encode_header(relay.BEGIN, 1, 4))
        await writer.drain()
        await reader.readexactly(relay.HEADER.size)
        writer.write(b"x")
        await writer.drain()
        await self.close_peer(writer)
        self.assertEqual(await self.wait_failure(third), "mcp_failure")
        self.assertEqual(self.lines, [])

    async def test_incomplete_line_and_malformed_reply_fail(self):
        bridge = await self.create()
        reader, writer = await self.peer(bridge)
        await self.exchange(reader, writer, 1, b"part")
        writer.write(relay.encode_header(relay.EOF, 2))
        await writer.drain()
        self.assertEqual(await self.wait_failure(bridge), "mcp_failure")
        for reply in (b"missing newline", b"two\nlines\n"):
            async def handler(line):
                await self.access.submit(line)
                return reply
            other = await self.create(handler)
            reader, writer = await self.peer(other)
            writer.write(relay.encode_header(relay.BEGIN, 1, 2))
            await writer.drain()
            await reader.readexactly(relay.HEADER.size)
            writer.write(b"x\n")
            await writer.drain()
            self.assertEqual(await self.wait_failure(other), "mcp_failure")


if __name__ == "__main__":
    unittest.main()
