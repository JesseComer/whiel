# Author: Fangzhu Shen
"""C wire3 conformance; B independently enforces all authority and limits."""

import asyncio
from pathlib import Path
import struct
import tempfile
import unittest

from agent_houdini import json_wire
from agent_houdini.protocol import (
    API_VERSION, MAX_CONTROL_BYTES, MAX_HEADER_BYTES, MAX_PACKET_BYTES, QUERY_NAMES,
    U64_MAX, ApiClient, EndpointError, ProtocolError, QueryUnavailable, RequestEvent, RequestRevoked,
    ShutdownEvent, SubmissionRejected, attachment_lengths, decode_header,
    encode_packet, next_sequence, read_packet,
)

TOKEN = "ab" * 32


def frame(operation, sequence=0, request_id=None):
    return {"wire_version": 3, "endpoint_token": TOKEN, "sequence": sequence,
            "request_id": request_id, "operation": operation}


def wire(value, attachments=()):
    data = json_wire.encode(value)
    return struct.pack(">I", len(data)) + data + b"".join(attachments)


class CountingReader:
    def __init__(self, data):
        self.data = data
        self.read_sizes = []

    async def readexactly(self, size):
        self.read_sizes.append(size)
        part, self.data = self.data[:size], self.data[size:]
        if len(part) != size:
            raise asyncio.IncompleteReadError(part, size)
        return part


class JsonWireTests(unittest.TestCase):
    def test_strict_utf8_duplicate_nonfinite_and_trailing_values(self):
        for data in (b"", b'{} {}', b'{"x":0,"x":1}', b'{"x":{"a":0,"a":1}}',
                     b"NaN", b"Infinity", b"-Infinity", b"1e99999", b'"\xff"',
                     b'"\\ud800"', b'"\\udc00"', b'"\\ud800x"', b"\xef\xbb\xbf{}"):
            with self.subTest(data=data), self.assertRaises(ValueError):
                json_wire.decode(data)
        self.assertEqual(json_wire.decode(b' "\\ud83d\\ude00" '), "😀")
        self.assertEqual(json_wire.decode(b' {"b":1,"a":[null,true,0.2]} \n'),
                         {"b": 1, "a": [None, True, 0.2]})

    def test_encoding_preserves_order_or_explicitly_sorts_without_ascii_expansion(self):
        value = {"z": {"b": "λ", "a": 3}, "a": []}
        self.assertEqual(json_wire.encode(value), '{"z":{"b":"λ","a":3},"a":[]}'.encode())
        self.assertEqual(json_wire.encode(value, sort_keys=True), '{"a":[],"z":{"a":3,"b":"λ"}}'.encode())
        for value in ({1: "x"}, {"a": float("nan")}, {"a": float("inf")}, "\ud800", object()):
            with self.subTest(value=repr(value)), self.assertRaises(ValueError):
                json_wire.encode(value)

    def test_positive_limits_and_depth(self):
        for limit in (0, -1, True):
            with self.assertRaises(ValueError):
                json_wire.decode(b"{}", maximum=limit)
        with self.assertRaises(ValueError):
            json_wire.decode(b"{}", maximum=1)
        self.assertEqual(json_wire.encode({}, maximum=2), b"{}")
        with self.assertRaises(ValueError):
            json_wire.encode({"a": "λ"}, maximum=4)
        with self.assertRaises(ValueError):
            json_wire.decode(b"[" * 130 + b"0" + b"]" * 130)


class PacketTests(unittest.IsolatedAsyncioTestCase):
    async def test_fragmented_packets_and_opaque_proposals(self):
        proposal = b'  {"bad":"\xff", "x":1,"x":2}\n'
        packet = b"".join(encode_packet(TOKEN, U64_MAX, 1,
                                        {"kind": "submit", "bytes": len(proposal)}, (proposal,)))
        reader = asyncio.StreamReader()
        async def feed():
            for byte in packet:
                reader.feed_data(bytes((byte,)))
                await asyncio.sleep(0)
        feeder = asyncio.create_task(feed())
        decoded, parts = await read_packet(reader, TOKEN, U64_MAX, "to_b")
        await feeder
        self.assertEqual(parts, (proposal,))
        self.assertEqual(decoded["operation"]["kind"], "submit")
        with self.assertRaises(ProtocolError):
            next_sequence(U64_MAX)
        self.assertEqual(next_sequence(0), 1)

    async def test_strict_metadata_rejects_before_reading_attachment(self):
        original = frame({"kind": "request", "observation_bytes": 10,
                          "response_example_bytes": 10, "remaining_request_budget_ns": None},
                         request_id=1)
        bad = []
        for field, value in (("wire_version", 2), ("wire_version", True),
                             ("endpoint_token", "cd" * 32), ("endpoint_token", "AB" * 32), ("endpoint_token", "ab" * 31),
                             ("sequence", 1), ("sequence", True), ("sequence", -1), ("sequence", 0.0),
                             ("sequence", U64_MAX + 1), ("extra", 1),
                             ("request_id", None), ("request_id", 0), ("request_id", False)):
            bad.append({**original, field: value})
        bad.append({key: value for key, value in original.items() if key != "request_id"})
        for field, value in (("observation_bytes", True), ("observation_bytes", -1),
                             ("observation_bytes", 1.0), ("observation_bytes", 1 << 32),
                             ("response_example_bytes", MAX_PACKET_BYTES), ("extra", 0),
                             ("remaining_request_budget_ns", 1),
                             ("remaining_request_budget_ns", "01"),
                             ("remaining_request_budget_ns", "+1"),
                             ("remaining_request_budget_ns", str(U64_MAX + 1))):
            bad.append({**original, "operation": {**original["operation"], field: value}})
        bad.append({**original, "operation": {key: value for key, value in original["operation"].items()
                                             if key != "remaining_request_budget_ns"}})
        for value in bad:
            reader = CountingReader(wire(value, (b"unread attachment",)))
            with self.subTest(value=value), self.assertRaises(ProtocolError):
                await read_packet(reader, TOKEN, 0, "to_c")
            self.assertEqual(reader.data, b"unread attachment")

    async def test_phase_direction_duplicates_and_unknown_nested_keys_before_body(self):
        value = frame({"kind": "query_result", "query_id": 1, "result_bytes": 10}, request_id=1)
        for direction in ("to_b", "bad"):
            reader = CountingReader(wire(value, (b"unread!!!!",)))
            with self.assertRaises(ProtocolError):
                await read_packet(reader, TOKEN, 0, direction)
            self.assertEqual(reader.data, b"unread!!!!")
        reader = CountingReader(wire(value, (b"unread!!!!",)))
        def reject(_):
            raise ProtocolError("wrong phase")
        with self.assertRaises(ProtocolError):
            await read_packet(reader, TOKEN, 0, "to_c", reject)
        self.assertEqual(reader.data, b"unread!!!!")
        header = json_wire.encode(value)
        for invalid in (header.replace(b'{', b'{"sequence":0,', 1),
                        header.replace(b'"kind":"query_result"', b'"kind":"query_result","kind":"query_result"'),
                        header + b" {}", b'"\xff"'):
            with self.assertRaises(ProtocolError):
                decode_header(invalid, TOKEN, 0, "to_c")
        ready = frame({"kind": "ready", "api": {"version": API_VERSION, "operations": [], "extra": 0}})
        with self.assertRaises(ProtocolError):
            decode_header(json_wire.encode(ready), TOKEN, 0, "to_c")

    async def test_header_controls_aggregate_and_truncation(self):
        for size in (0, MAX_HEADER_BYTES + 1, 1 << 31):
            reader = CountingReader(struct.pack(">I", size) + b"unread")
            with self.assertRaises(ProtocolError):
                await read_packet(reader, TOKEN, 0, "to_c")
            self.assertEqual(reader.read_sizes, [4])
        control = json_wire.encode(frame({"kind": "cancel", "reason": "deadline"}, request_id=1))
        with self.assertRaises(ProtocolError):
            decode_header(control + b" " * MAX_CONTROL_BYTES, TOKEN, 0, "to_c")
        value = frame({"kind": "request", "observation_bytes": MAX_PACKET_BYTES // 2,
                       "response_example_bytes": MAX_PACKET_BYTES // 2,
                       "remaining_request_budget_ns": "0"}, request_id=1)
        reader = CountingReader(wire(value) + b"unread")
        with self.assertRaises(ProtocolError):
            await read_packet(reader, TOKEN, 0, "to_c")
        self.assertEqual(reader.data, b"unread")
        for data in (b"", b"\x00", struct.pack(">I", 10) + b"short",
                     wire(frame({"kind": "query_result", "query_id": 1, "result_bytes": 2}, request_id=1), (b"{",))):
            with self.subTest(data=data), self.assertRaises(EndpointError):
                await read_packet(CountingReader(data), TOKEN, 0, "to_c")

    def test_exact_types_capabilities_enums_and_immutable_attachments(self):
        for operation in ({"kind": "query", "query_id": 0, "name": "history", "args_bytes": 0},
                          {"kind": "query", "query_id": 1, "name": "1bad", "args_bytes": 0},
                          {"kind": "query", "query_id": 1, "name": "é", "args_bytes": 0},
                          {"kind": "query_result", "query_id": True, "result_bytes": 0},
                          {"kind": "cancel", "reason": True},
                          {"kind": "complete", "outcome": "success"},
                          {"kind": "rejected", "code": "semantic_error"},
                          {"kind": "shutdown", "reason": "deadline"},
                          {"kind": "closed", "extra": 1}):
            with self.subTest(operation=operation), self.assertRaises(ProtocolError):
                attachment_lengths(operation)
        for version in ("03.0.0", "3.0", "3.0.0.0", True):
            with self.assertRaises(ProtocolError):
                attachment_lengths({"kind": "hello", "capabilities": {
                    "version": version, "supported_operations": [], "required_operations": []}})
        for supported, required in ((["history", "history"], []), ([], ["history"]),
                                    ([True], []), (["a" * 65], [])):
            with self.assertRaises(ProtocolError):
                attachment_lengths({"kind": "hello", "capabilities": {
                    "version": API_VERSION, "supported_operations": supported, "required_operations": required}})
        for attachments in ([b"x"], (bytearray(b"x"),), (b"xx",)):
            with self.assertRaises(ProtocolError):
                encode_packet(TOKEN, 0, 1, {"kind": "submit", "bytes": 1}, attachments)


class MemoryWriter:
    def __init__(self, incoming, outgoing):
        self.incoming, self.outgoing = incoming, outgoing
        self.transport = self
        self.aborted = False
        self.block = False
        self.entered_drain = asyncio.Event()
        self.drain_release = asyncio.Event()

    def write(self, data):
        if self.aborted:
            raise ConnectionError("closed")
        self.outgoing.feed_data(data)

    async def drain(self):
        if self.block:
            self.entered_drain.set()
            await self.drain_release.wait()
        if self.aborted:
            raise ConnectionError("closed")

    def abort(self):
        self.aborted = True
        self.incoming.feed_eof()
        self.outgoing.feed_eof()
        self.drain_release.set()

    def close(self):
        self.abort()

    async def wait_closed(self):
        pass


class ClientTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        self.incoming, self.outgoing = asyncio.StreamReader(), asyncio.StreamReader()
        self.writer = MemoryWriter(self.incoming, self.outgoing)
        self.client = ApiClient(self.incoming, self.writer, TOKEN)
        self.b_sequence = self.c_sequence = 0
        self.addAsyncCleanup(self.client.close)

    async def send(self, operation, request_id=None, parts=()):
        self.incoming.feed_data(b"".join(encode_packet(TOKEN, self.b_sequence, request_id, operation, parts)))
        self.b_sequence += 1
        await asyncio.sleep(0)

    async def receive(self):
        result = await asyncio.wait_for(read_packet(self.outgoing, TOKEN, self.c_sequence, "to_b"), 1)
        self.c_sequence += 1
        return result

    async def start(self, operations=QUERY_NAMES):
        task = asyncio.create_task(self.client.start())
        packet, _ = await self.receive()
        self.assertEqual(packet["operation"]["kind"], "hello")
        await self.send({"kind": "ready", "api": {"version": API_VERSION, "operations": list(operations)}})
        await task

    async def request(self, request_id=1, budget=None):
        parts = (b'{"immutable":"observation"}', b'{"exact":"example"}')
        await self.send({"kind": "request", "observation_bytes": len(parts[0]),
                         "response_example_bytes": len(parts[1]), "remaining_request_budget_ns": budget},
                        request_id, parts)
        event = await self.client.next_event()
        self.assertIsInstance(event, RequestEvent)
        return event

    async def complete(self, access, outcome="no_response"):
        task = asyncio.create_task(self.client.complete(access, outcome))
        packet, _ = await self.receive()
        self.assertEqual(packet["operation"], {"kind": "complete", "outcome": outcome})
        self.assertFalse(task.done())
        await self.send({"kind": "request_closed"}, access.view.request_id)
        await task

    async def test_out_of_order_query_results_opaque_receipt_and_two_requests(self):
        await self.start()
        first = await self.request(budget=str(U64_MAX))
        access = first.access
        self.assertEqual(access.view.remaining_budget_ns, U64_MAX)
        queries = [asyncio.create_task(access.query("history", b' {"key":1} ')),
                   asyncio.create_task(access.query("ledger", b"{}"))]
        one, parts = await self.receive()
        two, _ = await self.receive()
        self.assertEqual(parts, (b' {"key":1} ',))
        self.assertEqual([one["operation"]["query_id"], two["operation"]["query_id"]], [1, 2])
        for query_id in (2, 1):
            result = ('{"id":%d}' % query_id).encode()
            await self.send({"kind": "query_result", "query_id": query_id, "result_bytes": len(result)}, 1, (result,))
        self.assertEqual(await asyncio.gather(*queries), [b'{"id":1}', b'{"id":2}'])
        proposal = b' {"not":"\xff", "x":1,"x":2} '
        submit = asyncio.create_task(access.submit(proposal))
        packet, parts = await self.receive()
        self.assertEqual(parts, (proposal,))
        self.assertEqual(packet["operation"]["kind"], "submit")
        self.assertFalse(submit.done())
        with self.assertRaises(ProtocolError):
            await self.client.complete(access, "response")
        await self.send({"kind": "submitted"}, 1)
        await submit
        with self.assertRaises(ProtocolError):
            await access.submit(b"replacement")
        with self.assertRaises(ProtocolError):
            await self.client.complete(access, "no_response")
        await self.complete(access, "response")
        with self.assertRaises(RequestRevoked):
            await access.query("history", b"{}")
        second = await self.request(2, "0")
        self.assertEqual(second.access.view.remaining_budget_ns, 0)
        query = asyncio.create_task(second.access.query("ledger", b"{}"))
        packet, _ = await self.receive()
        self.assertEqual(packet["operation"]["query_id"], 1)
        await self.send({"kind": "query_result", "query_id": 1, "result_bytes": 2}, 2, (b"{}",))
        await query
        await self.complete(second.access, "source_exhausted")
        await self.send({"kind": "shutdown", "reason": "complete"})
        self.assertEqual(await self.client.next_event(), ShutdownEvent("complete"))
        close = asyncio.create_task(self.client.closed())
        packet, _ = await self.receive()
        self.assertEqual(packet["operation"]["kind"], "closed")
        await close
        self.assertTrue(self.writer.aborted)
        self.assertTrue(self.client._reader_task.done())

    async def test_cancel_revokes_pending_query_and_submit_preserving_authoritative_cause(self):
        for reason in ("deadline", "cancelled", "failure"):
            # A separate endpoint is needed for each cause; subtests use fresh setup.
            if reason != "deadline":
                await self.client.close()
                await self.asyncSetUp()
            await self.start()
            event = await self.request(budget="0")
            query = asyncio.create_task(event.access.query("history", b"{}"))
            await self.receive()
            submit = asyncio.create_task(event.access.submit(b"malformed"))
            await self.receive()
            await self.send({"kind": "cancel", "reason": reason}, 1)
            self.assertEqual(await event.stop.wait(), reason)
            for task in (query, submit):
                with self.assertRaises(RequestRevoked) as caught:
                    await task
                self.assertEqual(caught.exception.reason, reason)
            with self.assertRaises(RequestRevoked):
                await event.access.query("ledger", b"{}")
            with self.assertRaises(ProtocolError):
                await self.client.complete(event.access, "response")
            await self.complete(event.access, "failure")
            next_request = await self.request(2)
            await self.complete(next_request.access)

    async def test_fail_can_abort_pending_work_and_late_replies_do_not_restore_authority(self):
        await self.start()
        event = await self.request()
        query = asyncio.create_task(event.access.query("ledger", b"{}"))
        await self.receive()
        submit = asyncio.create_task(event.access.submit(b""))
        await self.receive()
        complete = asyncio.create_task(self.client.complete(event.access, "failure"))
        await self.receive()
        for task in (query, submit):
            with self.assertRaises(RequestRevoked):
                await task
        await self.send({"kind": "query_result", "query_id": 1, "result_bytes": 2}, 1, (b"{}",))
        await self.send({"kind": "submitted"}, 1)
        await self.send({"kind": "request_closed"}, 1)
        await complete
        with self.assertRaises(RequestRevoked):
            await event.access.submit(b"{}")

    async def test_caller_cancellation_keeps_query_correlation_until_reply(self):
        await self.start()
        event = await self.request()
        query = asyncio.create_task(event.access.query("history", b"{}"))
        await self.receive()
        query.cancel()
        with self.assertRaises(asyncio.CancelledError):
            await query
        with self.assertRaises(ProtocolError):
            await self.client.complete(event.access, "no_response")
        await self.send({"kind": "query_result", "query_id": 1, "result_bytes": 2}, 1, (b"{}",))
        await self.complete(event.access)

    async def test_transport_rejection_is_never_a_semantic_receipt(self):
        await self.start()
        event = await self.request()
        submit = asyncio.create_task(event.access.submit(b"x"))
        await self.receive()
        await self.send({"kind": "rejected", "code": "too_large"}, 1)
        with self.assertRaises(SubmissionRejected):
            await submit
        with self.assertRaises(SubmissionRejected):
            await self.client.next_event()
        self.assertTrue(self.writer.aborted)

    async def test_unknown_reply_duplicate_receipt_and_stale_scope_fail(self):
        variants = [({"kind": "query_result", "query_id": 1, "result_bytes": 2}, 1, (b"{}",)),
                    ({"kind": "submitted"}, 1, ()),
                    ({"kind": "cancel", "reason": "failure"}, 2, ()),
                    ({"kind": "request_closed"}, 1, ())]
        for index, (operation, request_id, parts) in enumerate(variants):
            if index:
                await self.client.close()
                await self.asyncSetUp()
            await self.start()
            await self.request()
            await self.send(operation, request_id, parts)
            with self.assertRaises(ProtocolError):
                await self.client.next_event()
            self.assertTrue(self.writer.aborted)

    async def test_ready_rejects_extra_capabilities_wrong_version_and_bad_order(self):
        for index, api in enumerate(({"version": "4.0.0", "operations": []},
                                     {"version": "3.1.1", "operations": []},
                                     {"version": API_VERSION, "operations": ["private_secret"]})):
            if index:
                await self.client.close()
                await self.asyncSetUp()
            task = asyncio.create_task(self.client.start())
            await self.receive()
            await self.send({"kind": "ready", "api": api})
            with self.assertRaises(ProtocolError):
                await task
        await self.client.close()
        await self.asyncSetUp()
        task = asyncio.create_task(self.client.start())
        await self.receive()
        await self.send({"kind": "shutdown", "reason": "failure"})
        with self.assertRaises(ProtocolError):
            await task

    async def test_negotiation_narrows_and_rejects_unadvertised_query(self):
        await self.start(("history",))
        event = await self.request()
        self.assertEqual(event.access.query_names, ("history",))
        with self.assertRaises(QueryUnavailable):
            await event.access.query("ledger", b"{}")
        await self.complete(event.access)

    async def test_all_six_queries_forward_opaque_arguments_and_exact_results(self):
        await self.start()
        event = await self.request()
        for index, name in enumerate(QUERY_NAMES, 1):
            arguments = (" malformed λ: %s " % name).encode()
            pending = asyncio.create_task(event.access.query(name, arguments))
            packet, parts = await self.receive()
            self.assertEqual(packet["operation"]["name"], name)
            self.assertEqual(packet["operation"]["query_id"], index)
            self.assertEqual(parts, (arguments,))
            result = b' {"status":"error","message":"backend owns argument validation"} '
            await self.send({"kind": "query_result", "query_id": index, "result_bytes": len(result)}, 1, (result,))
            self.assertEqual(await pending, result)
        await self.complete(event.access)

    async def test_missing_required_negotiated_operation_fails_before_request(self):
        self.client._capabilities["required_operations"] = ["history"]
        task = asyncio.create_task(self.client.start())
        await self.receive()
        await self.send({"kind": "ready", "api": {"version": API_VERSION, "operations": []}})
        with self.assertRaises(ProtocolError):
            await task
        self.assertTrue(self.writer.aborted)

    async def test_duplicate_query_result_is_rejected_after_its_first_delivery(self):
        await self.start()
        event = await self.request()
        query = asyncio.create_task(event.access.query("ledger", b"{}"))
        await self.receive()
        reply = {"kind": "query_result", "query_id": 1, "result_bytes": 2}
        await self.send(reply, 1, (b"{}",))
        await query
        await self.send(reply, 1, (b"{}",))
        with self.assertRaises(ProtocolError):
            await self.client.next_event()


    async def test_sequence_request_and_query_exhaustion_never_wrap(self):
        await self.start()
        event = await self.request()
        event.access._next_query = U64_MAX
        query = asyncio.create_task(event.access.query("history", b"{}"))
        packet, _ = await self.receive()
        self.assertEqual(packet["operation"]["query_id"], U64_MAX)
        await self.send({"kind": "query_result", "query_id": U64_MAX, "result_bytes": 2}, 1, (b"{}",))
        await query
        with self.assertRaises(ProtocolError):
            await event.access.query("history", b"{}")
        await self.complete(event.access)
        await self.send({"kind": "request", "observation_bytes": 2, "response_example_bytes": 2,
                         "remaining_request_budget_ns": None}, 3, (b"{}", b"{}"))
        with self.assertRaises(ProtocolError):
            await self.client.next_event()

    async def test_shutdown_and_eof_wake_pending_requests_without_inventing_receipts(self):
        await self.start()
        event = await self.request()
        submit = asyncio.create_task(event.access.submit(b"{}"))
        await self.receive()
        await self.send({"kind": "shutdown", "reason": "cancelled"})
        self.assertEqual(await event.stop.wait(), "cancelled")
        with self.assertRaises(RequestRevoked):
            await submit
        self.assertEqual(await self.client.next_event(), ShutdownEvent("cancelled"))
        await self.client.close()
        await self.asyncSetUp()
        await self.start()
        event = await self.request()
        query = asyncio.create_task(event.access.query("history", b"{}"))
        await self.receive()
        self.incoming.feed_eof()
        with self.assertRaises(EndpointError):
            await query
        with self.assertRaises(EndpointError):
            await self.client.next_event()
        self.assertTrue(event.stop.requested())

    async def test_cancel_unblocks_a_backpressured_write_and_preserves_reason(self):
        await self.start()
        event = await self.request(budget="0")
        self.writer.block = True
        query = asyncio.create_task(event.access.query("history", b"{}"))
        await self.writer.entered_drain.wait()
        await self.send({"kind": "cancel", "reason": "cancelled"}, 1)
        with self.assertRaises(RequestRevoked) as caught:
            await asyncio.wait_for(query, 1)
        self.assertEqual(caught.exception.reason, "cancelled")
        self.assertEqual(await event.stop.wait(), "cancelled")
        self.assertTrue(self.writer.aborted)
        await self.client.close()
        self.assertTrue(self.client._reader_task.done())

    async def test_cancelled_writer_aborts_incomplete_stream_and_joins_reader(self):
        await self.start()
        event = await self.request()
        self.writer.block = True
        submit = asyncio.create_task(event.access.submit(b"{}"))
        await self.writer.entered_drain.wait()
        submit.cancel()
        with self.assertRaises(asyncio.CancelledError):
            await submit
        self.assertTrue(self.writer.aborted)
        with self.assertRaises(EndpointError):
            await self.client.next_event()
        await self.client.close()
        self.assertTrue(self.client._reader_task.done())

    async def test_local_close_wakes_event_waiter_and_joins_despite_caller_cancellation(self):
        await self.start()
        waiter = asyncio.create_task(self.client.next_event())
        await asyncio.sleep(0)
        gate = asyncio.Event()
        async def slow_close():
            await gate.wait()
        self.writer.wait_closed = slow_close
        closing = asyncio.create_task(self.client.close())
        await asyncio.sleep(0)
        closing.cancel()
        await asyncio.sleep(0)
        self.assertFalse(closing.done())
        gate.set()
        with self.assertRaises(asyncio.CancelledError):
            await closing
        with self.assertRaises(EndpointError):
            await waiter
        self.assertTrue(self.client._reader_task.done())
        self.assertTrue(self.client._close_task.done())

    async def test_cancellation_racing_completion_keeps_the_real_stop_cause(self):
        await self.start()
        event = await self.request()
        completion = asyncio.create_task(self.client.complete(event.access, "no_response"))
        await self.receive()
        await self.send({"kind": "cancel", "reason": "deadline"}, 1)
        self.assertEqual(await event.stop.wait(), "deadline")
        with self.assertRaises(EndpointError):
            await completion
        self.assertTrue(self.writer.aborted)


    async def test_duplicate_receipt_and_invalid_json_reply_fail_closed(self):
        await self.start()
        event = await self.request()
        submit = asyncio.create_task(event.access.submit(b"{}"))
        await self.receive()
        await self.send({"kind": "submitted"}, 1)
        await submit
        await self.send({"kind": "submitted"}, 1)
        with self.assertRaises(ProtocolError):
            await self.client.next_event()
        await self.client.close()
        await self.asyncSetUp()
        await self.start()
        event = await self.request()
        query = asyncio.create_task(event.access.query("history", b"{}"))
        await self.receive()
        await self.send({"kind": "query_result", "query_id": 1, "result_bytes": 4}, 1, (b"nope",))
        with self.assertRaises(ProtocolError):
            await query


class SocketClientTests(unittest.IsolatedAsyncioTestCase):
    async def test_real_unix_bootstrap_handshake_request_and_joined_close(self):
        with tempfile.TemporaryDirectory() as directory:
            path = str(Path(directory) / "api.sock")
            completed = asyncio.get_running_loop().create_future()
            async def host(reader, writer):
                try:
                    hello, _ = await read_packet(reader, TOKEN, 0, "to_b")
                    self.assertEqual(hello["operation"]["capabilities"]["version"], API_VERSION)
                    for packet in (encode_packet(TOKEN, 0, None, {"kind": "ready", "api": {"version": API_VERSION, "operations": []}}),
                                   encode_packet(TOKEN, 1, 1, {"kind": "request", "observation_bytes": 2,
                                                 "response_example_bytes": 2, "remaining_request_budget_ns": None}, (b"{}", b"{}"))):
                        for part in packet:
                            writer.write(part)
                        await writer.drain()
                    complete, _ = await read_packet(reader, TOKEN, 1, "to_b")
                    self.assertEqual(complete["operation"]["outcome"], "no_response")
                    for sequence, request_id, operation in ((2, 1, {"kind": "request_closed"}),
                                                            (3, None, {"kind": "shutdown", "reason": "complete"})):
                        for part in encode_packet(TOKEN, sequence, request_id, operation):
                            writer.write(part)
                    await writer.drain()
                    closed, _ = await read_packet(reader, TOKEN, 2, "to_b")
                    self.assertEqual(closed["operation"]["kind"], "closed")
                    self.assertEqual(await reader.read(), b"")
                    completed.set_result(None)
                except BaseException as error:
                    completed.set_exception(error)
                finally:
                    writer.close()
                    await writer.wait_closed()
            server = await asyncio.start_unix_server(host, path)
            async with server:
                client = await ApiClient.from_environment({"WHIEL_PROPOSER_SOCKET": path,
                                                           "WHIEL_PROPOSER_TOKEN": TOKEN})
                try:
                    event = await client.next_event()
                    await client.complete(event.access, "no_response")
                    self.assertEqual(await client.next_event(), ShutdownEvent("complete"))
                    await client.closed()
                    await asyncio.wait_for(completed, 2)
                finally:
                    await client.close()
        for environment in ({}, {"WHIEL_PROPOSER_SOCKET": "relative", "WHIEL_PROPOSER_TOKEN": TOKEN},
                             {"WHIEL_PROPOSER_SOCKET": "/absolute", "WHIEL_PROPOSER_TOKEN": "BAD"}):
            with self.assertRaises(ProtocolError):
                await ApiClient.from_environment(environment)


if __name__ == "__main__":
    unittest.main()
