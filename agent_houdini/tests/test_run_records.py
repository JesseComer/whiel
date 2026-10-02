# Author: Fangzhu Shen
"""Retained consultation bytes, diagnosable failures and the offline reader.

The first real run of the installed CLI reached the model seven times and left
counts behind: two consultations failed with a bare `mcp_failure` code that did
not say which side closed, what the exception was, which MCP call was in flight
or what the CLI had last reported. These tests pin the records and the reasons
that replace those counts.
"""

import os
import asyncio
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import AsyncMock, patch

from agent_houdini import mcp_stdio as relay
from agent_houdini import show_run
from agent_houdini.agent_log import WITHHELD
from agent_houdini.agent_runtime import NativeAgentRuntime
from agent_houdini.agent_transport import McpTransport, MeteredRequestAccess
from agent_houdini.providers import claude
from agent_houdini.provider_runtime import CliEventCapture
from agent_houdini.run_records import (
    DEBUG_FILE, MCP_FILE, PROMPT_FILE, STDERR_FILE, STDOUT_FILE, SUBMISSIONS_FILE, TRUNCATED,
    ConsultationRecord, RunRecords, null_records,
)
from agent_houdini.runtime_types import NativeOptions
from agent_houdini.json_wire import encode
from agent_houdini.tests.test_agent_transport import Access, Budget, Events, Stop
from agent_houdini.tests.test_frontend import Host, NATIVE_FIXTURE
from agent_houdini.tests.test_native_providers import MODEL


def call(identifier, name, arguments):
    return json.dumps({"jsonrpc": "2.0", "id": identifier, "method": "tools/call",
                       "params": {"name": name, "arguments": arguments}}).encode() + b"\n"


class RecordTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="c-records-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def test_identify_renames_the_temporary_input_directory_once(self):
        parent = self.root / "logs"
        parent.mkdir()
        first = parent / "input-abc123"
        first.mkdir()
        records = RunRecords(first, "all")
        self.assertEqual(records.identify("Example0001"), "Example0001")
        self.assertEqual(records.directory, parent / "Example0001")
        self.assertFalse(first.exists())
        # Retained consultations land under the new name.
        record = records.consultation(1)
        self.assertEqual(record.directory, parent / "Example0001" / "request-1")
        record.close()
        # A later endpoint for the same input takes the next free name.
        second = parent / "input-def456"
        second.mkdir()
        self.assertEqual(RunRecords(second, "events").identify("Example0001"), "Example0001-2")
        self.assertTrue((parent / "Example0001-2").is_dir())
        # Unusable ids and directories that were never temporary are left alone.
        third = parent / "input-ghi789"
        third.mkdir()
        untouched = RunRecords(third, "all")
        for bad in (None, "", "../escape", "Example 1", "x" * 65, 7):
            self.assertIsNone(untouched.identify(bad))
        self.assertEqual(untouched.directory, third)
        self.assertIsNone(RunRecords(parent / "Example0001", "all").identify("Example0002"))
        self.assertTrue((parent / "Example0001").is_dir())
        self.assertIsNone(null_records().identify("Example0001"))

    def test_retention_off_keeps_metadata_and_writes_nothing(self):
        records = null_records()
        record = records.consultation(3)
        self.assertIsNone(record.directory)
        record.prompt(b"a prompt")
        record.stdout(b'{"type":"system"}\n')
        record.mcp_request(call(1, "ledger", {}))
        self.assertEqual(record.exchange_fields()["last_mcp_method"], "tools/call")
        self.assertEqual(record.exchange_fields()["last_mcp_tool"], "ledger")
        self.assertTrue(record.exchange_fields()["mcp_awaiting_reply"])
        self.assertEqual(record.close(), {})
        self.assertEqual(sorted(self.root.iterdir()), [])

    def test_retention_all_keeps_prompt_stream_traffic_and_submissions(self):
        records = RunRecords(self.root, "all")
        record = records.consultation(4)
        record.prompt(b"rendered prompt bytes\nsecond line\n")
        record.stdout(b'{"type":"system","subtype":"init"}\n{"type":"assist')
        record.stdout(b'ant"}\n')
        record.stderr(b"a CLI complaint\n")
        record.mcp_request(call(1, "ledger", {"page": 1}))
        record.mcp_reply(b'{"jsonrpc":"2.0","id":1,"result":{"isError":false}}\n')
        record.mcp_request(call(2, "submit", {"payload": '{"clauses":[]}'}))
        record.mcp_reply(b'{"jsonrpc":"2.0","id":2,"result":{"isError":false}}\n')
        record.mcp_request(call(3, "submit", {"payload": "rejected text"}))
        record.mcp_reply(b'{"jsonrpc":"2.0","id":3,"error":{"code":-32602,"message":"refused"}}\n')
        summary = record.close()

        self.assertEqual(summary["directory"], "request-4")
        held = self.root / "request-4"
        self.assertEqual((held / PROMPT_FILE).read_text(), "rendered prompt bytes\nsecond line\n")
        self.assertEqual((held / STDOUT_FILE).read_text(),
                         '{"type":"system","subtype":"init"}\n{"type":"assistant"}\n')
        self.assertEqual((held / STDERR_FILE).read_text(), "a CLI complaint\n")
        traffic = [json.loads(line) for line in (held / MCP_FILE).read_text().splitlines()]
        self.assertEqual([(entry["direction"], entry["method"], entry["tool"]) for entry in traffic],
                         [("request", "tools/call", "ledger"), ("reply", "tools/call", "ledger"),
                          ("request", "tools/call", "submit"), ("reply", "tools/call", "submit"),
                          ("request", "tools/call", "submit"), ("reply", "tools/call", "submit")])
        self.assertTrue(all(entry["bytes"] > 0 for entry in traffic))
        self.assertTrue(all(entry["time"] > 0 for entry in traffic))
        self.assertIn('"page": 1', traffic[0]["text"])
        submissions = [json.loads(line) for line in (held / SUBMISSIONS_FILE).read_text().splitlines()]
        # A payload the coordinator refused locally never reached B and spent
        # no round, so it is not counted as one.
        self.assertEqual([(entry["payload"], entry["verdict"], entry["forwarded"])
                          for entry in submissions],
                         [('{"clauses":[]}', "receipt", True),
                          ("rejected text", "refused_locally", False)])
        self.assertEqual([entry["accepted"] for entry in submissions], [True, False])
        self.assertEqual(submissions[1]["detail"], "refused")
        self.assertEqual(sorted(summary["files"]),
                         sorted((MCP_FILE, PROMPT_FILE, STDERR_FILE, STDOUT_FILE, SUBMISSIONS_FILE)))
        self.assertFalse(any(entry["truncated"] for entry in summary["files"].values()))

    def test_credential_lines_are_withheld_and_a_cap_leaves_a_marker(self):
        record = RunRecords(self.root, "all").consultation(1)
        record.stdout(b'{"type":"system","authorization": "Bearer abc"}\n{"type":"user"}\n')
        record._file(STDOUT_FILE, 0).maximum = 24
        record.stdout(b"0123456789012345678901234567890123456789\n")
        record.close()
        text = (self.root / "request-1" / STDOUT_FILE).read_text()
        self.assertIn(WITHHELD, text)
        self.assertNotIn("Bearer abc", text)
        self.assertIn('{"type":"user"}', text)
        self.assertIn(TRUNCATED, text)

    def test_an_unparsed_line_is_recorded_without_a_method(self):
        record = RunRecords(self.root, "all").consultation(2)
        record.mcp_request(b"not json at all\n")
        record.mcp_reply(None)
        record.close()
        entries = [json.loads(line) for line in
                   (self.root / "request-2" / MCP_FILE).read_text().splitlines()]
        self.assertEqual([entry["method"] for entry in entries], [None, None])
        self.assertEqual(entries[1]["bytes"], 0)
        self.assertIn("not json at all", entries[0]["text"])


class CaptureTests(unittest.TestCase):
    def test_the_stream_is_teed_and_the_last_reported_event_is_kept(self):
        seen = []
        capture = CliEventCapture((), None, sink=seen.append)
        capture.feed(b'{"type":"system","subtype":"init"}\n')
        capture.feed(b'{"type":"assistant"}\n{"type":"result","subtype":"success"}\n')
        self.assertEqual(b"".join(seen),
                         b'{"type":"system","subtype":"init"}\n{"type":"assistant"}\n'
                         b'{"type":"result","subtype":"success"}\n')
        summary = capture.summary()
        self.assertEqual(summary["last_event"], "result")
        self.assertEqual(summary["last_event_subtype"], "success")
        self.assertEqual(summary["events"], {"system": 1, "assistant": 1, "result": 1})

    def test_a_failing_tee_never_fails_the_turn(self):
        def sink(_data):
            raise OSError("no space")
        capture = CliEventCapture((), None, sink=sink)
        capture.feed(b'{"type":"system"}\n')
        capture.feed(b'{"type":"user"}\n')
        self.assertIsNone(capture.sink)
        self.assertEqual(capture.summary()["events"], {"system": 1, "user": 1})


class RelayDiagnosticTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="c-relay-", dir=os.path.realpath("/tmp"))
        self.addCleanup(self.directory.cleanup)
        self.socket_path = str(Path(self.directory.name) / "mcp.sock")

    def test_a_relay_refusal_leaves_one_bounded_line_beside_its_socket(self):
        # The CLI keeps its MCP server's stderr to itself, so a relay that
        # refuses its own framing must leave the reason where C can read it.
        token = "f" * 64
        output = io.BytesIO()
        try:
            relay.run(io.BytesIO(b"line\n"), output, self.socket_path, "not a token")
        except relay.RelayError as error:
            relay.write_diagnostic(self.socket_path, relay.failure_text(error, token))
        text = Path(self.socket_path + relay.DIAGNOSTIC_SUFFIX).read_text()
        self.assertIn("RelayError: invalid C relay token", text)
        self.assertEqual(len(text.splitlines()), 1)

    def test_the_connection_token_never_reaches_the_diagnostic(self):
        token = "a" * 64
        text = relay.failure_text(OSError(f"connect {token} refused"), token)
        self.assertNotIn(token, text)
        self.assertIn("<token>", text)
        self.assertTrue(text.startswith("OSError: "))


class FailureReasonTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="c-reason-", dir=os.path.realpath("/tmp"))
        self.addCleanup(self.directory.cleanup)
        self.work = Path(self.directory.name)
        self.retained = self.work / "logs"
        self.retained.mkdir()
        self.stop, self.budget, self.events = Stop(), Budget(), Events()
        self.access = MeteredRequestAccess(Access(), self.budget)
        self.record = RunRecords(self.retained, "all").consultation(3)
        self.addCleanup(self.record.close)

    async def create(self, handler):
        bridge = await McpTransport.create(self.work, handler, self.stop, self.budget,
                                          self.events, record=self.record)
        self.addAsyncCleanup(bridge.close_and_join)
        return bridge

    async def peer(self, bridge):
        reader, writer = await asyncio.open_unix_connection(
            bridge.launch.environment[relay.SOCKET_ENV])
        writer.write(relay.encode_header(relay.HELLO, 0, 32)
                     + relay.token_bytes(bridge.launch.environment[relay.TOKEN_ENV]))
        await writer.drain()
        self.assertEqual(relay.decode_header(await reader.readexactly(relay.HEADER.size)),
                         (relay.READY, 0, 0))
        self.addAsyncCleanup(self.close_peer, writer)
        return reader, writer

    @staticmethod
    async def close_peer(writer):
        writer.close()
        try:
            await writer.wait_closed()
        except (OSError, ConnectionError):
            pass

    async def wait_failure(self, bridge):
        async def wait():
            while bridge.failure() is None:
                await asyncio.sleep(0.001)
            return bridge.failure()
        return await asyncio.wait_for(wait(), 2)

    def emitted(self, kind):
        return [fields for name, fields in self.events.items if name == kind]

    async def test_a_relay_that_dies_during_a_tool_call_names_the_side_and_the_call(self):
        started = asyncio.Event()
        release = asyncio.Event()

        async def handler(_line):
            started.set()
            await release.wait()
            return b'{"jsonrpc":"2.0","id":1,"result":{}}\n'

        bridge = await self.create(handler)
        reader, writer = await self.peer(bridge)
        line = call(1, "evaluate_clauses", {"clauses": ["p"]})
        writer.write(relay.encode_header(relay.BEGIN, 1, len(line)))
        await writer.drain()
        await reader.readexactly(relay.HEADER.size)
        writer.write(line)
        await writer.drain()
        await asyncio.wait_for(started.wait(), 2)
        # The provider CLI tore its MCP server down mid tool call.
        writer.transport.abort()
        release.set()
        self.assertEqual(await self.wait_failure(bridge), "mcp_failure")
        detail = bridge.failure_detail()
        self.assertEqual(detail["side"], "relay")
        self.assertEqual(detail["last_mcp_method"], "tools/call")
        self.assertEqual(detail["last_mcp_tool"], "evaluate_clauses")
        self.assertEqual(detail["mcp_exchanges"], 1)
        self.assertTrue(detail["connection_seen"])
        self.assertIn(detail["phase"], ("awaiting_relay_header", "sending_reply"))
        self.assertIn(detail["error_class"],
                      ("IncompleteReadError", "ConnectionResetError", "BrokenPipeError"))
        self.assertTrue(detail["reason"])
        self.assertEqual(self.emitted("mcp_failure")[0]["code"], "mcp_failure")
        self.assertEqual(self.emitted("mcp_failure")[0]["last_mcp_tool"], "evaluate_clauses")

    async def test_a_malformed_coordinator_reply_is_refused_with_its_own_reason(self):
        async def handler(_line):
            # Two lines in one reply: the framing rule the relay protocol keeps.
            return b'{"jsonrpc":"2.0","id":1,"result":{}}\ntrailing\n'

        bridge = await self.create(handler)
        reader, writer = await self.peer(bridge)
        line = call(1, "ledger", {})
        writer.write(relay.encode_header(relay.BEGIN, 1, len(line)))
        await writer.drain()
        await reader.readexactly(relay.HEADER.size)
        writer.write(line)
        await writer.drain()
        self.assertEqual(await self.wait_failure(bridge), "mcp_failure")
        detail = bridge.failure_detail()
        self.assertEqual(detail["side"], "coordinator")
        self.assertEqual(detail["error_class"], "RelayError")
        self.assertIn("invalid native MCP reply", detail["reason"])
        self.assertEqual(detail["last_mcp_tool"], "ledger")
        self.assertFalse(detail["mcp_awaiting_reply"])

    async def test_a_relay_diagnostic_left_behind_reaches_the_failure_record(self):
        bridge = await self.create(lambda line: None)
        reader, writer = await self.peer(bridge)
        relay.write_diagnostic(bridge.launch.environment[relay.SOCKET_ENV],
                               "RelayError: native MCP line exceeds bound")
        writer.transport.abort()
        self.assertEqual(await self.wait_failure(bridge), "mcp_failure")
        await bridge.close_and_join()
        self.assertEqual(self.emitted("relay_diagnostic")[0]["reason"],
                         "RelayError: native MCP line exceeds bound")
        self.assertIn("native MCP line exceeds bound", bridge.failure_detail()["relay_diagnostic"])

    async def test_retained_traffic_survives_the_failure_that_ended_the_turn(self):
        async def handler(_line):
            return b'{"jsonrpc":"2.0","id":1,"result":{"isError":false}}\n'

        bridge = await self.create(handler)
        reader, writer = await self.peer(bridge)
        line = call(1, "submit", {"payload": '{"clauses":["p"]}'})
        writer.write(relay.encode_header(relay.BEGIN, 1, len(line)))
        await writer.drain()
        await reader.readexactly(relay.HEADER.size)
        writer.write(line)
        await writer.drain()
        await asyncio.wait_for(reader.readexactly(relay.HEADER.size), 2)
        writer.transport.abort()
        self.assertEqual(await self.wait_failure(bridge), "mcp_failure")
        self.record.close()
        held = self.retained / "request-3"
        submissions = [json.loads(text) for text in
                       (held / SUBMISSIONS_FILE).read_text().splitlines()]
        self.assertEqual(submissions[0]["payload"], '{"clauses":["p"]}')
        self.assertEqual(submissions[0]["verdict"], "receipt")
        self.assertEqual(len((held / MCP_FILE).read_text().splitlines()), 2)


class ShowRunTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="c-show-")
        self.addCleanup(self.directory.cleanup)
        self.input = Path(self.directory.name) / "whiel-agent-x" / "input-y"
        self.input.mkdir(parents=True)

    def write(self, events):
        (self.input / "events.jsonl").write_text(
            "".join(json.dumps(event) + "\n" for event in events))

    def render(self, path):
        lines = []
        for found in show_run.find_inputs(path):
            show_run.describe_input(lines.append, found)
        return "\n".join(lines)

    def test_a_retained_consultation_reads_without_opening_json(self):
        record = ConsultationRecord(1, self.input / "request-1")
        (self.input / "request-1").mkdir()
        record.prompt(b"prompt text\n")
        record.mcp_request(call(1, "history", {}))
        record.mcp_reply(b'{"jsonrpc":"2.0","id":1,"result":{"isError":false}}\n')
        record.mcp_request(call(2, "submit", {"payload": '{"clauses":[]}'}))
        record.mcp_reply(b'{"jsonrpc":"2.0","id":2,"result":{"isError":false}}\n')
        summary = record.close()
        self.write([
            {"kind": "endpoint_configuration",
             "fields": {"selection": {"provider": "claude", "model": "m"},
                        "isolation": "local", "retention": "all"}},
            {"kind": "request_started",
             "fields": {"request_id": 1, "prompt_bytes": 12, "prompt_sha256": "ab" * 32,
                        "tool_names": ["history", "submit"]}},
            {"kind": "native_capture",
             "fields": {"counts": {"stdout_bytes": 2048, "events": {"system": 4},
                                   "last_event": "system", "provider_errors": []}}},
            {"kind": "request_outcome",
             "fields": {"request_id": 1, "outcome": "response", "diagnostic_code": None,
                        **summary}},
        ])
        text = self.render(Path(self.directory.name))
        self.assertIn("request 1: response", text)
        self.assertIn("retention=all", text)
        self.assertIn("prompt: 12 B", text)
        self.assertIn("tool history: sent", text)
        self.assertIn("submission 1: 14 B -> receipt", text)
        self.assertIn("systemx4", text)
        self.assertIn("last=system", text)

    def test_a_failure_reason_is_printed_in_full(self):
        self.write([
            {"kind": "request_started", "fields": {"request_id": 3, "prompt_bytes": 10}},
            {"kind": "mcp_failure",
             "fields": {"code": "mcp_failure", "side": "relay", "phase": "handling_request",
                        "error_class": "IncompleteReadError", "reason": "IncompleteReadError: 0/9",
                        "last_mcp_method": "tools/call", "last_mcp_tool": "countermodel"}},
            {"kind": "native_bridge_failure",
             "fields": {"code": "mcp_failure", "cli_last_event": "assistant",
                        "cli_stdout_bytes": 45563}},
            {"kind": "request_outcome",
             "fields": {"request_id": 3, "outcome": "failure", "diagnostic_code": "mcp_failure"}},
        ])
        text = self.render(self.input / "events.jsonl")
        self.assertIn("request 3: failure [mcp_failure]", text)
        self.assertIn("side=relay", text)
        self.assertIn("last_mcp_tool=countermodel", text)
        self.assertIn("cli_last_event=assistant", text)
        self.assertIn("retained: nothing", text)

    def test_a_directory_without_any_run_is_reported_not_guessed(self):
        self.assertEqual(show_run.find_inputs(Path(self.directory.name) / "missing"), [])
        self.assertEqual(show_run.main([str(Path(self.directory.name) / "missing")]), 1)


class EndToEndRetentionTests(unittest.IsolatedAsyncioTestCase):
    """One whole consultation through the real endpoint, with retention on."""

    async def asyncSetUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="c-retain-", dir=os.path.realpath("/tmp"))
        self.root = Path(self.temporary.name)
        self.addCleanup(self.temporary.cleanup)

    async def host(self, factory, **options):
        host = Host(self.root)
        self.addAsyncCleanup(host.close)
        return await host.start(factory, **options)

    def native_factory(self, actions):
        script = self.root / "native.py"
        script.write_text("#!" + sys.executable + "\n" + NATIVE_FIXTURE.read_text())
        script.chmod(0o700)
        (self.root / "native.json").write_text(json.dumps({
            "synthetic_fixture": True, "events": str(self.root / "native-events"),
            "actions": actions}))
        selected = claude.ClaudeIdentity(str(script), MODEL, "medium", self.root / ".claude")
        return (lambda *arguments: NativeAgentRuntime(*arguments)), selected

    async def test_first_push_names_the_input_directory_before_retention(self):
        from agent_houdini.tests.test_frontend import Runner

        logs = self.root / "logs"
        logs.mkdir()
        temporary = logs / "input-a1b2c3"
        temporary.mkdir()
        runner = Runner()
        observation = {"schema_version": 15, "operation": "proposer_observation", "correction": None,
                       "feedback": {"iteration": 1, "remaining_search_budget_ns": "30000000000",
                                    "presentation": {"task": {"canonical_id": "Example0042"}}}}
        host = await self.host(runner.factory, records=RunRecords(temporary, "all"))
        await host.request(observation=observation)
        await host.complete("no_response")
        await host.request(2, observation=observation)
        await host.complete("no_response", 2)
        self.assertEqual(await host.shutdown(), 0)
        named = logs / "Example0042"
        self.assertFalse(temporary.exists())
        self.assertTrue((named / "request-1" / PROMPT_FILE).is_file())
        self.assertTrue((named / "request-2" / PROMPT_FILE).is_file())
        self.assertIn(b"Example0042", (named / "request-1" / PROMPT_FILE).read_bytes())
        identified = [fields for kind, fields in host.events.items if kind == "input_identified"]
        self.assertEqual(identified, [{"request_id": 1, "canonical_id": "Example0042",
                                       "directory": "Example0042"}])
        outcomes = [fields["directory"] for kind, fields in host.events.items if kind == "request_outcome"]
        self.assertEqual(outcomes, ["request-1", "request-2"])

    async def test_a_push_without_a_task_leaves_the_temporary_name(self):
        from agent_houdini.tests.test_frontend import Runner

        temporary = self.root / "input-keep"
        temporary.mkdir()
        host = await self.host(Runner().factory, records=RunRecords(temporary, "all"))
        await host.request()
        await host.complete("no_response")
        self.assertEqual(await host.shutdown(), 0)
        self.assertTrue((temporary / "request-1" / PROMPT_FILE).is_file())
        self.assertEqual([kind for kind, _ in host.events.items if kind == "input_identified"], [])

    async def test_a_real_turn_leaves_prompt_stream_traffic_and_submission_on_disk(self):
        payload = '{"kind":"candidate_clauses","binding":{"unchanged":true}}'
        actions = [{"method": "tools/call",
                    "params": {"name": "ledger", "arguments": {"cursor": None}}},
                   {"method": "tools/call",
                    "params": {"name": "submit", "arguments": {"payload": payload}}}]
        logs = self.root / "logs"
        logs.mkdir()
        factory, selected = self.native_factory(actions)
        with patch("agent_houdini.agent_runtime.verify_provider", AsyncMock(return_value=selected)):
            host = await self.host(factory, operations=("ledger",),
                                   records=RunRecords(logs, "all"),
                                   options=NativeOptions(
                                       encode({"provider": "claude", "model": MODEL}),
                                       "local", self.root))
            await host.request(budget="0")
            packet, _parts = await host.receive()
            self.assertEqual(packet["operation"]["name"], "ledger")
            reply = b'{"operation":"ledger","data":{"clauses":[]}}'
            await host.send(1, {"kind": "query_result", "query_id": 1,
                                "result_bytes": len(reply)}, (reply,))
            packet, parts = await host.receive()
            self.assertEqual(packet["operation"]["kind"], "submit")
            self.assertEqual(parts, (payload.encode(),))
            await host.send(1, {"kind": "submitted"})
            await host.complete("response")
            self.assertEqual(await host.shutdown(), 0)
        held = logs / "request-1"
        self.assertTrue(held.is_dir())
        self.assertGreater(len((held / PROMPT_FILE).read_bytes()), 100)
        self.assertIn(b"candidate_clauses", (held / PROMPT_FILE).read_bytes())
        traffic = [json.loads(line) for line in (held / MCP_FILE).read_text().splitlines()]
        self.assertEqual([entry["tool"] for entry in traffic if entry["direction"] == "request"],
                         [None, None, "ledger", "submit"])
        self.assertTrue(all(entry["bytes"] > 0 for entry in traffic
                            if entry["direction"] == "request"))
        submissions = [json.loads(line) for line in
                       (held / SUBMISSIONS_FILE).read_text().splitlines()]
        self.assertEqual([(entry["payload"], entry["verdict"]) for entry in submissions],
                         [(payload, "receipt")])
        stdout = (held / STDOUT_FILE).read_text()
        self.assertTrue(stdout.strip(), "the CLI stream was not retained")
        outcome = next(fields for kind, fields in host.events.items
                       if kind == "request_outcome")
        self.assertEqual(outcome["directory"], "request-1")
        self.assertEqual(sorted(outcome["files"]),
                         sorted((MCP_FILE, PROMPT_FILE, STDERR_FILE, STDOUT_FILE,
                                 SUBMISSIONS_FILE)))
        text = []
        show_run.describe_request(text.append, 1, [
            {"kind": kind, "fields": fields} for kind, fields in host.events.items], logs)
        self.assertIn("tool ledger: sent", "\n".join(text))
        self.assertIn("submission 1:", "\n".join(text))


if __name__ == "__main__":
    unittest.main()


class NativeDebugRetentionTests(unittest.TestCase):
    """The CLI's own debug log is copied after the turn, bounded and redacted."""

    def test_the_debug_log_is_copied_redacted_and_only_when_it_exists(self):
        with tempfile.TemporaryDirectory() as root:
            source = Path(root) / "scratch" / "native-debug.txt"
            source.parent.mkdir()
            record = RunRecords(root, "all").consultation(1)
            record.native_debug(source)
            self.assertFalse((record.directory / DEBUG_FILE).exists())
            source.write_text("mcp: whiel connected\nAuthorization: Bearer sk-ant-secret123456\n")
            record.native_debug(source)
            held = record.close()
            text = (record.directory / DEBUG_FILE).read_text()
            self.assertIn("mcp: whiel connected", text)
            self.assertNotIn("secret123456", text)
            self.assertIn(DEBUG_FILE, held["files"])
            metadata_only = ConsultationRecord(2)
            metadata_only.native_debug(source)
            self.assertEqual(metadata_only.close(), {})

    def test_the_debug_copy_stops_at_its_cap(self):
        with tempfile.TemporaryDirectory() as root, \
                patch("agent_houdini.run_records.DEBUG_BYTES", 64):
            source = Path(root) / "native-debug.txt"
            source.write_bytes(b"x" * 40 + b"\n" + b"y" * 40 + b"\n" + b"z" * 40 + b"\n")
            record = RunRecords(root, "all").consultation(3)
            record.native_debug(source)
            held = record.close()
            self.assertTrue(held["files"][DEBUG_FILE]["truncated"])
            self.assertIn(TRUNCATED, (record.directory / DEBUG_FILE).read_text())
