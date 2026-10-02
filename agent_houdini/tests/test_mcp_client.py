# Author: Fangzhu Shen
"""RPC parity and local presentation tests for the production Python client."""

import asyncio
import unittest
from unittest.mock import patch

from agent_houdini.json_wire import decode, encode
from agent_houdini.mcp_client import McpClient, ProtocolError
from agent_houdini.protocol import EndpointError, QueryUnavailable, RequestRevoked, SubmissionRejected
from agent_houdini.skills import SkillCatalog
from agent_houdini.submission_check import (
    admission_refusal, expected_binding, payload_refusal, push_checks,
)
from agent_houdini.tool_catalog import ToolCatalog


async def ready():
    pass


class Queries:
    """Fake narrow RequestAccess: refused calls never become endpoint requests."""
    def __init__(self, replies=(), query_names=("ledger",)):
        self.requests = []
        self.replies = list(replies)
        self.query_names = query_names
        self.revoked = False

    def check(self):
        if self.revoked:
            raise RequestRevoked("private revocation detail")

    def response(self, default):
        result = self.replies.pop(0) if self.replies else default
        if isinstance(result, BaseException):
            raise result
        return result

    async def submit(self, payload):
        self.check()
        self.requests.append(("submit", payload))
        return self.response(None)

    async def query(self, name, arguments):
        self.check()
        if name not in self.query_names:
            raise QueryUnavailable("private unavailable query detail")
        self.requests.append((name, arguments))
        return self.response(b"{}")


async def rpc(client, method, params=None, identifier=1):
    result = (await client.line(encode({"jsonrpc": "2.0", "id": identifier, "method": method, "params": params}) + b"\n"))
    return decode(result) if result is not None else None


async def initialized(catalog=None, query_names=("ledger",), replies=(), native_ready=ready):
    queries = Queries(replies, query_names)
    client = McpClient(catalog or ToolCatalog(), query_names, queries, native_ready=native_ready)
    (await rpc(client, "initialize"))
    return client, queries


class McpTests(unittest.IsolatedAsyncioTestCase):
    async def test_initialize_listing_ping_and_resource_refusal_are_local(self):
        client, queries = (await initialized(query_names=()))
        result = (await rpc(client, "initialize"))["result"]
        self.assertEqual(result, {"protocolVersion": "2025-06-18", "capabilities": {"tools": {}, "resources": {}},
                                  "serverInfo": {"name": "whiel-agent-tools", "version": "1"}})
        self.assertEqual((await rpc(client, "ping"))["result"], {})
        self.assertEqual((await rpc(client, "resources/list"))["result"], {"resources": []})
        self.assertEqual((await rpc(client, "resources/templates/list"))["result"], {"resourceTemplates": []})
        self.assertEqual([tool["name"] for tool in (await rpc(client, "tools/list"))["result"]["tools"]], ["submit"])
        self.assertEqual((await rpc(client, "resources/read", {"uri": "file:///Benchmark/Certificate/Valid.lean"}))["error"]["message"], "Resources are unavailable")
        self.assertEqual((await rpc(client, "tools/call", {"name": "read_file", "arguments": {}}))["error"]["message"], "Unknown tool or invalid arguments")
        self.assertEqual(queries.requests, [])

    async def test_notifications_and_null_id_never_dispatch(self):
        client, queries = (await initialized())
        for request in ({"jsonrpc": "2.0", "method": "notifications/initialized"},
                        {"jsonrpc": "2.0", "id": None, "method": "tools/call", "params": {"name": "submit", "arguments": {"payload": "x"}}},
                        {"jsonrpc": "other", "method": "initialize"}):
            self.assertIsNone((await client.line(encode(request) + b"\n")))
        self.assertEqual(queries.requests, [])

    async def test_strict_malformed_rpc_and_preinitialize_errors(self):
        client = McpClient(ToolCatalog(), [], Queries(), native_ready=ready)
        self.assertEqual((await rpc(client, "ping"))["error"]["code"], -32002)
        for value in (b"not json\n", b"[]\n", b'{"jsonrpc":"2.0","id":1,"method":"x","surprise":1}\n',
                      b'{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"submit","arguments":{"payload":"a","payload":"b"}}}\n',
                      b'{"jsonrpc":"2.0","id":1,"method":false}\n'):
            self.assertEqual(decode((await client.line(value)))["error"]["code"], -32700)
        for identifier in (True, [], {}):
            self.assertEqual((await rpc(client, "ping", identifier=identifier))["error"]["code"], -32600)
        (await rpc(client, "initialize"))
        self.assertEqual((await rpc(client, "unknown"))["error"]["code"], -32601)

    async def test_exact_opaque_proposal_receipt_and_second_submit(self):
        client, queries = (await initialized())
        payload = '  {"bad":true, "bad":false, "unicode":"λ"}\n\t'
        received = (await rpc(client, "tools/call", {"name": "submit", "arguments": {"payload": payload}, "_meta": {"x": 1}}))
        self.assertEqual(received["result"], {"content": [{"type": "text", "text": "Submission received."}], "isError": False})
        self.assertEqual(queries.requests, [("submit", payload.encode())])
        self.assertIn("already has a submission", (await rpc(client, "tools/call", {"name": "submit", "arguments": {"payload": "second"}}))["error"]["message"])
        self.assertEqual(len(queries.requests), 1)

    async def test_rejected_submit_cannot_manufacture_receipt(self):
        client, queries = (await initialized(replies=[SubmissionRejected("private rejected payload")]))
        reply = (await rpc(client, "tools/call", {"name": "submit", "arguments": {"payload": "first"}}))
        self.assertEqual(reply["error"]["message"], "Tool call rejected by the current request")
        self.assertFalse(client.submitted)
        self.assertEqual(queries.requests, [("submit", b"first")])

    async def test_invalid_arguments_do_not_reach_query_endpoint(self):
        client, queries = (await initialized())
        for params in (None, {}, {"name": "submit"}, {"name": "submit", "arguments": {}, "extra": 1},
                       {"name": "submit", "arguments": {"payload": 2}},
                       {"name": "submit", "arguments": {"payload": "x", "binding": {}}}):
            self.assertIn("error", (await rpc(client, "tools/call", params)))
        self.assertEqual(queries.requests, [])

    async def test_local_skill_has_no_query_or_evidence_envelope(self):
        catalog = ToolCatalog(skills=SkillCatalog.from_json(b'{"guide":{"text":"local"}}'))
        client, queries = (await initialized(catalog=catalog, query_names=()))
        self.assertEqual([tool["name"] for tool in (await rpc(client, "tools/list"))["result"]["tools"]], ["submit", "get_skill"])
        good = (await rpc(client, "tools/call", {"name": "get_skill", "arguments": {"id": "guide"}}))["result"]
        self.assertEqual(decode(good["content"][0]["text"].encode()), {"id": "guide", "content": {"text": "local"}})
        self.assertFalse(good["isError"])
        missing = (await rpc(client, "tools/call", {"name": "get_skill", "arguments": {"id": "missing"}}))["result"]
        self.assertTrue(missing["isError"])
        self.assertEqual(queries.requests, [])

    async def test_canonical_query_is_gated_even_when_disabled_in_inventory(self):
        client, queries = (await initialized(query_names=(), replies=[]))
        result = (await rpc(client, "tools/call", {"name": "ledger", "arguments": {}}))
        self.assertIn("error", result)
        self.assertEqual(queries.requests, [])

    async def test_canonical_response_error_preserves_historical_single_envelope(self):
        value = {"state_revision": 2, "error": {"code": "invalid_arguments"}}
        data = encode(value)
        client, _ = (await initialized(replies=[data]))
        result = (await rpc(client, "tools/call", {"name": "ledger", "arguments": {}}))["result"]
        self.assertFalse(result["isError"])
        self.assertEqual(decode(result["content"][0]["text"].encode()), value)

    async def test_output_limit_includes_newline_and_oversize_diagnostics_stay_distinct(self):
        client, _ = (await initialized())
        request = b'{"jsonrpc":"2.0","id":1,"method":"initialize"}\n'
        complete = (await client.line(request))
        # A small cap exercises the same arithmetic without allocating 64 MiB.
        with patch("agent_houdini.mcp_client.MAX_DATA_BYTES", len(complete)):
            self.assertEqual((await client.line(request)), complete)
        with patch("agent_houdini.mcp_client.MAX_DATA_BYTES", len(complete) - 1):
            with self.assertRaisesRegex(ProtocolError, "response not delivered"):
                (await client.line(request))
        with patch("agent_houdini.mcp_client.MAX_DATA_BYTES", 8):
            with self.assertRaisesRegex(ProtocolError, "payload not semantically checked"):
                (await client.line(b"123456789\n"))

    async def test_line_shape_is_exactly_one_terminated_line(self):
        client, _ = (await initialized())
        for line in (b"", b'{"jsonrpc":"2.0","id":1,"method":"ping"}', b"a\nb\n"):
            with self.subTest(line=line), self.assertRaises(ProtocolError):
                (await client.line(line))

    async def test_local_startup_rpcs_do_not_wait_for_native_ready(self):
        waiting, release = asyncio.Event(), asyncio.Event()

        async def native_ready():
            waiting.set()
            await release.wait()

        catalog = ToolCatalog(skills=SkillCatalog.from_json(b'{"guide":"local"}'))
        client, queries = await asyncio.wait_for(
            initialized(catalog=catalog, native_ready=native_ready), 1)
        for method, params in (("ping", None), ("tools/list", None), ("resources/list", None),
                               ("resources/templates/list", None),
                               ("tools/call", {"name": "get_skill", "arguments": {"id": "guide"}})):
            self.assertIn("result", await asyncio.wait_for(rpc(client, method, params), 1))
        self.assertFalse(waiting.is_set())
        task = asyncio.create_task(rpc(client, "tools/call", {"name": "ledger", "arguments": {}}))
        await asyncio.wait_for(waiting.wait(), 1)
        self.assertFalse(task.done())
        self.assertEqual(queries.requests, [])
        release.set()
        self.assertIn("result", await asyncio.wait_for(task, 1))
        self.assertEqual(queries.requests, [("ledger", b"{}")])

    async def test_readiness_is_rechecked_and_revoked_access_refuses_the_query(self):
        readiness = []

        async def native_ready():
            readiness.append(len(queries.requests))
            if len(readiness) == 2:
                queries.revoked = True

        client, queries = await initialized(query_names=("ledger",), native_ready=native_ready)
        self.assertIn("result", await rpc(client, "tools/call", {"name": "ledger", "arguments": {}}))
        result = await rpc(client, "tools/call", {"name": "ledger", "arguments": {}})
        self.assertEqual(readiness, [0, 1])
        self.assertEqual(result["error"]["message"], "Tool call rejected by the current request")
        self.assertEqual(queries.requests, [("ledger", b"{}")])

    async def test_submit_waits_for_readiness_and_completed_receipt(self):
        entered, receipt = asyncio.Event(), asyncio.Event()
        readiness = []

        class ReceiptAccess(Queries):
            async def submit(self, payload):
                self.requests.append(("submit", payload))
                entered.set()
                await receipt.wait()

        async def native_ready():
            readiness.append("ready")

        access = ReceiptAccess()
        client = McpClient(ToolCatalog(), (), access, native_ready=native_ready)
        await rpc(client, "initialize")
        payload = ' \t{"malformed":"λ", duplicate is deliberately not repaired}\n'
        task = asyncio.create_task(rpc(client, "tools/call",
                                       {"name": "submit", "arguments": {"payload": payload}}))
        await asyncio.wait_for(entered.wait(), 1)
        self.assertEqual(readiness, ["ready"])
        self.assertEqual(access.requests, [("submit", payload.encode())])
        self.assertFalse(client.submitted)
        self.assertFalse(task.done())
        receipt.set()
        response = await asyncio.wait_for(task, 1)
        self.assertEqual(response["result"]["content"][0]["text"], "Submission received.")
        self.assertTrue(client.submitted)

    async def test_async_cancellation_propagates_without_a_submission_receipt(self):
        for phase in ("readiness", "query", "submit"):
            with self.subTest(phase=phase):
                entered, release = asyncio.Event(), asyncio.Event()

                async def suspended():
                    entered.set()
                    await release.wait()

                class SuspendedAccess(Queries):
                    async def query(self, name, arguments):
                        self.requests.append((name, arguments))
                        await suspended()
                        return b"{}"

                    async def submit(self, payload):
                        self.requests.append(("submit", payload))
                        await suspended()

                access = SuspendedAccess()
                client = McpClient(ToolCatalog(), ("ledger",), access,
                                   native_ready=suspended if phase == "readiness" else ready)
                await rpc(client, "initialize")
                params = {"name": "submit", "arguments": {"payload": "opaque"}} if phase == "submit" else {
                    "name": "ledger", "arguments": {}}
                task = asyncio.create_task(rpc(client, "tools/call", params))
                await asyncio.wait_for(entered.wait(), 1)
                task.cancel()
                with self.assertRaises(asyncio.CancelledError):
                    await task
                self.assertFalse(client.submitted)
                self.assertEqual(len(access.requests), 0 if phase == "readiness" else 1)

    async def test_transport_faults_propagate_instead_of_becoming_rpc_refusals(self):
        for fault in (ProtocolError("private payload"), EndpointError("password: secret")):
            with self.subTest(fault=type(fault).__name__):
                client, _ = await initialized(replies=[fault])
                with self.assertRaises(type(fault)) as caught:
                    await rpc(client, "tools/call", {"name": "ledger", "arguments": {}})
                self.assertIs(caught.exception, fault)


if __name__ == "__main__":
    unittest.main()


EXAMPLE_BINDING = {"consultation_digest": "c" * 64, "request_digest": "r" * 64,
                   "run_digest": "u" * 64, "scope_digest": "s" * 64,
                   "state_snapshot_digest": "n" * 64, "task_digest": "t" * 64,
                   "validation_manifest_digest": "v" * 64, "validation_ordinal": 0}


class SubmissionPrecheckTests(unittest.IsolatedAsyncioTestCase):
    """What the push already decides is answered here, not a round later.

    A refusal the verifier raises arrives in the next consultation's
    correction, two minutes and one round later. Every fault below is one the
    coordinator can decide from the push it holds, so it comes back as a tool
    error inside the same turn and the turn may submit again.
    """

    def example(self):
        return encode({"binding": EXAMPLE_BINDING, "clauses": [], "dropped": [],
                       "kind": "candidate_clauses", "schema_version": 4})

    def checks(self, observation=None):
        return push_checks(self.example(), observation)

    def refusal(self, payload, observation=None):
        return payload_refusal(payload, self.checks(observation))

    def response(self, **fields):
        return encode({"binding": EXAMPLE_BINDING, "kind": "candidate_clauses",
                       "schema_version": 4, "clauses": [], "dropped": [], **fields})

    def test_expected_binding_comes_only_from_a_parseable_example_object(self):
        self.assertEqual(expected_binding(self.example()), EXAMPLE_BINDING)
        for broken in (b"", b"[]", b"{", b'{"binding": 3}', "text", None):
            self.assertIsNone(expected_binding(broken))
            self.assertFalse(push_checks(broken).holds_push())

    def test_refusal_names_missing_unexpected_and_changed_keys(self):
        wrong = dict(EXAMPLE_BINDING)
        del wrong["request_digest"]
        wrong["policy_digest"] = "p" * 64
        wrong["validation_ordinal"] = 2
        text = self.refusal(self.response(binding=wrong))
        self.assertIn("missing keys: request_digest", text)
        self.assertIn("keys that do not belong: policy_digest", text)
        self.assertIn("keys with a different value: validation_ordinal", text)
        self.assertIn("RESPONSE EXAMPLE", text)
        self.assertIn("no round was spent", text)
        self.assertNotIn("r" * 64, text)
        self.assertIn("`binding` is missing", self.refusal(b'{"clauses": []}'))
        # The binding is a verbatim copy target, so a differing value is as
        # certain a refusal as a missing key.
        changed = dict(EXAMPLE_BINDING, request_digest="0" * 64)
        self.assertIn("keys with a different value: request_digest",
                      self.refusal(self.response(binding=changed)))
        # An exact copy, a payload that is not an object and a coordinator
        # holding no push all go to the verifier unchanged.
        self.assertIsNone(self.refusal(self.example()))
        self.assertIsNone(self.refusal(b"[1]"))
        self.assertIsNone(payload_refusal(b'{"binding": {}}', push_checks(None)))

    def test_only_a_decoder_position_refuses_a_payload_that_is_not_json(self):
        """A parse failure C can locate is certain; a bound it cannot is not.

        The verifier's decoder and this one agree on what parses, so a
        position C can name is a refusal C can be certain of. A duplicate key,
        a nesting bound or an oversized document may yet be read differently,
        so those go to the verifier as before.
        """
        for payload in (self.example() + b"}", self.example()[:-4],
                        self.example() + b"</payload>"):
            text = self.refusal(payload)
            self.assertIn("not one complete JSON value", text)
            self.assertIn("at character", text)
            self.assertIn("no round was spent", text)
            self.assertNotIn("binding", text.split("(")[1])
        self.assertIsNone(self.refusal(b'{"a": 1, "a": 2}'))
        self.assertIsNone(self.refusal(b"x" * (4 * 1024 * 1024 + 1)))

    def test_a_drop_the_push_did_not_authorize_is_refused_by_its_index(self):
        reference = {"clause": {"clause_id": 7, "record_digest": "a" * 64,
                                "formula_digest": "b" * 64},
                     "consultation_digest": "c" * 64, "authorization_digest": "d" * 64}
        observation = {"feedback": {"pending": [{"drop_reference": reference}]}}
        self.assertIsNone(self.refusal(self.response(dropped=[reference]), observation))
        stale = {**reference, "authorization_digest": "e" * 64}
        text = self.refusal(self.response(dropped=[reference, stale]), observation)
        self.assertIn("`dropped[1]`", text)
        self.assertIn("IDENTITIES AND DROP REFERENCES", text)
        # A reference carrying the clause text the push showed beside it is
        # the verifier's to judge, and so is one C cannot read as a reference.
        whole = {**reference, "clause": {**reference["clause"],
                                         "canonical_source": "(op_zT = ∅[2])"}}
        self.assertIsNone(self.refusal(self.response(dropped=[whole]), observation))
        self.assertIsNone(self.refusal(self.response(dropped=[{"clause": 1}]), observation))
        self.assertIsNone(self.refusal(self.response(dropped=[stale])))

    def test_a_formula_the_push_reports_dead_is_refused_before_it_is_sent(self):
        def entry(source, cause):
            return {"clause": {"clause_id": 4, "record_digest": "a" * 64,
                               "formula_digest": "b" * 64, "canonical_source": source},
                    "outcome": {"kind": "dead", "cause": cause}}
        observation = {"feedback": {"last_round": [entry("(op_zT = ∅[2])", "refuted"),
                                                   entry("(op_zS = ∅[2])", "dropped")]}}
        text = self.refusal(self.response(clauses=["(op_zS ⊆ op_zT)", "(op_zT = ∅[2])"]),
                            observation)
        self.assertIn("`clauses[1]`", text)
        self.assertIn("dead by refutation", text)
        # A clause dead by a drop of your own is revived by exactly this
        # resubmission, and a clause the push never named is not C's to judge.
        self.assertIsNone(self.refusal(self.response(clauses=["(op_zS = ∅[2])"]), observation))
        self.assertIsNone(self.refusal(self.response(clauses=["(op_zT = ∅[3])"]), observation))

    def test_an_admission_answer_refuses_only_what_it_names(self):
        clauses = ["(op_zT = ∅[2])", "(op_zS ⊇ op_zT)"]
        reply = {"tool": "validate_clauses", "state_revision": 3, "result": {"results": [
            {"source": clauses[0], "admitted": True},
            {"source": clauses[1], "admitted": False, "correctable": {
                "code": "clause_lexical_error", "message": "clause contains unsupported lexical input",
                "item_index": None, "path": None, "offset": 8}}]}}
        text = admission_refusal(reply, clauses)
        self.assertIn("`clauses[1]`", text)
        self.assertIn("clause_lexical_error", text)
        self.assertIn("offset 8", text)
        self.assertIn("no round was spent", text)
        # Anything C cannot read as that answer leaves the payload alone.
        self.assertIsNone(admission_refusal(reply["result"], clauses))
        self.assertIsNone(admission_refusal(reply, clauses[:1]))
        self.assertIsNone(admission_refusal(
            {"tool": "validate_clauses", "state_revision": 3,
             "error": {"code": "query_unavailable", "message": "no"}}, clauses))

    async def test_a_wrong_binding_is_refused_locally_and_the_turn_may_submit_again(self):
        queries = Queries((), ("ledger",))
        client = McpClient(ToolCatalog(), ("ledger",), queries, native_ready=ready,
                           checks=self.checks())
        (await rpc(client, "initialize"))
        wrong = dict(EXAMPLE_BINDING)
        del wrong["request_digest"]
        payload = encode({"binding": wrong, "clauses": ["c"], "dropped": [],
                          "kind": "candidate_clauses", "schema_version": 4}).decode()
        reply = (await rpc(client, "tools/call", {"name": "submit", "arguments": {"payload": payload}}))
        self.assertTrue(reply["result"]["isError"])
        self.assertIn("missing keys: request_digest", reply["result"]["content"][0]["text"])
        self.assertEqual(queries.requests, [])
        self.assertFalse(client.submitted)
        self.assertEqual(len(client.rejections), 1)
        self.assertTrue(client.rejections[0].startswith("SubmissionPrecheck: "))
        exact = self.example().decode()
        reply = (await rpc(client, "tools/call", {"name": "submit", "arguments": {"payload": exact}}, 2))
        self.assertFalse(reply["result"]["isError"])
        self.assertEqual(queries.requests, [("submit", exact.encode())])
        self.assertTrue(client.submitted)

    async def test_clauses_are_put_to_lean_once_before_the_payload_is_forwarded(self):
        payload = self.response(clauses=["(op_zT = ∅[2])"]).decode()
        answer = encode({"tool": "validate_clauses", "state_revision": 1, "result": {"results": [
            {"source": "(op_zT = ∅[2])", "admitted": False, "correctable": {
                "code": "clause_schema_error", "message": "not well formed",
                "item_index": 0, "path": None, "offset": None}}]}})
        queries = Queries([answer], ("validate_clauses",))
        client = McpClient(ToolCatalog(), ("validate_clauses",), queries,
                           native_ready=ready, checks=self.checks())
        (await rpc(client, "initialize"))
        reply = (await rpc(client, "tools/call", {"name": "submit", "arguments": {"payload": payload}}))
        self.assertTrue(reply["result"]["isError"])
        self.assertIn("clause_schema_error", reply["result"]["content"][0]["text"])
        self.assertEqual([name for name, _ in queries.requests], ["validate_clauses"])
        self.assertFalse(client.submitted)
        # An admitted clause, and a response with no clause text at all, cost
        # the query nothing beyond the one call that answers them.
        admitted = encode({"tool": "validate_clauses", "state_revision": 1,
                           "result": {"results": [{"source": "(op_zT = ∅[2])", "admitted": True}]}})
        queries.replies.append(admitted)
        reply = (await rpc(client, "tools/call",
                           {"name": "submit", "arguments": {"payload": payload}}, 2))
        self.assertFalse(reply["result"]["isError"])
        self.assertEqual([name for name, _ in queries.requests],
                         ["validate_clauses", "validate_clauses", "submit"])

    async def test_an_unavailable_admission_query_leaves_the_payload_to_the_verifier(self):
        payload = self.response(clauses=["(op_zT = ∅[2])"]).decode()
        queries = Queries((), ("ledger",))
        client = McpClient(ToolCatalog(), ("ledger",), queries, native_ready=ready,
                           checks=self.checks())
        (await rpc(client, "initialize"))
        reply = (await rpc(client, "tools/call", {"name": "submit", "arguments": {"payload": payload}}))
        self.assertFalse(reply["result"]["isError"])
        self.assertEqual([name for name, _ in queries.requests], ["submit"])

    async def test_without_an_example_the_payload_is_opaque_as_before(self):
        client, queries = await initialized()
        reply = (await rpc(client, "tools/call", {"name": "submit", "arguments": {"payload": "{\"binding\": {}}"}}))
        self.assertFalse(reply["result"]["isError"])
        self.assertEqual(queries.requests, [("submit", b'{"binding": {}}')])
