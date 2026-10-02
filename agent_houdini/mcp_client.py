# Author: Fangzhu Shen
"""Editable MCP presentation over the read-only host API and submission channel.

This carries the RPC envelopes, local skill lookup and one canonical query per
tool call. It neither evaluates clauses nor grants query permission.
"""

from agent_houdini.agent_log import bounded_redacted_diagnostic
from agent_houdini.json_wire import JsonWireError, decode, encode
from agent_houdini.protocol import (
    MAX_DATA_BYTES, ProtocolError, QueryUnavailable, RequestRevoked,
    SubmissionRejected, require,
)
from agent_houdini.submission_check import (
    PushChecks, admission_refusal, clause_drafts, decoded_payload, payload_refusal,
)


TOO_LARGE = "too_large: 64 MiB encoded transport limit (67108864 bytes); payload not semantically checked"
RESPONSE_TOO_LARGE = "too_large: 64 MiB encoded transport limit (67108864 bytes); response not delivered"


class RpcFailure(Exception):
    def __init__(self, code, message):
        super().__init__(message)
        self.code = code


REJECTED = "Tool call rejected by the current request"
REJECTION_BYTES = 512


def _error(identifier, code, message):
    return {"jsonrpc": "2.0", "id": identifier,
            "error": {"code": code, "message": message}}


def _rejection(error):
    """Name the refusal for C's own log, never for the reply the agent reads.

    A revoked request, an unavailable query and a rejected submission are three
    different events, and the run log recorded none of them. The detail stays on
    this side of the boundary: the agent still receives only the bare sentence.
    """
    text = bounded_redacted_diagnostic(str(error), REJECTION_BYTES).strip()
    return f"{type(error).__name__}" + (f": {text}" if text else "")


def _json(value, *, maximum=MAX_DATA_BYTES):
    try:
        # serde_json::Value objects had sorted keys in the former Rust client.
        return encode(value, sort_keys=True, maximum=maximum)
    except JsonWireError as error:
        raise ProtocolError(RESPONSE_TOO_LARGE) from error


def _content(value, is_error=False):
    return {"content": [{"type": "text", "text": _json(value).decode("utf-8")}],
            "isError": is_error}


class McpClient:
    """One consultation's native MCP state; no native process or raw stdio access."""

    def __init__(self, catalog, query_names, access, *, native_ready, checks=None):
        self.catalog = catalog
        # What this request's push lets C decide about a payload before it is
        # sent: the response example's binding, the drop references the push
        # authorized, and the formulas it reports permanently dead. A payload
        # that one of them refuses is answered here, with the fault named,
        # instead of spending a round on the verifier's own correction. Never
        # used to edit or complete a payload.
        self.checks = PushChecks() if checks is None else checks
        self.query_names = tuple(query_names)
        self.tools = catalog.tools_for_policy(query_names)
        self.access = access
        self.native_ready = native_ready
        self.initialized = False
        self.submitted = False
        # C-local refusal reasons for the run log; never sent to the agent.
        self.rejections = []

    async def line(self, line):
        """Return one complete MCP reply line or None for a notification."""
        require(type(line) is bytes and line.endswith(b"\n") and b"\n" not in line[:-1],
                "MCP line must have exactly one terminal newline")
        if len(line) > MAX_DATA_BYTES:
            raise ProtocolError(TOO_LARGE)
        try:
            request = decode(line)
            require(type(request) is dict
                    and set(request) <= {"jsonrpc", "id", "method", "params"}
                    and {"jsonrpc", "method"} <= set(request)
                    and type(request["jsonrpc"]) is str and type(request["method"]) is str,
                    "invalid RPC envelope")
        except (JsonWireError, ProtocolError):
            response = _error(None, -32700, "Invalid JSON")
        else:
            identifier = request.get("id")
            # Rust's Option<Value> treated both absent and null IDs as a
            # notification, without dispatching even tools/call notifications.
            if identifier is None:
                return None
            if request["jsonrpc"] != "2.0" or type(identifier) not in (str, int, float):
                response = _error(None, -32600, "Invalid JSON-RPC request")
            else:
                try:
                    result = await self.dispatch(request["method"], request.get("params"))
                    response = {"jsonrpc": "2.0", "id": identifier, "result": result}
                except RpcFailure as error:
                    response = _error(identifier, error.code, str(error))
                except (QueryUnavailable, RequestRevoked, SubmissionRejected) as error:
                    self.rejections.append(_rejection(error))
                    response = _error(identifier, -32602, REJECTED)
        # Keep the former client cap: the final newline fits within 64 MiB.
        return _json(response, maximum=MAX_DATA_BYTES - 1) + b"\n"

    async def dispatch(self, method, params):
        if method == "initialize":
            self.initialized = True
            return {"protocolVersion": "2025-06-18",
                    "capabilities": {"tools": {}, "resources": {}},
                    "serverInfo": {"name": "whiel-agent-tools", "version": "1"}}
        if not self.initialized:
            raise RpcFailure(-32002, "Initialize first")
        if method == "ping":
            return {}
        if method == "resources/list":
            return {"resources": []}
        if method == "resources/templates/list":
            return {"resourceTemplates": []}
        if method == "resources/read":
            raise RpcFailure(-32602, "Resources are unavailable")
        if method == "tools/list":
            return {"tools": self.tools}
        if method == "tools/call":
            return await self._call(params)
        raise RpcFailure(-32601, "Unsupported method")

    async def _call(self, params):
        if self.submitted:
            raise RpcFailure(-32602, "This request already has a submission")
        if (type(params) is not dict or set(params) - {"name", "arguments", "_meta"}
                or not {"name", "arguments"} <= set(params) or type(params["name"]) is not str):
            raise RpcFailure(-32602, "Invalid tool arguments")
        name, arguments = params["name"], params["arguments"]
        if name == "submit":
            if (type(arguments) is not dict or set(arguments) != {"payload"}
                    or type(arguments["payload"]) is not str):
                raise RpcFailure(-32602, "Unknown tool or invalid arguments")
            # Only the outer MCP string is decoded. The proposal itself is
            # opaque, including whitespace, malformed JSON and supplied binding.
            payload = arguments["payload"].encode("utf-8")
            await self.native_ready()
            refusal = payload_refusal(payload, self.checks) or await self._admission(payload)
            if refusal is not None:
                self.rejections.append("SubmissionPrecheck: " + refusal)
                return {"content": [{"type": "text", "text": refusal}], "isError": True}
            await self.access.submit(payload)
            self.submitted = True
            return {"content": [{"type": "text", "text": "Submission received."}], "isError": False}
        if name == "get_skill":
            value, is_error = self.catalog.skills.get(arguments)
            return _content(value, is_error)
        query = self.catalog.query(name)
        if query is None:
            raise RpcFailure(-32602, "Unknown tool or invalid arguments")
        # The narrow access handle checks negotiated authority; B independently
        # authorizes every received query.
        await self.native_ready()
        response = decode(await self.access.query(query, _json(arguments)))
        # The canonical response passes through untouched, including isError
        # false for a reply that carries its own inner error.
        return _content(response)

    async def _admission(self, payload):
        """Ask Lean about the payload's clauses before the round is spent.

        `validate_clauses` runs the same admission a submission runs, so a
        clause it refuses is a round the submission would lose, and the answer
        carries the offset the submission-path diagnostic does not. It costs
        one worker round trip, so it is asked only when the run negotiated the
        query and the payload actually carries clause text, and any refusal to
        answer -- an unavailable query, a revoked request, an unreadable reply
        -- leaves the payload to the verifier.
        """
        if not self.checks.holds_push() or "validate_clauses" not in self.query_names:
            return None
        value = decoded_payload(payload)
        clauses = clause_drafts(value) if value is not None else []
        if not clauses:
            return None
        try:
            reply = decode(await self.access.query(
                "validate_clauses", _json({"clauses": clauses})))
        except (QueryUnavailable, RequestRevoked, JsonWireError, ProtocolError) as error:
            self.rejections.append("SubmissionPrecheck skipped: " + _rejection(error))
            return None
        return admission_refusal(reply, clauses)
