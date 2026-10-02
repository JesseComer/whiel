# Author: Fangzhu Shen
"""Strict asynchronous client for the provider-neutral version 3 proposer API.

B owns authorization, semantic validation and API accounting. This client keeps
opaque proposal bytes unchanged and revokes local request access on lifecycle
controls. It contains no native provider, MCP or agent policy.
"""

import asyncio
from dataclasses import dataclass
import os
from pathlib import Path
import re
import struct

from agent_houdini.json_wire import decode, encode
from agent_houdini.runtime_types import RequestView
from agent_houdini.stop import Stop, joined


VERSION = 3
API_VERSION = "3.1.0"
MAX_PACKET_BYTES = 64 * 1024 * 1024
MAX_HEADER_BYTES = 16 * 1024
MAX_CONTROL_BYTES = 1024
# C's existing MCP parser uses these independent logical limits.
MAX_DATA_BYTES = MAX_PACKET_BYTES
MAX_RAW_CHUNK_BYTES = 64 * 1024
MAX_MCP_LINE_BYTES = MAX_DATA_BYTES + 1
U64_MAX = (1 << 64) - 1
U32_MAX = (1 << 32) - 1
QUERY_NAMES = ("countermodel", "strongest_refutations", "history", "ledger",
               "validate_clauses", "evaluate_clauses")
SOCKET_ENV = "WHIEL_PROPOSER_SOCKET"
TOKEN_ENV = "WHIEL_PROPOSER_TOKEN"

_CONTROL = frozenset(("submitted", "rejected", "complete", "request_closed",
                      "cancel", "shutdown", "closed"))
_ENDPOINT = frozenset(("hello", "ready", "shutdown", "closed"))
_TO_B = frozenset(("hello", "query", "submit", "complete", "closed"))
_TO_C = frozenset(("ready", "request", "query_result", "submitted", "rejected",
                   "request_closed", "cancel", "shutdown"))
_FIELDS = {
    "hello": ("capabilities",), "ready": ("api",),
    "request": ("observation_bytes", "response_example_bytes", "remaining_request_budget_ns"),
    "query": ("query_id", "name", "args_bytes"),
    "query_result": ("query_id", "result_bytes"), "submit": ("bytes",),
    "submitted": (), "rejected": ("code",), "complete": ("outcome",),
    "request_closed": (), "cancel": ("reason",), "shutdown": ("reason",), "closed": (),
}
_ATTACHMENTS = {"request": ("observation_bytes", "response_example_bytes"),
                "query": ("args_bytes",), "query_result": ("result_bytes",),
                "submit": ("bytes",)}


class ProtocolError(ValueError):
    """Invalid wire identity, framing, declaration or phase; no payload echo."""


class EndpointError(ConnectionError):
    """The API connection is no longer usable."""


class QueryUnavailable(ProtocolError):
    """The requested operation was not included in this endpoint's negotiation."""


class RequestRevoked(RuntimeError):
    def __init__(self, reason):
        self.reason = reason
        super().__init__(f"proposer request revoked: {reason}")


class SubmissionRejected(ProtocolError):
    def __init__(self, code):
        self.code = code
        super().__init__(f"proposal transport rejected: {code}")


def require(condition, message):
    if not condition:
        raise ProtocolError(message)


def exact_keys(value, keys):
    require(type(value) is dict and set(value) == set(keys), "unexpected JSON fields")


def _integer(value, maximum=U64_MAX, minimum=0):
    require(type(value) is int and minimum <= value <= maximum, "invalid unsigned integer")


def _decimal(value):
    require(type(value) is str and re.fullmatch(r"0|[1-9][0-9]{0,19}", value)
            is not None, "invalid canonical decimal")
    number = int(value)
    _integer(number)
    return number


def _version(value):
    require(type(value) is str, "invalid API version")
    parts = value.split(".")
    require(len(parts) == 3, "invalid API version")
    return tuple(_decimal(part) for part in parts)


def _names(value):
    require(type(value) is list and len(value) <= 128, "invalid API operation list")
    require(all(type(name) is str and 0 < len(name.encode("utf-8")) <= 64
                for name in value), "invalid API operation name")
    require(len(set(value)) == len(value), "duplicate API operation name")


def _capabilities(value):
    exact_keys(value, ("version", "supported_operations", "required_operations"))
    _version(value["version"])
    _names(value["supported_operations"])
    _names(value["required_operations"])
    require(set(value["required_operations"]) <= set(value["supported_operations"]),
            "required API operation is unsupported")


def _negotiated(value):
    exact_keys(value, ("version", "operations"))
    _version(value["version"])
    _names(value["operations"])


def valid_token(token):
    return type(token) is str and re.fullmatch(r"[0-9a-f]{64}", token) is not None


def next_sequence(sequence):
    _integer(sequence)
    require(sequence < U64_MAX, "proposer sequence exhausted")
    return sequence + 1


def _advance(sequence):
    return None if sequence == U64_MAX else sequence + 1


def attachment_lengths(operation):
    require(type(operation) is dict, "invalid operation")
    kind = operation.get("kind")
    require(type(kind) is str and kind in _FIELDS, "invalid operation kind")
    exact_keys(operation, ("kind", *_FIELDS[kind]))
    lengths = tuple(operation[field] for field in _ATTACHMENTS.get(kind, ()))
    for length in lengths:
        _integer(length, U32_MAX)
    if kind == "hello":
        _capabilities(operation["capabilities"])
    elif kind == "ready":
        _negotiated(operation["api"])
    elif kind == "request":
        budget = operation["remaining_request_budget_ns"]
        if budget is not None:
            _decimal(budget)
    elif kind in ("query", "query_result"):
        _integer(operation["query_id"], minimum=1)
        if kind == "query":
            name = operation["name"]
            require(type(name) is str and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]{0,63}", name)
                    is not None, "invalid query name")
    elif kind == "rejected":
        require(operation["code"] in ("too_large", "duplicate_submission"), "invalid rejection")
    elif kind == "complete":
        require(operation["outcome"] in ("response", "source_exhausted", "no_response", "failure"),
                "invalid completion outcome")
    elif kind == "cancel":
        require(operation["reason"] in ("deadline", "cancelled", "failure"), "invalid cancellation")
    elif kind == "shutdown":
        require(operation["reason"] in ("complete", "cancelled", "failure"), "invalid shutdown")
    return lengths


def decode_header(data, token, sequence, direction):
    require(type(data) is bytes and 0 < len(data) <= MAX_HEADER_BYTES, "invalid header length")
    try:
        frame = decode(data, maximum=MAX_HEADER_BYTES)
    except ValueError as error:
        raise ProtocolError("invalid header JSON") from error
    exact_keys(frame, ("wire_version", "endpoint_token", "sequence", "request_id", "operation"))
    _integer(frame["wire_version"])
    _integer(frame["sequence"])
    require(sequence is not None and frame["wire_version"] == VERSION
            and frame["sequence"] == sequence and valid_token(frame["endpoint_token"])
            and frame["endpoint_token"] == token, "wire identity or sequence mismatch")
    operation = frame["operation"]
    lengths = attachment_lengths(operation)
    kind = operation["kind"]
    require(direction in ("to_b", "to_c") and kind in (_TO_B if direction == "to_b" else _TO_C),
            "wrong packet direction")
    if kind in _ENDPOINT:
        require(frame["request_id"] is None, "unexpected request scope")
    else:
        _integer(frame["request_id"], minimum=1)
    require(len(data) <= (MAX_CONTROL_BYTES if kind in _CONTROL else MAX_HEADER_BYTES),
            "control header exceeds bound")
    require(4 + len(data) + sum(lengths) <= MAX_PACKET_BYTES, "aggregate packet exceeds bound")
    return frame, lengths


def encode_packet(token, sequence, request_id, operation, attachments=()):
    require(type(attachments) is tuple and all(type(part) is bytes for part in attachments),
            "attachments must be immutable bytes")
    attachment_lengths(operation)
    frame = {"wire_version": VERSION, "endpoint_token": token, "sequence": sequence,
             "request_id": request_id, "operation": operation}
    try:
        header = encode(frame, maximum=MAX_HEADER_BYTES)
    except ValueError as error:
        raise ProtocolError("invalid outgoing header") from error
    _, lengths = decode_header(header, token, sequence,
                               "to_b" if operation.get("kind") in _TO_B else "to_c")
    require(tuple(map(len, attachments)) == lengths, "attachment length mismatch")
    return (struct.pack(">I", len(header)), header, *attachments)


async def read_packet(reader, token, sequence, direction, check_phase=None):
    require(sequence is not None, "proposer sequence exhausted")
    try:
        prefix = await reader.readexactly(4)
        size, = struct.unpack(">I", prefix)
        require(0 < size <= MAX_HEADER_BYTES, "invalid header length")
        header = await reader.readexactly(size)
        frame, lengths = decode_header(header, token, sequence, direction)
        if check_phase is not None:
            check_phase(frame)
        parts = tuple([await reader.readexactly(length) for length in lengths])
        return frame, parts
    except (asyncio.IncompleteReadError, ConnectionError, OSError) as error:
        raise EndpointError("truncated or failed API connection") from error


@dataclass(frozen=True, slots=True)
class RequestEvent:
    access: object
    stop: Stop


@dataclass(frozen=True, slots=True)
class ShutdownEvent:
    reason: str


class _Request:
    def __init__(self, client, view):
        self._client = client
        self._view = view
        self._stop = Stop()
        self._queries = {}
        self._next_query = 1
        self._submit = None
        self._receipt = False
        self._completion = None
        self._closed = asyncio.get_running_loop().create_future()
        self._closed.add_done_callback(_consume_exception)
        self._revoked = None

    @property
    def view(self):
        return self._view

    @property
    def query_names(self):
        return self._client.query_names

    def _check(self):
        if self._revoked is not None:
            raise RequestRevoked(self._revoked)
        require(self._client._request is self and self._completion is None,
                "inactive request access")
        self._client._check_connection()

    def _revoke(self, reason, error=None):
        if self._revoked in (None, "completed"):
            self._revoked = reason
        if reason != "completed":
            self._stop.set(reason)
        self._fail_waiters(error or RequestRevoked(self._revoked))

    def _fail_waiters(self, error):
        for future in self._queries.values():
            _fail_future(future, error)
        if self._submit is not None:
            _fail_future(self._submit, error)

    async def query(self, name, arguments):
        require(type(arguments) is bytes, "query arguments must be immutable bytes")
        async with self._client._writer_lock:
            self._check()
            if name not in self.query_names:
                raise QueryUnavailable("query was not negotiated")
            require(self._next_query is not None, "query identifier exhausted")
            query_id = self._next_query
            operation = {"kind": "query", "query_id": query_id, "name": name,
                         "args_bytes": len(arguments)}
            packet = self._client._packet(self, operation, (arguments,))
            future = self._client._future()
            self._queries[query_id] = future
            self._next_query = _advance(query_id)
            await self._client._write(packet, self)
        return await asyncio.shield(future)

    async def submit(self, proposal):
        require(type(proposal) is bytes, "proposal must be immutable bytes")
        async with self._client._writer_lock:
            self._check()
            require(self._submit is None, "duplicate submission")
            packet = self._client._packet(self, {"kind": "submit", "bytes": len(proposal)},
                                          (proposal,))
            self._submit = self._client._future()
            await self._client._write(packet, self)
        await asyncio.shield(self._submit)


def _consume_exception(future):
    # The caller may have cancelled its shielded waiter; retain correlation and
    # consume terminal exceptions without producing orphaned-Future warnings.
    if not future.cancelled():
        future.exception()


def _fail_future(future, error):
    if not future.done():
        future.set_exception(error)


class ApiClient:
    """One duplex reader and serialized writer for one input-scoped endpoint.

    Only the C coordinator uses lifecycle methods. Native tooling receives a
    RequestAccess, never this object. close() joins only API I/O; the coordinator
    must join all its native work before acknowledging closed().
    """

    def __init__(self, reader, writer, token, supported_operations=QUERY_NAMES,
                 required_operations=()):
        require(valid_token(token), "invalid endpoint token")
        self._capabilities = {"version": API_VERSION,
                              "supported_operations": list(supported_operations),
                              "required_operations": list(required_operations)}
        _capabilities(self._capabilities)
        self._reader, self._writer, self._token = reader, writer, token
        self._writer_lock = asyncio.Lock()
        self._send_sequence = self._receive_sequence = 0
        self._next_request = 1
        self._phase = "handshake"
        self._request = None
        self._error = None
        self._writing_request = None
        self._reader_task = None
        self._close_task = None
        self._events = asyncio.Queue(maxsize=2)
        self._ready = self._future()
        self._query_names = ()
        self._shutdown_reason = None

    @staticmethod
    def _future():
        future = asyncio.get_running_loop().create_future()
        future.add_done_callback(_consume_exception)
        return future

    @property
    def query_names(self):
        return self._query_names

    @property
    def shutdown_reason(self):
        """Read-only lifecycle status for the C coordinator during native work."""
        return self._shutdown_reason

    @classmethod
    async def connect(cls, socket_path, token, **options):
        require(type(socket_path) in (str, Path) or isinstance(socket_path, Path),
                "invalid endpoint socket path")
        require(Path(socket_path).is_absolute() and valid_token(token), "invalid API bootstrap")
        reader, writer = await asyncio.open_unix_connection(socket_path, limit=MAX_HEADER_BYTES)
        client = None
        try:
            client = cls(reader, writer, token, **options)
            await client.start()
            return client
        except BaseException:
            if client is not None:
                await client.close()
            else:
                writer.transport.abort()
                await writer.wait_closed()
            raise

    @classmethod
    async def from_environment(cls, environment=None, **options):
        environment = os.environ if environment is None else environment
        require(SOCKET_ENV in environment and TOKEN_ENV in environment, "missing API bootstrap")
        return await cls.connect(environment[SOCKET_ENV], environment[TOKEN_ENV], **options)

    async def start(self):
        require(self._reader_task is None, "endpoint already started")
        self._reader_task = asyncio.create_task(self._read_loop(), name="proposer-api-reader")
        async with self._writer_lock:
            await self._write(self._packet(None, {"kind": "hello", "capabilities": self._capabilities}))
        await asyncio.shield(self._ready)

    def _check_connection(self):
        if self._error is not None:
            raise self._error
        require(self._phase not in ("shutdown", "closed"), "endpoint is shutting down")

    def _packet(self, request, operation, attachments=()):
        self._check_connection()
        return encode_packet(self._token, self._send_sequence,
                             None if request is None else request.view.request_id,
                             operation, attachments)

    async def _write(self, parts, request=None):
        # Validation precedes state changes. A cancelled partial frame can never
        # be followed by another frame on the same byte stream.
        self._writing_request = request
        try:
            for part in parts:
                self._writer.write(part)
            await self._writer.drain()
            self._send_sequence = _advance(self._send_sequence)
        except asyncio.CancelledError:
            self._fail(EndpointError("API write cancelled before completion"))
            raise
        except (ConnectionError, OSError) as error:
            failure = EndpointError("API write failed")
            self._fail(failure)
            if request is not None and request._revoked is not None:
                raise RequestRevoked(request._revoked) from error
            raise failure from error
        finally:
            self._writing_request = None

    def _check_phase(self, frame):
        kind = frame["operation"]["kind"]
        if self._phase == "handshake":
            require(kind == "ready", "ready required before other messages")
            api = frame["operation"]["api"]
            version = _version(api["version"])
            require(version[0] == 3 and version <= _version(API_VERSION), "incompatible negotiated API")
            require(set(api["operations"]) <= set(self._capabilities["supported_operations"])
                    and set(self._capabilities["required_operations"]) <= set(api["operations"]),
                    "negotiated API violates declaration")
            return
        if kind == "shutdown":
            require(self._phase not in ("shutdown", "closed"), "duplicate shutdown")
            return
        if self._phase == "idle":
            require(kind == "request" and self._next_request is not None
                    and frame["request_id"] == self._next_request, "unexpected request or phase")
            return
        request = self._request
        require(request is not None and frame["request_id"] == request.view.request_id,
                "stale request scope")
        if kind == "request_closed":
            require(request._completion is not None, "request closed before completion")
        elif kind == "cancel":
            require(request._revoked in (None, "completed"), "duplicate or late cancellation")
        elif kind == "query_result":
            require(frame["operation"]["query_id"] in request._queries,
                    "unmatched query result")
        elif kind in ("submitted", "rejected"):
            require(request._submit is not None and not request._receipt,
                    "unmatched submission receipt")
        else:
            raise ProtocolError("unexpected request operation")

    async def _read_loop(self):
        try:
            while True:
                frame, parts = await read_packet(self._reader, self._token, self._receive_sequence,
                                                 "to_c", self._check_phase)
                self._receive_sequence = _advance(self._receive_sequence)
                operation = frame["operation"]
                kind = operation["kind"]
                if kind == "ready":
                    self._query_names = tuple(operation["api"]["operations"])
                    self._phase = "idle"
                    self._ready.set_result(None)
                elif kind == "request":
                    for part in parts:
                        decode(part)
                    raw_budget = operation["remaining_request_budget_ns"]
                    view = RequestView(frame["request_id"], parts[0], parts[1],
                                       None if raw_budget is None else _decimal(raw_budget))
                    request = _Request(self, view)
                    self._request = request
                    self._phase = "active"
                    self._next_request = _advance(view.request_id)
                    self._events.put_nowait(RequestEvent(request, request._stop))
                elif kind == "query_result":
                    decode(parts[0])
                    future = self._request._queries.pop(operation["query_id"])
                    if not future.done():
                        future.set_result(parts[0])
                elif kind == "submitted":
                    self._request._receipt = True
                    if not self._request._submit.done():
                        self._request._submit.set_result(None)
                elif kind == "rejected":
                    raise SubmissionRejected(operation["code"])
                elif kind == "cancel":
                    self._request._revoke(operation["reason"])
                    if self._writing_request is self._request or self._request._completion is not None:
                        raise EndpointError("cancel interrupted an API frame or raced completion")
                elif kind == "request_closed":
                    request = self._request
                    request._revoke("request_closed")
                    request._closed.set_result(None)
                    self._request = None
                    self._phase = "idle"
                elif kind == "shutdown":
                    self._shutdown_reason = operation["reason"]
                    self._phase = "shutdown"
                    if self._request is not None:
                        self._request._revoke(operation["reason"])
                        _fail_future(self._request._closed, RequestRevoked(operation["reason"]))
                    self._clear_events()
                    self._events.put_nowait(ShutdownEvent(operation["reason"]))
                    if self._writing_request is not None:
                        raise EndpointError("shutdown interrupted an API frame")
                    return
        except asyncio.CancelledError:
            if self._phase != "closed":
                self._fail(EndpointError("API reader stopped"))
            raise
        except (ValueError, ConnectionError, OSError, asyncio.QueueFull) as error:
            failure = error if isinstance(error, (ProtocolError, EndpointError)) else ProtocolError("invalid API data")
            self._fail(failure)

    def _clear_events(self):
        while not self._events.empty():
            self._events.get_nowait()

    def _fail(self, error):
        if self._error is None:
            self._error = error
        if self._request is not None:
            self._request._revoke("failure", self._error)
            _fail_future(self._request._closed, self._error)
        _fail_future(self._ready, self._error)
        self._clear_events()
        self._events.put_nowait(None)
        self._writer.transport.abort()

    async def next_event(self):
        if self._error is not None:
            raise self._error
        require(self._phase != "closed", "endpoint already closed")
        require(self._phase != "shutdown" or not self._events.empty(), "shutdown already delivered")
        event = await self._events.get()
        if self._error is not None:
            raise self._error
        return event

    async def complete(self, access, outcome):
        require(outcome in ("response", "source_exhausted", "no_response", "failure"),
                "invalid completion outcome")
        async with self._writer_lock:
            self._check_connection()
            require(access is self._request and access._completion is None, "inactive completion")
            if access._revoked is not None:
                require(outcome == "failure", "revoked request must complete as failure")
            if outcome == "response":
                require(access._receipt, "response requires completed receipt")
            elif outcome in ("no_response", "source_exhausted"):
                require(access._submit is None, "completion conflicts with submission")
            if outcome != "failure":
                require(not access._queries, "completion has outstanding queries")
            packet = self._packet(access, {"kind": "complete", "outcome": outcome})
            access._completion = outcome
            access._revoke(access._revoked or "completed")
            await self._write(packet, access)
        await asyncio.shield(access._closed)

    async def closed(self):
        require(self._phase == "shutdown" and self._error is None, "shutdown required before closed")
        async with self._writer_lock:
            packet = encode_packet(self._token, self._send_sequence, None, {"kind": "closed"})
            await self._write(packet)
        await self._join_close(graceful=True)

    async def close(self):
        await self._join_close(graceful=False)

    async def _join_close(self, graceful):
        if self._close_task is None:
            self._close_task = asyncio.create_task(self._close_io(graceful), name="proposer-api-close")
        await joined(self._close_task, on_cancel=self._writer.transport.abort)

    async def _close_io(self, graceful):
        self._phase = "closed"
        if self._request is not None:
            self._request._revoke("closed")
            _fail_future(self._request._closed, EndpointError("API client closed"))
        error = EndpointError("API client closed")
        if self._error is None:
            self._error = error
        _fail_future(self._ready, self._error)
        self._clear_events()
        self._events.put_nowait(None)
        if graceful:
            self._writer.close()
        else:
            self._writer.transport.abort()
        if self._reader_task is not None and self._reader_task is not asyncio.current_task():
            self._reader_task.cancel()
            await asyncio.gather(self._reader_task, return_exceptions=True)
        try:
            await self._writer.wait_closed()
        except (ConnectionError, OSError):
            pass
