# Author: Fangzhu Shen
"""C-local MCP transport, metered API access and native delivery receipts.

Only the coordinator supplies a scoped API access object. The standalone relay
receives C's private socket/token, and never the verifier connection or package.
"""

import asyncio
import hmac
import os
from pathlib import Path
import secrets
import sys

from agent_houdini import mcp_stdio as relay
from agent_houdini.agent_log import bounded_redacted_diagnostic
from agent_houdini.protocol import QueryUnavailable, SubmissionRejected
from agent_houdini.run_records import ConsultationRecord
from agent_houdini.runtime_types import CleanupError, McpLaunch
from agent_houdini.stop import joined


REASON_BYTES = 4096
RELAY_DIAGNOSTIC_BYTES = 4096


class AgentTrafficExhausted(RuntimeError):
    """A C logical traffic allowance refused an observed leg."""


class MeteredRequestAccess:
    """Charge logical canonical payloads once; B counts actual API packets."""

    def __init__(self, access, budget):
        self._access, self._budget = access, budget
        self._receipt_received = False
        self._submission_attempted = False

    @property
    def view(self):
        return self._access.view

    @property
    def query_names(self):
        return self._access.query_names

    @property
    def receipt_received(self):
        return self._receipt_received

    @property
    def submission_attempted(self):
        return self._submission_attempted

    def _charge(self, leg, length, messages):
        try:
            self._budget.charge(leg, length, messages)
        except Exception as error:
            raise AgentTrafficExhausted("C agent traffic allowance exhausted") from error

    async def query(self, name, arguments):
        self._charge("canonical_request", len(arguments), 1)
        try:
            result = await self._access.query(name, arguments)
        except QueryUnavailable:
            # A completed local refusal has no result attachment.
            self._charge("canonical_reply", 0, 1)
            raise
        self._charge("canonical_reply", len(result), 1)
        return result

    async def submit(self, proposal):
        self._charge("canonical_request", len(proposal), 1)
        self._submission_attempted = True
        try:
            await self._access.submit(proposal)
        except SubmissionRejected:
            self._charge("canonical_reply", 0, 1)
            raise
        self._charge("canonical_reply", 0, 1)
        self._receipt_received = True


class McpTransport:
    """One native turn's private listener and relay, with joined I/O cleanup.

    The native runner owns the native/relay processes. This object owns their
    C-local socket and handler tasks, and reports a latched failure for the
    runner's grace-period checks.
    """

    def __init__(self, work, handler, stop, budget, events,
                 interpreter, relay_path, cleanup_timeout, record=None):
        self._socket_path = work / ("mcp-" + secrets.token_hex(5) + ".sock")
        self._diagnostic_path = Path(str(self._socket_path) + relay.DIAGNOSTIC_SUFFIX)
        self._token = secrets.token_hex(32)
        self._handler, self._stop = handler, stop
        self._budget, self._events = budget, events
        self._record = ConsultationRecord(None) if record is None else record
        self._cleanup_timeout = cleanup_timeout
        self._launch = McpLaunch(
            (str(interpreter), str(relay_path)),
            {relay.SOCKET_ENV: str(self._socket_path), relay.TOKEN_ENV: self._token},
            (interpreter, relay_path),
        )
        self._server = None
        self._connections = set()
        self._writers = set()
        self._monitor = None
        self._close_task = None
        self._connection_seen = False
        self._closing = False
        self._failure = None
        self._failure_detail = {}
        self._phase = "listening"
        self._sequence = 0

    @classmethod
    async def create(cls, work, handler, stop, budget, events, *,
                     interpreter=None, relay_path=None, cleanup_timeout=2.0, record=None):
        work = Path(work).resolve(strict=True)
        if not work.is_dir():
            raise ValueError("C MCP scratch must be a directory")
        interpreter = Path(interpreter or sys.executable).resolve(strict=True)
        relay_path = Path(relay_path or Path(__file__).with_name("mcp_stdio.py")).resolve(strict=True)
        if not all(path.is_file() and os.access(path, os.X_OK) for path in (interpreter, relay_path)):
            raise ValueError("C MCP launch requires exact executable files")
        if type(cleanup_timeout) not in (int, float) or not 0 < cleanup_timeout <= 60:
            raise ValueError("invalid C MCP cleanup timeout")
        transport = cls(work, handler, stop, budget, events,
                        interpreter, relay_path, cleanup_timeout, record)
        try:
            transport._server = await asyncio.start_unix_server(
                transport._connected, str(transport._socket_path), limit=relay.MAX_CHUNK_BYTES)
            os.chmod(transport._socket_path, 0o600)
            transport._monitor = asyncio.create_task(transport._watch_stop(), name="agent-mcp-stop")
            transport._emit("mcp_open", {})
            return transport
        except BaseException:
            await transport.close_and_join()
            raise

    @property
    def launch(self):
        return self._launch

    def failure(self):
        return self._failure

    def failure_detail(self):
        """Why the bridge failed, for the runner's own failure record."""
        return dict(self._failure_detail)

    def _emit(self, kind, fields):
        try:
            self._events.emit(kind, fields)
        except Exception:
            self._fail("agent_log_failure", emit=False)
            raise

    def _reason(self, code, error, side):
        """Name the side that ended the exchange, the error and what was in flight.

        A bare code cannot tell a relay that died at provider startup from a
        coordinator that refused a framing rule mid tool call, so every field a
        reader would otherwise have to guess is recorded here.
        """
        text = "no exception; the bridge latched this code directly"
        if error is not None:
            text = f"{type(error).__name__}: {error}"
        return {"code": code, "side": side, "phase": self._phase,
                "relay_sequence": self._sequence,
                "error_class": None if error is None else type(error).__name__,
                "reason": bounded_redacted_diagnostic(text, REASON_BYTES),
                "connection_seen": self._connection_seen,
                **self._record.exchange_fields()}

    def _fail(self, code, *, emit=True, error=None, side="coordinator"):
        if self._failure is None and not self._stop.requested() and not self._closing:
            self._failure = code
            self._failure_detail = self._reason(code, error, side)
            if emit:
                try:
                    self._events.emit("mcp_failure", self._failure_detail)
                except Exception:
                    pass
        self._request_close()

    def _charge(self, leg, length, messages):
        try:
            self._budget.charge(leg, length, messages)
        except Exception:
            self._fail("agent_traffic_exhausted")
            raise

    def _connected(self, reader, writer):
        task = asyncio.create_task(self._connection(reader, writer), name="agent-mcp-connection")
        self._connections.add(task)

    async def _watch_stop(self):
        await self._stop.wait()
        self._request_close()

    def _request_close(self):
        self._closing = True
        if self._server is not None:
            self._server.close()
        current = asyncio.current_task()
        for task in tuple(self._connections):
            if task is not current:
                task.cancel()
        for writer in tuple(self._writers):
            writer.transport.abort()

    async def _header(self, reader, expected_sequence):
        kind, sequence, length = relay.decode_header(await reader.readexactly(relay.HEADER.size))
        relay.require(sequence == expected_sequence, "wrong relay sequence")
        return kind, length

    @staticmethod
    async def _send(writer, kind, sequence, length=0, body=b""):
        writer.write(relay.encode_header(kind, sequence, length))
        if body:
            writer.write(body)
        await writer.drain()

    async def _connection(self, reader, writer):
        self._writers.add(writer)
        try:
            if self._closing:
                return
            if self._connection_seen:
                raise relay.RelayError("duplicate relay connection")
            self._connection_seen = True
            self._phase = "relay_hello"
            kind, length = await self._header(reader, 0)
            relay.require(kind == relay.HELLO, "relay hello required")
            identity = await reader.readexactly(length)
            relay.require(hmac.compare_digest(identity, relay.token_bytes(self._token)), "wrong relay token")
            await self._send(writer, relay.READY, 0)
            sequence, line_bytes = 1, 0
            pending = bytearray()
            while not self._closing:
                self._phase, self._sequence = "awaiting_relay_header", sequence
                kind, length = await self._header(reader, sequence)
                if kind == relay.EOF:
                    self._phase = "relay_eof"
                    relay.require(not pending, "incomplete native MCP input")
                    await self._send(writer, relay.CLOSED, sequence)
                    self._phase = "closed_by_relay"
                    return
                relay.require(kind == relay.BEGIN, "raw reservation required")
                self._charge("mcp_request", length, int(line_bytes == 0))
                relay.require(line_bytes + length <= relay.MAX_LINE_BYTES, "native MCP line exceeds bound")
                await self._send(writer, relay.RESERVED, sequence)
                self._phase = "reading_request_body"
                data = await reader.readexactly(length)
                relay.require(b"\n" not in data[:-1], "multiple MCP lines in raw chunk")
                end_line = data.endswith(b"\n")
                pending.extend(data)
                line_bytes += length
                output = None
                if end_line:
                    line = bytes(pending)
                    pending.clear()
                    line_bytes = 0
                    self._record.mcp_request(line)
                    self._phase = "handling_request"
                    output = await self._handler(line)
                    self._record.mcp_reply(output)
                relay.require(output is None or (type(output) is bytes and 0 < len(output) <= relay.MAX_LINE_BYTES
                              and output.endswith(b"\n") and b"\n" not in output[:-1]),
                              "invalid native MCP reply")
                if output is not None:
                    self._charge("mcp_reply", len(output), 1)
                payload = output or b""
                self._phase = "sending_reply"
                await self._send(writer, relay.RESULT, sequence, len(payload), payload)
                sequence = relay.next_sequence(sequence)
        except asyncio.CancelledError:
            if not self._closing and not self._stop.requested():
                self._fail("mcp_failure", side="owner")
            raise
        except AgentTrafficExhausted as error:
            self._fail("agent_traffic_exhausted", error=error)
        except (asyncio.IncompleteReadError, ConnectionError, OSError) as error:
            # The relay's end of the socket went away: either the relay itself
            # exited or whatever started it tore the process down.
            self._fail("mcp_failure", error=error, side="relay")
        except (relay.RelayError, ValueError, TypeError) as error:
            self._fail("mcp_failure", error=error)
        except Exception as error:
            self._fail("mcp_failure", error=error)
        finally:
            writer.close()
            try:
                await writer.wait_closed()
            except (ConnectionError, OSError):
                pass
            self._writers.discard(writer)

    async def close_and_join(self):
        if self._close_task is None:
            self._close_task = asyncio.create_task(self._close(), name="agent-mcp-close")
        await joined(self._close_task, on_cancel=self._request_close)

    async def _close(self):
        self._request_close()
        if self._server is not None:
            await self._server.wait_closed()
        tasks = set(self._connections)
        if self._monitor is not None:
            self._monitor.cancel()
            tasks.add(self._monitor)
        if tasks:
            done, pending = await asyncio.wait(tasks, timeout=self._cleanup_timeout)
            failed = any(task.exception() is not None for task in done if not task.cancelled())
            if pending:
                raise CleanupError("C MCP tasks did not join before cleanup deadline")
            if failed:
                raise CleanupError("C MCP task failed during joined cleanup")
        self._collect_relay_diagnostic()
        self._socket_path.unlink(missing_ok=True)

    def _collect_relay_diagnostic(self):
        """Read the relay's own bounded failure line, if it left one behind.

        Only the relay writes this file, and only when it refused or lost its
        own framing, so its presence is what distinguishes a relay that failed
        from a relay that the provider CLI simply killed.
        """
        try:
            text = self._diagnostic_path.read_bytes()[:RELAY_DIAGNOSTIC_BYTES]
        except OSError:
            return
        finally:
            self._diagnostic_path.unlink(missing_ok=True)
        reason = bounded_redacted_diagnostic(text.decode("utf-8", errors="replace").strip(),
                                             RELAY_DIAGNOSTIC_BYTES)
        self._failure_detail["relay_diagnostic"] = reason
        try:
            self._events.emit("relay_diagnostic", {"reason": reason, "phase": self._phase,
                                                   "relay_sequence": self._sequence})
        except Exception:
            pass
