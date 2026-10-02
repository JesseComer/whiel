# Author: Fangzhu Shen
"""Per-input C owner of native agents, authentication and MCP bridge lifetime.

Each request uses a fresh native process. A clean_exit result means a completed
and joined C turn: once B's submission receipt has arrived, the owner may stop
an idle native after a one-second grace. Earlier failures still fail.
"""

import asyncio
import os
from pathlib import Path
import shutil
import sys
import tempfile
import time

from .bwrap import wrap_native_command
from .agent_provenance import native_command_provenance
from .process_tree import OwnedProcess
from .provider_runtime import (
    CliEventCapture, CommandSpec, NativeError, capture_diagnostic, file_hash,
    native_identity_fields, verify_provider,
)
from .providers import claude, codex
from .resource_limits import AgentResourceError, NativeAllowance
from .run_records import ConsultationRecord, DEBUG_FILE, STDERR_BYTES
from .runtime_types import CleanupError, NativeResult
from .stop import AnyStop, Stop, joined
from .token_usage import MODES as USAGE_MODES, USAGE_ENV, RolloutUsage


RECEIPT_GRACE_SECONDS = 1.0
DEFAULT_WRAPPER_SECONDS = 600
DEADLINE_BACKSTOP_SECONDS = 5
# The diagnostic of a turn C stopped at its own deadline. The coordinator reads
# it to complete such a request with the wire's `no_response`, never a transport
# `failure`: the consultation clock ran out with nothing submitted, which is not
# a transport fault and must not be retried as one.
DEADLINE_DIAGNOSTIC = "deadline"


def deadline_seconds(remaining_ns):
    """C's whole-second deadline, never later than the budget B sent.

    Flooring keeps C's own stop at or before B's deadline. Below one second the
    wrapper cannot express a shorter lifetime, and B's deadline governs.
    """
    if remaining_ns is None:
        return None
    return max(1, remaining_ns // 1000000000)


class NativeAgentRuntime:
    def __init__(self, options, budget, events, bridge_factory, *, limits=None):
        self.options = options
        self.budget = budget
        self.events = events
        self.bridge_factory = bridge_factory
        self.allowance = NativeAllowance(limits)
        self.identity = None
        self.root = None
        self.request_number = 0
        self.active = None
        self.shutdown_stop = Stop()
        self.closed = False
        self.cleanup_error = None
        self._bridge_failure_reported = False

    def _scratch(self):
        if self.root is None:
            parent = self.options.scratch_parent.resolve(strict=True)
            self.root = Path(tempfile.mkdtemp(prefix="wa-", dir=parent))
        self.request_number += 1
        request = self.root / f"r{self.request_number}"
        request.mkdir(mode=0o700)
        if len(str(request / "relay.sock").encode()) >= 100:
            raise NativeError("native_setup", "native socket path is too long; choose /tmp as the scratch parent")
        for name in ("logs", "state", "tmp"):
            (request / name).mkdir(mode=0o700)
        return request

    async def run(self, turn):
        if self.cleanup_error is not None:
            raise self.cleanup_error
        if self.closed or self.shutdown_stop.requested():
            raise NativeError("native_closed", "the native runtime is closed")
        if self.active is not None:
            raise NativeError("native_closed", "the native runtime already owns an active turn")
        self.active = asyncio.current_task()
        try:
            return await self._run(turn)
        finally:
            self.active = None

    async def _run(self, turn):
        stop = AnyStop(turn.stop, self.shutdown_stop)
        record = turn.record if turn.record is not None else ConsultationRecord(None)
        deadline = deadline_seconds(turn.remaining_budget_ns)
        child = child_task = bridge = gate = None
        self._bridge_failure_reported = False
        started = None
        capture = None
        debug_file = None
        usage = None
        owner_stopped = deadline_stopped = False
        turn_ended = asyncio.Event()
        result = NativeResult("failed", False, "native_failure")
        try:
            if stop.requested():
                return NativeResult("cancelled", False, await stop.wait())
            self.allowance.checkpoint()
            # This zero charge observes the existing latch; it does not debit
            # the logical prompt (the endpoint coordinator charges that once).
            self.budget.charge("prompt", 0, 0)
            if self.options.isolation == "bwrap" and sys.platform != "linux":
                raise NativeError("isolation", "bubblewrap requires Linux; there is no local fallback")
            if self.identity is None:
                identity = await verify_provider(self.options, stop)
                self.events.emit("native_identity", native_identity_fields(identity))
                self.identity = identity
            scratch = self._scratch()
            usage_mode = os.environ.get(USAGE_ENV, "off")
            if usage_mode not in USAGE_MODES:
                raise NativeError("native_setup", "unsupported token usage mode")
            if usage_mode == "codex-rollout":
                if not isinstance(self.identity, codex.CodexIdentity) or self.options.isolation != "bwrap":
                    raise NativeError("native_setup", "codex-rollout usage requires Codex with bwrap")
                sessions = scratch / "usage-sessions"
                sessions.mkdir(mode=0o700)
                usage = RolloutUsage(sessions, record)
            self.allowance.check_workspace(self.root)
            if isinstance(self.identity, claude.ClaudeIdentity):
                gate = claude.ClaudeStartup(self.identity.model, turn.tool_names)

            async def ready():
                if turn_ended.is_set():
                    raise NativeError("native_closed", "the native turn has ended")
                if stop.requested():
                    raise NativeError(await stop.wait(), "native tool work stopped")
                if gate is not None:
                    await gate.wait()

            bridge = await self.bridge_factory(scratch, turn.make_mcp_handler(ready),
                                               stop, self.budget, self.events)
            files = tuple((path, file_hash(path)) for path in bridge.launch.readonly_resources)
            if Path(bridge.launch.argv[0]).resolve() not in tuple(path.resolve() for path, _ in files):
                raise NativeError("native_setup", "the native relay executable is not one of C's own launch resources")
            self.allowance.checkpoint()
            if any(file_hash(path) != digest for path, digest in files):
                raise NativeError("native_setup", "C's relay files changed before the native launch")
            if stop.requested():
                raise NativeError(await stop.wait(), "native launch stopped")
            if isinstance(self.identity, claude.ClaudeIdentity):
                provider = "claude"
                if record.directory:
                    debug_file = scratch / "logs" / DEBUG_FILE
                limits = self.allowance.limits
                command = claude.launch_command(self.identity, scratch, bridge.launch,
                                                turn.tool_names, isolation=self.options.isolation,
                                                debug_file=debug_file,
                                                thinking_tokens=None if limits is None
                                                else limits.thinking_tokens)
            else:
                provider = "codex"
                command = codex.launch_command(self.identity, scratch, bridge.launch, turn.tool_names,
                                               persist_usage=usage is not None)
            if self.options.isolation == "bwrap":
                seconds = DEFAULT_WRAPPER_SECONDS if deadline is None else deadline
                readonly = (Path(self.identity.executable), *bridge.launch.readonly_resources)
                argv, environment = wrap_native_command(command.argv, command.environment,
                                                        scratch, readonly, seconds,
                                                        provider=provider, persist_usage=usage is not None)
                command = CommandSpec(argv, environment, scratch)
            capture = CliEventCapture(turn.tool_names, gate, sink=record.stdout)
            self.events.emit("native_command", native_command_provenance(
                command.argv, isolation=self.options.isolation))
            started = time.monotonic()
            # Retention keeps the CLI's own stderr too; without it the bounded
            # excerpt beside the exit status is all C needs.
            child = await OwnedProcess.start(command.argv, command.environment, command.cwd,
                                             prompt=turn.prompt, stdout_limit=0,
                                             stderr_limit=STDERR_BYTES if record.directory else 65536,
                                             observer=capture)
            # The owner enforces C's deadline below, with the bridge joined
            # first; the process's own timeout is only a backstop behind it.
            child_task = asyncio.create_task(child.run(
                stop, timeout=None if deadline is None else deadline + DEADLINE_BACKSTOP_SECONDS))
            submitted_at = None
            next_scan = 0.0
            while True:
                if stop.requested():
                    result = NativeResult("cancelled", False, await stop.wait())
                    break
                failure = bridge.failure()
                if failure:
                    # The reason is emitted after joined cleanup, once the relay
                    # has had its chance to leave its own diagnostic behind.
                    result = NativeResult("failed", False, failure)
                    break
                self.budget.charge("prompt", 0, 0)
                now = time.monotonic()
                self.allowance.checkpoint(elapsed=now - started)
                if now >= next_scan:
                    self.allowance.check_workspace(self.root)
                    if usage is not None:
                        usage.poll()
                    next_scan = now + 1
                if deadline is not None and now - started >= deadline and not child_task.done():
                    # C's deadline. Join the relay before signalling the CLI: a
                    # CLI that is told to stop shuts its MCP server down itself,
                    # and a bridge still open at that moment would record the
                    # relay's disappearance as a transport failure and hide the
                    # deadline that actually ended the turn.
                    await bridge.close_and_join()
                    child.request_stop()
                    deadline_stopped = True
                    await joined(child_task)
                    result = NativeResult("failed", False, DEADLINE_DIAGNOSTIC)
                    break
                delivered = turn.submitted()
                if delivered and submitted_at is None:
                    submitted_at = now
                if child_task.done():
                    process = child_task.result()
                    successful = (process.returncode == 0 and not process.capture_failed
                                  and process.prompt_written and (gate is None or gate.verified))
                    result = NativeResult("clean_exit" if successful else "failed",
                                          delivered if successful else False,
                                          None if successful else "native_failure")
                    break
                if submitted_at is not None and now - submitted_at >= RECEIPT_GRACE_SECONDS:
                    # Reap/observe an already-exited failure before requesting
                    # owner termination; stop cannot relabel that failure.
                    if child.exited():
                        await asyncio.sleep(.01)
                        continue
                    # Join C's own relay before signalling the native process:
                    # killing a live relay first would manufacture an unrelated
                    # transport-truncation failure from its EOF.
                    await bridge.close_and_join()
                    child.request_stop()
                    owner_stopped = True
                    process = await joined(child_task)
                    successful = ((process.reason == "cancelled" or process.returncode == 0)
                                  and not process.capture_failed
                                  and process.prompt_written and (gate is None or gate.verified))
                    result = NativeResult("clean_exit" if successful else "failed",
                                          successful, None if successful else "native_failure")
                    break
                await asyncio.sleep(.01)
            if owner_stopped:
                self.events.emit("native_owner_stop", {"receipt_received": True})
            if deadline_stopped:
                self.events.emit("native_deadline", {"seconds": deadline,
                                                     "submission_attempted": bool(turn.submitted())})
        except Exception as error:
            if isinstance(error, CleanupError):
                self.cleanup_error = error
                raise
            code = error.code if isinstance(error, (NativeError, AgentResourceError)) else "native_failure"
            result = NativeResult("failed", False, code)
            try:
                self.events.emit("native_failure", {"code": code})
            except Exception:
                pass  # process/bridge cleanup must still run if the log is full
        finally:
            turn_ended.set()
            process = await joined(asyncio.create_task(
                self._cleanup_turn(child, child_task, bridge, gate, started)))
            if process is not None:
                if process.capture_failed:
                    result = NativeResult("failed", False, "native_failure")
                record.stderr(process.stderr)
                try:
                    self.events.emit("native_capture", {"diagnostic": capture_diagnostic(process, capture),
                                                        "counts": capture.summary()})
                except Exception:
                    result = NativeResult("failed", False, "native_failure")
            if bridge is not None and bridge.failure():
                self._emit_bridge_failure(bridge, capture)
                result = NativeResult("failed", False, bridge.failure())
            try:
                if usage is not None:
                    summary = usage.finish(natural_completion=(result.outcome == "clean_exit"
                        and not owner_stopped and not deadline_stopped and not stop.requested()))
                    self.events.emit("native_usage", summary)
            except Exception:
                pass  # diagnostics cannot change admission or skip record closure
            try:
                if debug_file is not None:
                    record.native_debug(debug_file)
                record.close()
            except Exception:
                pass
        if stop.requested():
            return NativeResult("cancelled", False, await stop.wait())
        return result

    def _emit_bridge_failure(self, bridge, capture):
        """Say why the bridge failed and what the CLI was doing at the time.

        The bridge names the side, the exception and the MCP call in flight; the
        CLI's own last reported event type says whether the turn died during
        startup, during tool use or after its answer. Emitted once per turn.
        """
        if self._bridge_failure_reported:
            return
        self._bridge_failure_reported = True
        detail = getattr(bridge, "failure_detail", None)
        fields = {"code": bridge.failure()}
        if callable(detail):
            fields.update(detail())
        if capture is not None:
            fields.update(cli_last_event=capture.last_event,
                          cli_last_event_subtype=capture.last_event_subtype,
                          cli_stdout_bytes=capture.stdout_bytes,
                          cli_events=dict(capture.events))
        try:
            self.events.emit("native_bridge_failure", fields)
        except Exception:
            pass

    async def _cleanup_turn(self, child, child_task, bridge, gate, started):
        errors = []
        process = None
        try:
            if gate is not None:
                gate.fail("native turn has ended")
            if child_task is not None:
                if not child_task.done():
                    child.request_stop()
                try:
                    process = await child_task
                except BaseException as error:
                    errors.append(error)
            if bridge is not None:
                try:
                    await bridge.close_and_join()
                except BaseException as error:
                    errors.append(error)
        finally:
            if started is not None:
                self.allowance.record_native_time(time.monotonic() - started)
        if errors:
            error = next((error for error in errors if isinstance(error, CleanupError)), errors[0])
            if isinstance(error, CleanupError):
                self.cleanup_error = error
            raise error
        return process

    async def shutdown(self):
        self.shutdown_stop.set("cancelled")
        if self.active is not None and self.active is not asyncio.current_task():
            await joined(self.active)
        if self.cleanup_error is not None:
            raise self.cleanup_error
        if self.root is not None:
            try:
                shutil.rmtree(self.root)
            except OSError as error:
                self.cleanup_error = CleanupError("native scratch cleanup failed")
                raise self.cleanup_error from error
            self.root = None
        self.closed = True
