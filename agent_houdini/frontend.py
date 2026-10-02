# Author: Fangzhu Shen
"""Python endpoint coordinator: present B observations and own native turns.

B supplies immutable snapshots and read-only query access. All prompt, tool,
skill, native-session and transport choices here belong to C. This module does
not implement invariant checking, Houdini updates or certificate publication.
"""

import asyncio
import os
from pathlib import Path
import signal
import sys
import threading

from .agent_runtime import DEADLINE_DIAGNOSTIC
from .agent_transport import AgentTrafficExhausted, McpTransport, MeteredRequestAccess
from .agent_provenance import prompt_provenance
from .bwrap import python_relay_resources
from .json_wire import decode
from .mcp_client import McpClient
from .prompt import render_prompt
from .protocol import ApiClient, ProtocolError, RequestRevoked, ShutdownEvent
from .resource_limits import AgentResourceError
from .run_records import null_records
from .runtime_types import CleanupError, NativeTurn
from .stop import AnyStop, Stop, joined
from .skills import SKILLS_FILE_ENV, SkillCatalog
from .submission_check import push_checks
from .tool_catalog import default_catalog


class _LocalInterrupted(Exception):
    pass


class _Signals:
    """The standalone C endpoint owns its signals; restore the caller on return."""

    def __init__(self, stop):
        self.previous = {}
        if threading.current_thread() is not threading.main_thread():
            return
        loop = asyncio.get_running_loop()
        for signum in (signal.SIGINT, signal.SIGTERM):
            self.previous[signum] = signal.getsignal(signum)
            def handle(received, _frame):
                loop.call_soon_threadsafe(stop.set, "cancelled", 128 + received)
            signal.signal(signum, handle)

    def restore(self):
        for signum, handler in self.previous.items():
            signal.signal(signum, handler)


async def _interruptible(operation, stop):
    work = asyncio.create_task(operation)
    stopped = asyncio.create_task(stop.wait())
    try:
        await asyncio.wait((work, stopped), return_when=asyncio.FIRST_COMPLETED)
        if stop.requested():
            work.cancel()
            await asyncio.gather(work, return_exceptions=True)
            raise _LocalInterrupted
        return await work
    finally:
        if not work.done():
            work.cancel()
        stopped.cancel()
        await asyncio.gather(work, stopped, return_exceptions=True)


def _is_resource_failure(code):
    return code in ("agent_traffic_exhausted", "agent_native_time_exhausted",
                    "agent_workspace_exhausted")


def _safe_event(events, kind, fields):
    try:
        events.emit(kind, fields)
    except Exception:
        pass


def task_identity(observation_bytes):
    """The canonical id of the task a push names, or None.

    A C-local read of `feedback.presentation.task.canonical_id`, used only to
    name this input's log directory; it decides nothing about the request,
    and any malformed push simply leaves the directory unnamed.
    """
    try:
        snapshot = decode(observation_bytes)
    except Exception:
        return None
    feedback = snapshot.get("feedback") if isinstance(snapshot, dict) else None
    presentation = feedback.get("presentation") if isinstance(feedback, dict) else None
    task = presentation.get("task") if isinstance(presentation, dict) else None
    identity = task.get("canonical_id") if isinstance(task, dict) else None
    return identity if isinstance(identity, str) and identity else None


async def _cleanup(runner, client):
    failure = None
    if runner is not None:
        try:
            await runner.shutdown()
        except BaseException as error:
            failure = error
    if client is not None:
        try:
            await client.close()
        except BaseException as error:
            failure = failure or error
    if failure is not None:
        raise CleanupError("C endpoint cleanup failed") from failure


# A provider CLI that cannot run at all -- a bad install, an expired login, a
# refused configuration, a provider outage -- fails every consultation in
# milliseconds, and the verifier reopens a failed consultation at once. Left
# alone that is thousands of launches per input until the search limit. After
# this many consecutive native failures with nothing submitted, the endpoint
# stops serving the input instead: it closes its connection without completing
# the open request, which the verifier reads as the endpoint having exited and
# ends the input at once. The next input starts a fresh endpoint and tries again.
CONSECUTIVE_NATIVE_FAILURE_LIMIT = 3
NATIVE_FAILURE_DIAGNOSTICS = ("native_failure", "endpoint_failure")


async def run_endpoint(options, budget, events, *, runner_factory, environment=None,
                       records=None):
    """Serve one B input; return 0, failure 1, or joined local signal status.

    The process-free factory receives (options, budget, events, bridge_factory).
    The caller owns the event sink and configuration; this function owns native
    endpoint shutdown, API I/O and endpoint signal handling. It never installs
    providers or changes B options. Per-input C resource failure remains latched:
    later requests receive source_exhausted without launching more native work.
    """
    environment = dict(os.environ if environment is None else environment)
    # Retention is C's own policy. Without it these records keep only the
    # metadata a failure reason needs and write nothing to disk.
    records = null_records() if records is None else records
    local_stop = Stop()
    signals = _Signals(local_stop)
    client = runner = None
    active = None
    record = None
    exhausted = None
    native_failures = 0
    status = 1
    runner_closed = False
    externally_cancelled = False
    cleanup_failed = False
    identified = False

    async def make_bridge(work, handler, stop, native_budget, native_events):
        if active is None or record is None:
            raise RuntimeError("native bridge lacks an active request")
        interpreter, path = Path(sys.executable), Path(__file__).with_name("mcp_stdio.py")
        if options.isolation == "bwrap":
            interpreter, path = python_relay_resources(Path("/usr/bin/python3"), path)
        return await McpTransport.create(
            work, handler, stop, native_budget, native_events,
            interpreter=interpreter, relay_path=path, record=record)

    async def acknowledge_shutdown():
        nonlocal runner_closed
        if not runner_closed:
            await runner.shutdown()
            runner_closed = True
        await client.closed()

    try:
        client = await _interruptible(ApiClient.from_environment(environment), local_stop)
        runner = runner_factory(options, budget, events, make_bridge)
        from .provider_runtime import redacted_selection

        events.emit("endpoint_started", {
            "provider_configuration": redacted_selection(decode(options.selection_json)),
            "isolation": options.isolation, "traffic_accounting": "logical_payloads_v1"})
        while True:
            event = await _interruptible(client.next_event(), local_stop)
            if isinstance(event, ShutdownEvent):
                await acknowledge_shutdown()
                status = 0
                break
            metered = MeteredRequestAccess(event.access, budget)
            active = metered
            if not identified:
                # The first push names the input this endpoint serves; the log
                # directory takes that name before any consultation is retained
                # under it, so every request-N lands under the named directory.
                identity = task_identity(event.access.view.observation)
                if identity is not None:
                    identified = True
                    _safe_event(events, "input_identified", {
                        "request_id": event.access.view.request_id, "canonical_id": identity,
                        "directory": records.identify(identity)})
            record = records.consultation(event.access.view.request_id)
            stop = AnyStop(event.stop, local_stop)
            outcome, diagnostic, retained = "failure", None, {}
            try:
                if exhausted is not None:
                    outcome, diagnostic = "source_exhausted", exhausted
                else:
                    snapshot = decode(event.access.view.observation)
                    if not isinstance(snapshot, dict):
                        raise ValueError("observation must be an object")
                    skill_path = environment.get(SKILLS_FILE_ENV)
                    skills = SkillCatalog() if skill_path is None else SkillCatalog.from_path(skill_path)
                    catalog = default_catalog().with_skills(skills)
                    tools = catalog.tools_for_policy(event.access.query_names)
                    prompt = render_prompt(snapshot, event.access.view.response_example,
                                           tools=tools, skills=skills)
                    budget.charge("prompt", len(prompt), 1)
                    record.prompt(prompt)
                    events.emit("request_started", {"request_id": event.access.view.request_id,
                                                    **prompt_provenance(prompt),
                                                    "tool_names": catalog.inventory(event.access.query_names)})
                    clients = []
                    checks = push_checks(event.access.view.response_example, snapshot)
                    def make_handler(ready):
                        mcp = McpClient(catalog, event.access.query_names, metered,
                                        native_ready=ready, checks=checks)
                        clients.append(mcp)
                        return mcp.line
                    # C's own native deadline comes from the request budget B
                    # sent on the wire, never from the observation body.
                    turn = NativeTurn(prompt, tuple(catalog.inventory(event.access.query_names)),
                                      make_handler, stop, lambda: metered.receipt_received,
                                      event.access.view.remaining_budget_ns, record)
                    result = await runner.run(turn)
                    # Refusals the coordinator returned to the agent, named in
                    # C's log only: the agent's own reply stays the bare code.
                    for reason in [text for mcp in clients for text in mcp.rejections][:16]:
                        _safe_event(events, "mcp_rejection",
                                    {"request_id": event.access.view.request_id,
                                     "reason": reason})
                    diagnostic = result.diagnostic_code
                    if _is_resource_failure(diagnostic):
                        exhausted = diagnostic
                        outcome = "failure" if metered.submission_attempted else "source_exhausted"
                    elif stop.requested():
                        outcome = "failure"
                    elif result.outcome == "clean_exit":
                        if result.submission_delivered and metered.receipt_received:
                            outcome = "response"
                        elif not metered.submission_attempted and not result.submission_delivered:
                            outcome = "no_response"
                    elif (diagnostic == DEADLINE_DIAGNOSTIC
                          and not metered.submission_attempted
                          and not result.submission_delivered):
                        # C's own deadline expired with nothing submitted. That
                        # is the wire's explicit "finished without a
                        # submission", not a transport fault; completing it as
                        # `failure` would have B record a transport failure and
                        # retry the turn its own clock was about to end.
                        outcome = "no_response"
            except (AgentResourceError, AgentTrafficExhausted) as error:
                exhausted = getattr(error, "code", "agent_traffic_exhausted")
                diagnostic = exhausted
                outcome = "failure" if metered.submission_attempted else "source_exhausted"
            except CleanupError:
                raise
            except Exception:
                diagnostic = "endpoint_failure"
                outcome = "failure"
            finally:
                active = None
                try:
                    retained = record.close()
                except Exception:
                    retained = {}
                record = None
            if local_stop.requested():
                raise _LocalInterrupted
            if client.shutdown_reason is not None:
                await acknowledge_shutdown()
                status = 0
                break
            # Authoritative cancellation always uses failure, even if a C
            # resource allowance also latched while the request was stopping.
            if event.stop.requested():
                outcome = "failure"
            events.emit("request_outcome", {"request_id": event.access.view.request_id,
                                            "outcome": outcome, "diagnostic_code": diagnostic,
                                            **retained})
            if (outcome == "failure" and diagnostic in NATIVE_FAILURE_DIAGNOSTICS
                    and not metered.submission_attempted):
                native_failures += 1
            else:
                native_failures = 0
            if native_failures >= CONSECUTIVE_NATIVE_FAILURE_LIMIT:
                _safe_event(events, "provider_unusable", {
                    "request_id": event.access.view.request_id,
                    "consecutive_native_failures": native_failures,
                    "diagnostic_code": diagnostic})
                print(f"agent_houdini: the provider CLI failed {native_failures} consultations in "
                      f"a row with nothing submitted ({diagnostic}); ending this input. Its own "
                      f"error output is in the consultation's native-stderr.txt.",
                      file=sys.stderr, flush=True)
                status = 1
                break
            try:
                await _interruptible(client.complete(event.access, outcome), local_stop)
            except (ProtocolError, RequestRevoked):
                if client.shutdown_reason is None:
                    raise
                await acknowledge_shutdown()
                status = 0
                break
    except _LocalInterrupted:
        status = local_stop.exit_status or 1
    except asyncio.CancelledError:
        local_stop.set("cancelled")
        externally_cancelled = True
    except Exception:
        _safe_event(events, "endpoint_failure", {})
        status = 1
    finally:
        try:
            await joined(asyncio.create_task(_cleanup(None if runner_closed else runner, client)))
        except CleanupError:
            _safe_event(events, "endpoint_cleanup_failure", {})
            cleanup_failed = True
            status = 1
        finally:
            signals.restore()
        usage = getattr(budget, "usage", None)
        if callable(usage):
            _safe_event(events, "agent_traffic", usage())
    if externally_cancelled and not cleanup_failed:
        raise asyncio.CancelledError
    return status
