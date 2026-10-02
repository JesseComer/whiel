# Author: Fangzhu Shen
"""C-owned campaign configuration and public verifier command construction.

The first `--` separates C options from opaque B campaign arguments. Only B's
three endpoint-selection flags are reserved; its other options are interpreted
by the public verifier, without a second option registry in C.
"""
from __future__ import annotations

import argparse
import asyncio
from collections.abc import Sequence
from dataclasses import asdict, dataclass, field
import os
from pathlib import Path
import signal
import sys
import tempfile

from .agent_log import AgentLog, bounded_redacted_diagnostic
from .json_wire import decode, encode
from .provider_config import MAX_CONFIGURATION_BYTES, validate_selection
from .resource_limits import AgentLimits, AgentTrafficBudget
from .run_records import RETENTION_MODES, RunRecords
from .runtime_types import NativeOptions
from .stop import Stop


@dataclass(frozen=True, slots=True)
class CampaignOptions:
    verifier: Path
    verifier_arguments: tuple[str, ...]
    native: NativeOptions | None
    limits: AgentLimits = field(default_factory=AgentLimits)
    log_parent: Path | None = None
    retention: str = "events"
    # An exact, fresh directory for this campaign's C logs, the alternative to
    # a parent under which a temporary name is made.
    log_dir: Path | None = None


@dataclass(frozen=True, slots=True)
class EndpointOptions:
    native: NativeOptions
    limits: AgentLimits = field(default_factory=AgentLimits)
    log_parent: Path | None = None
    retention: str = "events"


def native_options(
    provider: str = "codex", *, model: str | None = None,
    reasoning_effort: str | None = None, executable: str | None = None,
    isolation: str | None = None, scratch_parent: Path | None = None,
) -> NativeOptions | None:
    """Validate C choices without probes, installation or output creation."""
    if provider == "none":
        if any(value is not None for value in
               (model, reasoning_effort, executable, isolation, scratch_parent)):
            raise ValueError("no-proposer mode is incompatible with native options")
        return None
    selection = validate_selection(provider, model, reasoning_effort, executable)
    isolation = "local" if isolation is None else isolation
    if isolation not in ("local", "bwrap"):
        raise ValueError("isolation must be local or bwrap; no fallback is used")
    if selection["executable"] is not None:
        selection["executable"] = str(Path(selection["executable"]).absolute())
    scratch = Path(tempfile.gettempdir()) if scratch_parent is None else scratch_parent
    return NativeOptions(encode(selection, maximum=MAX_CONFIGURATION_BYTES),
                         isolation, scratch.resolve())


def _argument(value: str) -> None:
    if not isinstance(value, str) or "\0" in value:
        raise ValueError("command arguments must be strings without NUL")
    try:
        value.encode("utf-8")
    except UnicodeError as error:
        raise ValueError("command arguments must be valid UTF-8") from error


def _verifier_arguments(arguments: Sequence[str]) -> tuple[str, ...]:
    reserved = {"--proposer-executable", "--proposer-arg", "--no-proposer"}
    for argument in arguments:
        _argument(argument)
        if argument.partition("=")[0] in reserved:
            raise ValueError("C selects the proposer endpoint; conflicting B endpoint option")
    return tuple(arguments)


def _native_arguments(parser, *, endpoint=False):
    provider = parser.add_mutually_exclusive_group()
    provider.add_argument("--provider", choices=("codex", "claude") if endpoint else
                          ("codex", "claude", "none"), default="codex")
    if not endpoint:
        provider.add_argument("--no-proposer", dest="provider", action="store_const", const="none",
                             help="explicit no-model diagnostic; skip native setup")
    parser.add_argument("--model", help="provider model string, passed through verbatim")
    parser.add_argument("--reasoning-effort", help="optional provider effort string, passed through verbatim")
    parser.add_argument("--provider-cli", help="explicit provider CLI path; otherwise PATH is resolved")
    parser.add_argument("--isolation", choices=("local", "bwrap"))
    parser.add_argument("--agent-scratch-parent", type=Path)
    defaults = AgentLimits()
    for name, value in asdict(defaults).items():
        parser.add_argument("--agent-" + name.replace("_", "-"), dest=name,
                            type=float if name == "native_seconds" else int,
                            help=f"C-owned allowance (default: {value})")
    parser.add_argument("--agent-log-parent", type=Path, help="existing parent for fresh private C logs")
    if not endpoint:
        parser.add_argument("--agent-log-dir", type=Path,
                            help="fresh directory for this campaign's C logs, created by the launcher; "
                                 "the alternative to --agent-log-parent (its parent must exist)")
    parser.add_argument("--agent-retention", choices=RETENTION_MODES, default="events",
                        help="C diagnostics retained per consultation (default: events); "
                             "all also keeps the prompt, the CLI stream, MCP traffic and submissions")


def _options(parsed):
    native = native_options(parsed.provider, model=parsed.model,
                            reasoning_effort=parsed.reasoning_effort,
                            executable=parsed.provider_cli, isolation=parsed.isolation,
                            scratch_parent=parsed.agent_scratch_parent)
    limits = AgentLimits(**{name: getattr(parsed, name) if getattr(parsed, name) is not None else value
                            for name, value in asdict(AgentLimits()).items()})
    if native is None and (parsed.agent_log_parent is not None
                           or any(getattr(parsed, name) is not None for name in asdict(limits))):
        raise ValueError("no-proposer mode is incompatible with agent limits or logs")
    retention = getattr(parsed, "agent_retention", "events")
    if native is None and retention != "events":
        raise ValueError("no-proposer mode is incompatible with agent limits or logs")
    log_dir = getattr(parsed, "agent_log_dir", None)
    if log_dir is not None:
        if native is None:
            raise ValueError("no-proposer mode is incompatible with agent limits or logs")
        if parsed.agent_log_parent is not None:
            raise ValueError("choose --agent-log-dir or --agent-log-parent, not both")
        _argument(str(log_dir))
        log_dir = log_dir.absolute()
    parent = parsed.agent_log_parent.resolve() if parsed.agent_log_parent is not None else None
    return native, limits, parent, retention, log_dir


def parse_campaign_arguments(argv: Sequence[str]) -> CampaignOptions:
    """Parse the portion after `campaign run`; B options follow the first `--`."""
    arguments = list(argv)
    delimiter = arguments.index("--") if "--" in arguments else len(arguments)
    own, verifier = arguments[:delimiter], arguments[delimiter + 1:]
    parser = argparse.ArgumentParser(
        prog="python -m agent_houdini campaign run", allow_abbrev=False,
        description="Run the Python proposer with B's public campaign command.",
        epilog="Place B campaign options after --, for example: -- --input 1 --repo /checkout.")
    parser.add_argument("--verifier", required=True, type=Path,
                        help="public whiel-symbolic executable")
    _native_arguments(parser)
    parsed = parser.parse_args(own)
    try:
        native, limits, log_parent, retention, log_dir = _options(parsed)
        verifier_arguments = _verifier_arguments(verifier)
        _argument(str(parsed.verifier))
        return CampaignOptions(parsed.verifier.absolute(), verifier_arguments, native,
                               limits, log_parent, retention, log_dir)
    except ValueError as error:
        parser.error(str(error))


def build_verifier_command(options: CampaignOptions,
                           endpoint_argv: tuple[str, ...]) -> tuple[str, ...]:
    """Forward opaque argv to the public CLI; never quote or split shell text.

    Endpoint construction is injected by the C entry point. Passing an absolute
    executable is necessary because B starts it in a private working directory.
    """
    _argument(str(options.verifier))
    if not options.verifier.is_absolute():
        raise ValueError("public verifier executable must be absolute")
    command = (str(options.verifier), "campaign", "run",
               *_verifier_arguments(options.verifier_arguments))
    if options.native is None:
        if endpoint_argv:
            raise ValueError("no-proposer mode cannot supply an endpoint")
        return (*command, "--no-proposer")
    if not endpoint_argv or not Path(endpoint_argv[0]).is_absolute():
        raise ValueError("proposer endpoint executable must be absolute")
    for argument in endpoint_argv:
        _argument(argument)
    result = [*command, "--proposer-executable", endpoint_argv[0]]
    for argument in endpoint_argv[1:]:
        result.extend(("--proposer-arg", argument))
    return tuple(result)


def parse_endpoint_arguments(argv: Sequence[str]) -> EndpointOptions:
    parser = argparse.ArgumentParser(prog="python -m agent_houdini endpoint", allow_abbrev=False)
    _native_arguments(parser, endpoint=True)
    try:
        native, limits, log_parent, retention, _ = _options(parser.parse_args(argv))
        return EndpointOptions(native, limits, log_parent, retention)
    except ValueError as error:
        parser.error(str(error))


def build_endpoint_command(options: EndpointOptions) -> tuple[str, ...]:
    selected = decode(options.native.selection_json, maximum=MAX_CONFIGURATION_BYTES)
    # A direct C entry path is independent of B's private working directory.
    result = [str(Path(sys.executable).resolve()), str(Path(__file__).with_name("__main__.py").resolve()),
              "endpoint", "--provider", selected["provider"], "--model", selected["model"],
              "--isolation", options.native.isolation,
              "--agent-scratch-parent", str(options.native.scratch_parent)]
    if selected["reasoning_effort"] is not None:
        result.extend(("--reasoning-effort", selected["reasoning_effort"]))
    if selected["executable"] is not None:
        result.extend(("--provider-cli", selected["executable"]))
    for name, value in asdict(options.limits).items():
        if value is not None:
            result.extend(("--agent-" + name.replace("_", "-"), str(value)))
    if options.log_parent is not None:
        result.extend(("--agent-log-parent", str(options.log_parent)))
    if options.retention != "events":
        result.extend(("--agent-retention", options.retention))
    return tuple(result)


class _LaunchStopped(Exception):
    def __init__(self, status):
        self.status = status


async def _verify_for_launch(native, verify):
    from .provider_runtime import NativeError

    stop = Stop()
    loop = asyncio.get_running_loop()
    previous = {number: signal.getsignal(number) for number in (signal.SIGINT, signal.SIGTERM)}
    try:
        for number, reason in ((signal.SIGINT, "interrupted"), (signal.SIGTERM, "terminated")):
            loop.add_signal_handler(number, stop.set, reason)
        try:
            identity = await verify(native, stop)
        except NativeError as error:
            if not stop.requested() or error.code != stop.reason:
                raise
        if stop.requested():
            raise _LaunchStopped(130 if stop.reason == "interrupted" else 143)
        return identity
    finally:
        for number, handler in previous.items():
            loop.remove_signal_handler(number)
            signal.signal(number, handler)


def _log_directory(native, parent, prefix):
    parent = native.scratch_parent if parent is None else parent
    return Path(tempfile.mkdtemp(prefix=prefix, dir=parent.resolve(strict=True)))


def _check_fresh_log_directory(path):
    """The exact log directory must not exist yet, under a parent that does."""
    if not path.parent.is_dir():
        raise ValueError("the parent of the agent log directory must be an existing directory")
    if path.exists() or path.is_symlink():
        raise ValueError("agent log directory already exists; choose a fresh one")


def _fresh_log_directory(path):
    _check_fresh_log_directory(path)
    try:
        os.mkdir(path, 0o700)
    except FileExistsError as error:
        raise ValueError("agent log directory already exists; choose a fresh one") from error
    return path.resolve(strict=True)


async def endpoint_main(options: EndpointOptions, *, run_endpoint=None,
                        runner_factory=None, log_factory=AgentLog) -> int:
    if run_endpoint is None:
        from .frontend import run_endpoint
    if runner_factory is None:
        from .agent_runtime import NativeAgentRuntime

        def runner_factory(native, budget, events, bridge_factory):
            return NativeAgentRuntime(native, budget, events, bridge_factory, limits=options.limits)

    from .provider_runtime import redacted_selection

    directory = _log_directory(options.native, options.log_parent, "input-")
    with log_factory(directory / "events.jsonl") as events:
        events.emit("endpoint_configuration", {
            "selection": redacted_selection(decode(options.native.selection_json)),
            "isolation": options.native.isolation,
            "agent_limits": asdict(options.limits), "retention": options.retention})
        budget = AgentTrafficBudget(options.limits)
        return await run_endpoint(options.native, budget, events, runner_factory=runner_factory,
                                  records=RunRecords(directory, options.retention))


def main(argv: Sequence[str] | None = None, *, verify=None, execute=None,
         endpoint_runner=None) -> int:
    arguments = list(sys.argv[1:] if argv is None else argv)
    try:
        if arguments in ([], ["-h"], ["--help"]):
            print("Usage: python -m agent_houdini {campaign run|endpoint|experiment|render-prompt|"
                  "show-run|export-run|export-transcript|compare-runs} [OPTIONS]\n"
                  "Campaign C options precede --; public B campaign options follow it.\n"
                  "experiment run SPEC.json starts a campaign from a spec file into one run directory;\n"
                  "experiment pool SPEC.json runs independent single-input campaigns with GNU Parallel;\n"
                  "experiment report RUN_DIR rewrites that directory's readable digest.\n"
                  "render-prompt PATH prints, offline, what the agent reads for a recorded push.\n"
                  "show-run DIR prints, offline, a per-consultation summary of a recorded run.\n"
                  "export-run RUN_DIR DEST copies a run directory for a collaborator, without the "
                  "raw provider streams, and refuses output carrying this machine's own layout; "
                  "export-run --check-only RUN_DIR reports the same check in place.\n"
                  "export-transcript RUN_DIR OUT.json freezes a run's transcript into one small "
                  "file: no paths, prompts, provider streams or solver output, for a collaborator "
                  "to replay and for compare-runs to check a replay against.\n"
                  "compare-runs ORIGINAL REPLAY reports three named replay fidelity checks between "
                  "an original run (or its export-transcript file) and a replay of it.")
            return 0
        if arguments[0] == "experiment":
            from .experiment import main as experiment_main

            return experiment_main(arguments[1:])
        if arguments[0] == "show-run":
            from .show_run import main as show_main

            return show_main(arguments[1:])
        if arguments[0] == "render-prompt":
            from .render import main as render_main

            return render_main(arguments[1:])
        if arguments[0] == "export-run":
            from .export_run import main as export_main

            return export_main(arguments[1:])
        if arguments[0] == "export-transcript":
            from .export_transcript import main as export_transcript_main

            return export_transcript_main(arguments[1:])
        if arguments[0] == "compare-runs":
            from .compare_runs import main as compare_runs_main

            return compare_runs_main(arguments[1:])
        if arguments[0] == "endpoint":
            options = parse_endpoint_arguments(arguments[1:])
            return asyncio.run((endpoint_runner or endpoint_main)(options))
        if arguments[:2] != ["campaign", "run"]:
            raise ValueError("expected campaign run, endpoint, experiment, render-prompt, "
                            "show-run, export-run, export-transcript or compare-runs; see --help")
        options = parse_campaign_arguments(arguments[2:])
        if not options.verifier.is_file() or not os.access(options.verifier, os.X_OK):
            raise ValueError("public verifier executable must be an existing executable file")
        endpoint = ()
        if options.native is not None:
            log_parent = options.log_parent
            if not any(argument in ("-h", "--help") for argument in options.verifier_arguments):
                if options.native.isolation == "bwrap" and sys.platform != "linux":
                    raise ValueError("bubblewrap requires Linux; no local fallback")
                if not options.native.scratch_parent.is_dir():
                    raise ValueError("agent scratch parent must be an existing directory")
                if log_parent is not None and not log_parent.is_dir():
                    raise ValueError("agent log parent must be an existing directory")
                if options.log_dir is not None:
                    _check_fresh_log_directory(options.log_dir)
                if verify is None:
                    from .provider_runtime import verify_provider
                    verify = verify_provider
                from .provider_runtime import native_identity_fields, redacted_selection
                identity = asyncio.run(_verify_for_launch(options.native, verify))
                if options.log_dir is not None:
                    log_parent = _fresh_log_directory(options.log_dir)
                else:
                    log_parent = _log_directory(options.native, options.log_parent, "whiel-agent-")
                with AgentLog(log_parent / "launcher.jsonl") as events:
                    events.emit("launcher_configuration", {
                        "selection": redacted_selection(decode(options.native.selection_json)),
                        "isolation": options.native.isolation,
                        "agent_limits": asdict(options.limits), "retention": options.retention,
                        "native_identity": native_identity_fields(identity)})
                print(f"agent_houdini logs: {log_parent}", file=sys.stderr)
            endpoint = build_endpoint_command(
                EndpointOptions(options.native, options.limits, log_parent, options.retention))
        command = build_verifier_command(options, endpoint)
        # Replacement leaves B in direct ownership of its own signals/lifecycle.
        return (execute or os.execv)(command[0], command)
    except _LaunchStopped as error:
        return error.status
    except SystemExit as error:
        return int(error.code)
    except KeyboardInterrupt:
        # Outside a running owner, there is no native work to join. asyncio.run
        # also joins a cancelled owner before propagating its KeyboardInterrupt.
        return 130
    except (OSError, ValueError, RuntimeError) as error:
        print("agent_houdini: " + bounded_redacted_diagnostic(str(error)), file=sys.stderr)
        return 2
