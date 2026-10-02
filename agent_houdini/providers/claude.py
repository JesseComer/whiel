# Author: Fangzhu Shen
"""Native Claude launch construction, restricted argv and MCP startup gate."""

import asyncio
from dataclasses import dataclass
import os
from pathlib import Path
import shutil

from ..agent_log import bounded_redacted_diagnostic
from ..json_wire import JsonWireError, encode
from ..provider_runtime import CommandSpec, NativeError, UNKNOWN_VERSION, probe_version


# USER is required on macOS: without it the CLI cannot open the login keychain
# that stores its claude.ai credentials and reports "Not logged in".
ENVIRONMENT = ("HOME", "USER", "CLAUDE_CONFIG_DIR", "PATH", "LANG", "SSL_CERT_FILE", "SSL_CERT_DIR",
               "HTTPS_PROXY", "HTTP_PROXY", "NO_PROXY")
DISABLED_ENVIRONMENT = {
    "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC": "1", "CLAUDE_CODE_DISABLE_CLAUDE_MDS": "1",
    "CLAUDE_CODE_DISABLE_ATTACHMENTS": "1", "CLAUDE_CODE_DISABLE_AUTO_MEMORY": "1",
    "CLAUDE_CODE_DISABLE_OFFICIAL_MARKETPLACE_AUTOINSTALL": "1", "CLAUDE_CODE_DISABLE_GIT_INSTRUCTIONS": "1",
    "ENABLE_CLAUDEAI_MCP_SERVERS": "false", "ENABLE_TOOL_SEARCH": "false",
}


def native_environment(environ=None):
    source = os.environ if environ is None else environ
    return {**{name: source[name] for name in ENVIRONMENT if name in source}, **DISABLED_ENVIRONMENT}


def configuration_directory(environ=None):
    source = os.environ if environ is None else environ
    value = source.get("CLAUDE_CONFIG_DIR")
    if value is None and "HOME" in source:
        value = str(Path(source["HOME"]) / ".claude")
    if value is None or not Path(value).is_absolute():
        raise NativeError("native_setup", "native Claude needs an absolute HOME or CLAUDE_CONFIG_DIR")
    return Path(value)


@dataclass(frozen=True, slots=True)
class ClaudeIdentity:
    """Provenance of one selected CLI; no version, hash or profile requirement."""

    executable: str
    model: str
    reasoning_effort: str | None = None
    configuration_directory: Path | None = None
    version: str = UNKNOWN_VERSION
    schema_version: int = 1
    provider: str = "claude"


async def verify(model, effort, executable=None, stop=None):
    """Select the CLI from an explicit path or PATH and record what it reports."""
    configuration = configuration_directory()
    selected = executable or shutil.which("claude")
    if selected is None:
        raise NativeError("native_setup",
                          "install the native Claude Code CLI on PATH, or pass an explicit path")
    path = Path(selected).resolve(strict=True)
    if not path.is_file():
        raise NativeError("native_setup", "the selected Claude executable is not a file")
    version = await probe_version(path, native_environment(), stop)
    return ClaudeIdentity(str(path), model, effort, configuration, version)


def launch_command(identity, scratch, transport, tool_names, *, isolation="local", environ=None,
                   debug_file=None, thinking_tokens=None):
    # Under bwrap the same argv runs inside the wrapper's Claude profile, which
    # owns the confined home layout, login mounts and child environment.
    if isolation not in ("local", "bwrap"):
        raise NativeError("isolation", "unsupported native isolation; no fallback")
    names = tuple(tool_names)
    if not transport.argv or not Path(transport.argv[0]).is_absolute():
        raise NativeError("native_setup", "the native relay command must be an absolute path")
    allowed = ",".join("mcp__whiel__" + name for name in names)
    settings = {"disableAllHooks": True, "disableClaudeAiConnectors": True, "disableBundledSkills": True,
                "disableWorkflows": True, "autoMemoryEnabled": False, "fallbackModel": [],
                "switchModelsOnFlag": False, "ultracode": False}
    mcp = {"mcpServers": {"whiel": {"type": "stdio", "command": transport.argv[0],
                                   "args": list(transport.argv[1:]), "env": dict(transport.environment)}}}
    args = [identity.executable, "-p", "--restricted", "--tools", "", "--strict-mcp-config",
            "--mcp-config", encode(mcp).decode(), "--allowedTools", allowed, "--permission-mode", "dontAsk",
            "--setting-sources", "", "--settings", encode(settings).decode(), "--disable-slash-commands",
            "--no-session-persistence", "--output-format", "stream-json", "--verbose",
            "--model", identity.model]
    if identity.reasoning_effort is not None:
        args.extend(("--effort", identity.reasoning_effort))
    if thinking_tokens is not None:
        # A C agent allowance, not a model setting: a turn that thinks past its
        # consultation budget never reaches a tool call, so the owner may cap
        # the thinking the CLI lets the model spend before it must act.
        args.extend(("--max-thinking-tokens", str(int(thinking_tokens))))
    if debug_file is not None:
        # The CLI's own debug log, written inside C's scratch and retained only
        # when the owner asked for retention: it is the one place the CLI says
        # what it did to its MCP server between the stream events.
        args.extend(("--debug-file", str(debug_file)))
    environment = native_environment(environ)
    # Do not force CLAUDE_CONFIG_DIR: when it is set, the CLI reads its account
    # file from that directory instead of ~/.claude.json and reports "Not logged
    # in" for a keychain login. It is passed through only when the user set it.
    environment.update(TMPDIR=str(scratch / "tmp"))
    return CommandSpec(tuple(args), environment, scratch)


STARTUP_DIAGNOSTIC_BYTES = 8 * 1024
STARTUP_EXCERPT_ITEMS = 64
PROVIDER_ERROR_LIMIT = 4
PROVIDER_ERROR_BYTES = 512


def placeholder_model(value):
    """A CLI writes a bracketed placeholder where a message had no completion.

    This is a syntactic test on the reported field, not a table of models: any
    `<...>` marker means the CLI generated that message itself.
    """
    return type(value) is str and value.startswith("<") and value.endswith(">")


def provider_error_text(value):
    """The CLI's own error text for a message it generated instead of output."""
    message = value.get("message")
    parts = []
    if isinstance(message, dict) and isinstance(message.get("content"), list):
        parts = [item["text"] for item in message["content"][:PROVIDER_ERROR_LIMIT]
                 if isinstance(item, dict) and type(item.get("text")) is str]
    label = value.get("error")
    text = ((label + ": ") if type(label) is str and label else "") + " ".join(parts)
    return bounded_redacted_diagnostic(text.strip() or "provider error without text",
                                       PROVIDER_ERROR_BYTES)


def _scalar(value):
    """One JSON-safe, bounded rendering of a reported field."""
    if value is None or type(value) in (bool, int, str):
        return value
    if type(value) is float:
        return repr(value)
    if type(value) is list:
        return [_scalar(item) for item in value[:STARTUP_EXCERPT_ITEMS]]
    if type(value) is dict:
        return {str(key): _scalar(item) for key, item in tuple(value.items())[:STARTUP_EXCERPT_ITEMS]}
    return type(value).__name__


def startup_excerpt(value):
    """Only the fields the startup gate compares.

    The excerpt exists to explain a refusal, so it carries the reported model,
    permission mode, MCP server entries, the `mcp__` tool names and the error
    fields. It never carries the launch argv, the environment, the relay socket
    or token, the session identity or any conversation content.
    """
    tools = value.get("tools")
    known = [name for name in tools if type(name) is str] if type(tools) is list else []
    excerpt = {"type": _scalar(value.get("type")), "subtype": _scalar(value.get("subtype")),
               "model": _scalar(value.get("model")),
               "permissionMode": _scalar(value.get("permissionMode")),
               "mcp_servers": _scalar(value.get("mcp_servers")),
               "mcp_tools": sorted(name for name in known if name.startswith("mcp__"))[:STARTUP_EXCERPT_ITEMS],
               "other_tool_count": len(known) - sum(name.startswith("mcp__") for name in known),
               "tools_type": type(tools).__name__,
               "plugin_errors": _scalar(value.get("plugin_errors")),
               "mcp_server_errors": _scalar(value.get("mcp_server_errors"))}
    try:
        return encode(excerpt, sort_keys=True, maximum=STARTUP_DIAGNOSTIC_BYTES).decode("utf-8")
    except (JsonWireError, UnicodeError):
        return '{"excerpt":"unencodable"}'


class ClaudeStartup:
    """Functional startup gate: the whiel MCP server, its tools and the model.

    The init event must show the whiel server connected, every selected whiel
    tool exposed, no plugin or MCP server error, the restricted permission mode
    and the requested model: a silent model fallback would invalidate the
    experiment. The CLI also lists its own built-in tools and whatever account
    servers it loaded, so the tool and server checks are containment checks, not
    equality. Nothing else about the installation is compared.
    """

    def __init__(self, model, tool_names):
        self.model = model
        self.tools = frozenset("mcp__whiel__" + name for name in tool_names)
        self.verified = False
        self.failure = None
        self.refused = False
        self.provider_errors = []
        self.changed = asyncio.Event()

    def diagnostics(self):
        """Bounded provider-reported errors seen in this turn, for C's own log."""
        return list(self.provider_errors)

    def fail(self, message="native startup did not complete", *, refused=False):
        """Latch a failure. Only `refused` marks this gate's own refusal: an
        owner stop that ends the turn is not a startup rejection."""
        if self.failure is None:
            self.failure = message
            self.refused = refused
        self.verified = False
        self.changed.set()

    def refusals(self, value):
        """Every startup predicate this init event fails, named individually."""
        reasons = []
        if self.verified or self.failure:
            reasons.append("a second startup event arrived for this turn")
        tools = value.get("tools")
        if not isinstance(tools, list) or not all(isinstance(name, str) for name in tools):
            reasons.append("the reported tool inventory is not a list of names")
        else:
            missing = sorted(self.tools - set(tools))
            if missing:
                reasons.append("whiel tools are not exposed: " + ",".join(missing))
        servers = value.get("mcp_servers")
        if not isinstance(servers, list):
            reasons.append("the reported MCP server list is not a list")
        elif {"name": "whiel", "status": "connected"} not in servers:
            reasons.append("no whiel MCP server entry reports exactly name=whiel status=connected")
        # A CLI reports these as absent, null or an empty list when it has
        # nothing to report; only a non-empty error list is a failure.
        for name in ("plugin_errors", "mcp_server_errors"):
            if value.get(name):
                reasons.append("the CLI reported " + name)
        if value.get("model") != self.model:
            reasons.append("the reported model is not the requested model")
        if value.get("permissionMode") != "dontAsk":
            reasons.append("the reported permission mode is not the restricted mode")
        return reasons

    def observe(self, value):
        kind, subtype = value.get("type"), value.get("subtype")
        if kind == "system" and subtype == "init":
            reasons = self.refusals(value)
            if reasons:
                self.fail(bounded_redacted_diagnostic(
                    "Claude startup configuration differs from the selected capabilities: "
                    + "; ".join(reasons) + " | init=" + startup_excerpt(value),
                    STARTUP_DIAGNOSTIC_BYTES), refused=True)
            else:
                self.verified = True
                self.changed.set()
        elif kind == "assistant" and isinstance(value.get("message"), dict):
            model = value["message"].get("model")
            if value.get("is_api_error_message") or value.get("error") or placeholder_model(model):
                # The CLI writes these messages itself when the provider refused
                # the request, and names no model in them. That is a provider
                # failure to report, not the silent model fallback this gate
                # exists to catch.
                if len(self.provider_errors) < PROVIDER_ERROR_LIMIT:
                    self.provider_errors.append(provider_error_text(value))
            elif isinstance(model, str) and model != self.model:
                self.fail("Claude reported a different model; fallback is unsupported",
                          refused=True)
        if self.failure is not None:
            raise NativeError("native_setup", self.failure)

    async def wait(self):
        await self.changed.wait()
        if self.failure is not None:
            raise NativeError("native_setup", self.failure)
