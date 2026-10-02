# Author: Fangzhu Shen
"""Native Codex selection and exact restricted native command construction."""

from dataclasses import dataclass
import os
from pathlib import Path
import shutil

from ..json_wire import encode
from ..provider_runtime import CommandSpec, NativeError, UNKNOWN_VERSION, probe_version
from ..runtime_types import McpLaunch


DISABLED_FEATURES = (
    "shell_tool", "unified_exec", "shell_snapshot", "code_mode_host", "code_mode",
    "code_mode_only", "code_mode_buffered_exec", "deferred_executor",
    "executor_capability_discovery", "apps", "plugins", "remote_plugin", "skill_search",
    "skill_mcp_dependency_install", "memories", "external_agent_memory_import",
    "browser_use", "browser_use_external", "browser_use_full_cdp_access", "in_app_browser",
    "computer_use", "multi_agent", "multi_agent_v2", "workspace_dependencies", "hooks",
    "image_generation", "tool_suggest", "goals", "auth_elicitation", "tool_call_mcp_elicitation",
    "default_mode_request_user_input", "request_permissions_tool", "request_rule",
    "standalone_web_search",
)
ENVIRONMENT = ("HOME", "CODEX_HOME", "PATH", "SSL_CERT_FILE", "SSL_CERT_DIR",
               "HTTPS_PROXY", "HTTP_PROXY", "NO_PROXY")


@dataclass(frozen=True, slots=True)
class CodexIdentity:
    """Provenance of one selected CLI; no version, hash or catalog requirement."""

    executable: str
    model: str
    reasoning_effort: str | None = None
    version: str = UNKNOWN_VERSION
    schema_version: int = 1
    provider: str = "codex"


def native_environment(environ=None):
    source = os.environ if environ is None else environ
    return {name: source[name] for name in ENVIRONMENT if name in source}


async def verify(model, effort, executable=None, stop=None):
    """Select the CLI from an explicit path or PATH and record what it reports."""
    selected = executable or shutil.which("codex")
    if selected is None:
        raise NativeError("native_setup",
                          "install the native Codex CLI on PATH, or pass an explicit path")
    path = Path(selected).resolve(strict=True)
    if not path.is_file():
        raise NativeError("native_setup", "the selected Codex executable is not a file")
    version = await probe_version(path, native_environment(), stop)
    return CodexIdentity(str(path), model, effort, version)


def _json(value):
    return encode(value).decode()


def launch_command(identity, scratch: Path, transport: McpLaunch | None, tool_names, *, environ=None,
                   persist_usage=False):
    names = tuple(tool_names)
    if transport is None and names:
        raise NativeError("native_setup", "tool-free command cannot expose MCP tools")
    if transport is not None and (not transport.argv or not Path(transport.argv[0]).is_absolute()):
        raise NativeError("native_setup", "the native relay command must be an absolute path")
    args = [identity.executable, "exec", "--ignore-user-config", "--ignore-rules", "--strict-config",
            "--ephemeral", "--skip-git-repo-check", "--json", "--color", "never", "-C", str(scratch),
            "-m", identity.model]
    if persist_usage:
        # Only used with a fresh, request-local sessions mount. Never resume
        # a previous thread. The rollout supplies intermediate token counts
        # which exec --json otherwise emits only at the end of a whole turn.
        args.remove("--ephemeral")
    for feature in DISABLED_FEATURES:
        args.extend(("--disable", feature))

    def setting(key, value):
        args.extend(("-c", key + "=" + _json(value)))

    for key, value in (
        ("approval_policy", "never"), ("sandbox_mode", "danger-full-access"),
        ("project_doc_max_bytes", 0), ("project_doc_fallback_filenames", []),
        ("web_search", "disabled"), ("shell_environment_policy.inherit", "none"),
        ("shell_environment_policy.experimental_use_profile", False), ("history.persistence", "none"),
        ("log_dir", str(scratch / "logs")), ("sqlite_home", str(scratch / "state")),
        ("cli_auth_credentials_store", "file"), ("features.view_image", False),
        ("features.token_budget", False), ("features.current_time_reminder", False),
        ("tools.update_plan.enabled", False), ("tools.experimental_request_user_input.enabled", False),
        ("otel.exporter", "none"), ("otel.metrics_exporter", "none"), ("otel.trace_exporter", "none"),
        ("otel.log_user_prompt", False), ("analytics.enabled", False), ("feedback.enabled", False),
    ):
        setting(key, value)
    if identity.reasoning_effort is not None:
        setting("model_reasoning_effort", identity.reasoning_effort)
    args.extend(("-c", "mcp_servers={}"))
    if transport is not None:
        setting("mcp_servers.whiel.command", transport.argv[0])
        setting("mcp_servers.whiel.args", list(transport.argv[1:]))
        environment = ", ".join(_json(key) + "=" + _json(value)
                                for key, value in sorted(transport.environment.items()))
        args.extend(("-c", "mcp_servers.whiel.env={" + environment + "}"))
        setting("mcp_servers.whiel.enabled_tools", list(names))
        for name in names:
            setting(f"mcp_servers.whiel.tools.{name}.approval_mode", "approve")
        setting("mcp_servers.whiel.omit_tools_from", ["deferred", "code_mode"])
    args.append("-")
    environment = native_environment(environ)
    environment.update(TMPDIR=str(scratch / "tmp"), CODEX_INTERNAL_APP_SERVER_REMOTE_CONTROL_DISABLED="1")
    return CommandSpec(tuple(args), environment, scratch)
