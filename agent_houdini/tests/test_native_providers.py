# Author: Fangzhu Shen
"""Exact provider command/environment and startup capability preservation."""

import asyncio
import json
from pathlib import Path
import tomllib
import unittest

from agent_houdini.providers import claude, codex
from agent_houdini.process_tree import ProcessResult
from agent_houdini.provider_runtime import CliEventCapture, NativeError, capture_diagnostic
from agent_houdini.runtime_types import McpLaunch


MODEL = "model-a"


def identity(model=MODEL, effort="medium"):
    return codex.CodexIdentity("/fixture/codex", model, effort, version="fixture-cli 1.2.3")


# The shape an installed Claude Code CLI actually reports: its own built-in
# tools beside the whiel tools, whatever MCP servers the account loaded, and
# null rather than empty error fields.
BUILT_IN_TOOLS = ("Task", "Bash", "Edit", "Write", "Read", "WebFetch", "EndConversation")


INSTALLED_NAMES = ("countermodel", "strongest_refutations", "history", "ledger",
                   "validate_clauses", "evaluate_clauses", "submit")


def installed_init(model=MODEL):
    """One sanitized init event as the installed 2.1.273 CLI reports it."""
    return {"type": "system", "subtype": "init", "cwd": "/private/tmp/wa-fixture/r1",
            "session_id": "00000000-0000-4000-8000-000000000000",
            "tools": ["Task", "Bash", "Glob", "Grep", "ExitPlanMode", "Read", "Edit", "Write",
                      "NotebookEdit", "WebFetch", "TodoWrite", "WebSearch", "BashOutput",
                      "KillShell", "Skill", "EndConversation",
                      "mcp__connector_a__search",
                      "mcp__connector_b__list",
                      "mcp__connector_c__search",
                      "mcp__connector_d__find",
                      *("mcp__whiel__" + name for name in INSTALLED_NAMES)],
            "mcp_servers": [{"name": "connector-a", "status": "connected"},
                            {"name": "connector-b", "status": "connected"},
                            {"name": "whiel", "status": "connected"}],
            "model": model, "permissionMode": "dontAsk", "plugins": [],
            "plugin_errors": None, "mcp_server_errors": None,
            "claude_code_version": "2.1.273", "apiKeySource": "none", "output_style": "default"}


def init(names=("submit", "ledger"), model=MODEL):
    return {"type": "system", "subtype": "init", "model": model,
            "claude_code_version": "2.1.273", "apiKeySource": "none", "output_style": "default",
            "tools": [*BUILT_IN_TOOLS, *("mcp__whiel__" + name for name in names)],
            "permissionMode": "dontAsk", "plugins": [],
            "plugin_errors": None, "mcp_server_errors": None,
            "mcp_servers": [{"name": "whiel", "status": "connected"}]}


class NativeProviderTests(unittest.IsolatedAsyncioTestCase):
    def setUp(self):
        self.transport = McpLaunch(("/fixture/python", "/fixture/relay.py"),
            {"WHIEL_C_SOCKET": "/fixture/relay.sock", "WHIEL_C_TOKEN": "fixture"},
            (Path("/fixture/python"), Path("/fixture/relay.py")))
        self.environment = {"USER": "fixture-user", **{name: "sensitive-" + name for name in (
            "HOME", "CODEX_HOME", "CLAUDE_CONFIG_DIR", "PATH", "LANG", "SSL_CERT_FILE", "SSL_CERT_DIR",
            "HTTPS_PROXY", "HTTP_PROXY", "NO_PROXY", "OPENAI_API_KEY", "ANTHROPIC_API_KEY",
            "WHIEL_PROPOSER_SOCKET", "WHIEL_PROPOSER_TOKEN", "CODEX_APP_SERVER_URL", "PYTHONPATH")}}

    def test_codex_exact_restrictions_and_only_c_relay_resources(self):
        command = codex.launch_command(identity(), Path("/fixture/work"), self.transport,
                                       ("submit", "get_skill", "ledger"), environ=self.environment)
        args = command.argv
        self.assertEqual(args[:12], ("/fixture/codex", "exec", "--ignore-user-config", "--ignore-rules",
            "--strict-config", "--ephemeral", "--skip-git-repo-check", "--json", "--color", "never", "-C", "/fixture/work"))
        self.assertEqual(tuple(args[i + 1] for i, value in enumerate(args) if value == "--disable"),
                         codex.DISABLED_FEATURES)
        self.assertEqual(len(codex.DISABLED_FEATURES), 34)
        settings = {}
        for i, value in enumerate(args):
            if value == "-c":
                key, raw = args[i + 1].split("=", 1)
                settings[key] = tomllib.loads("value=" + raw)["value"]
        self.assertEqual(settings["mcp_servers"], {})
        self.assertEqual(settings["mcp_servers.whiel.command"], "/fixture/python")
        self.assertEqual(settings["mcp_servers.whiel.args"], ["/fixture/relay.py"])
        self.assertEqual(settings["mcp_servers.whiel.env"], dict(self.transport.environment))
        self.assertEqual(settings["mcp_servers.whiel.enabled_tools"], ["submit", "get_skill", "ledger"])
        self.assertEqual(settings["approval_policy"], "never")
        self.assertEqual(settings["shell_environment_policy.inherit"], "none")
        self.assertEqual(args[args.index("-m") + 1], MODEL)
        self.assertEqual(settings["model_reasoning_effort"], "medium")
        self.assertNotIn("model_catalog_json", settings)
        self.assertEqual(settings["mcp_servers.whiel.omit_tools_from"], ["deferred", "code_mode"])
        self.assertEqual(args[-1], "-")
        self.assertEqual(set(command.environment), set(codex.ENVIRONMENT) | {
            "TMPDIR", "CODEX_INTERNAL_APP_SERVER_REMOTE_CONTROL_DISABLED"})
        self.assertFalse(any(name.startswith("WHIEL_PROPOSER") for name in command.environment))

    def test_pass_through_model_and_optional_effort_reach_both_providers(self):
        """Any provider-accepted string is forwarded; C enumerates no models."""
        for model in ("model-b", "vendor/model.2-preview", "モデル"):
            with self.subTest(model=model):
                args = codex.launch_command(codex.CodexIdentity("/fixture/codex", model), Path("/fixture/work"),
                                            self.transport, ("submit",), environ=self.environment).argv
                self.assertEqual(args[args.index("-m") + 1], model)
                self.assertNotIn("model_reasoning_effort", "".join(args))
                selected = claude.ClaudeIdentity("/fixture/claude", model,
                                                 configuration_directory=Path("/fixture/login"))
                args = claude.launch_command(selected, Path("/fixture/work"), self.transport,
                                             ("submit",), environ=self.environment).argv
                self.assertEqual(args[args.index("--model") + 1], model)
                self.assertNotIn("--effort", args)

    def test_usage_changes_only_session_persistence_not_model_or_tools(self):
        default = codex.launch_command(identity(), Path('/fixture/work'), self.transport,
                                       ('submit', 'ledger'), environ=self.environment)
        metered = codex.launch_command(identity(), Path('/fixture/work'), self.transport,
                                       ('submit', 'ledger'), environ=self.environment, persist_usage=True)
        self.assertEqual(metered.argv, tuple(a for a in default.argv if a != '--ephemeral'))
        self.assertEqual(metered.environment, default.environment)

    def test_claude_argv_auth_and_tool_inventory_stay_restricted(self):
        selected = claude.ClaudeIdentity("/fixture/claude", MODEL, "medium", Path("/fixture/login"))
        command = claude.launch_command(selected, Path("/fixture/work"), self.transport,
                                        ("submit", "get_skill"), environ=self.environment)
        args = command.argv
        for option, expected in (("--tools", ""), ("--permission-mode", "dontAsk"), ("--setting-sources", ""),
                                  ("--allowedTools", "mcp__whiel__submit,mcp__whiel__get_skill"),
                                  ("--model", selected.model), ("--effort", "medium")):
            self.assertEqual(args[args.index(option) + 1], expected)
        mcp = json.loads(args[args.index("--mcp-config") + 1])["mcpServers"]["whiel"]
        self.assertEqual(mcp, {"type": "stdio", "command": "/fixture/python", "args": ["/fixture/relay.py"],
                               "env": dict(self.transport.environment)})
        settings = json.loads(args[args.index("--settings") + 1])
        self.assertEqual(settings["fallbackModel"], [])
        self.assertTrue(settings["disableAllHooks"])
        self.assertIn("--no-session-persistence", args)
        self.assertEqual(set(command.environment), set(claude.ENVIRONMENT) | set(claude.DISABLED_ENVIRONMENT) | {"TMPDIR"})
        # The configuration directory is not forced into the environment: only the
        # user's own CLAUDE_CONFIG_DIR passes through, so a keychain login is found.
        self.assertEqual(command.environment["CLAUDE_CONFIG_DIR"], "sensitive-CLAUDE_CONFIG_DIR")
        confined = claude.launch_command(selected, Path("/fixture/work"), self.transport,
                                         ("submit", "get_skill"), environ=self.environment,
                                         isolation="bwrap")
        self.assertEqual(confined.argv, args)
        with self.assertRaisesRegex(NativeError, "unsupported native isolation"):
            claude.launch_command(selected, Path("/fixture/work"), self.transport, ("submit",),
                                  isolation="other")
        # The CLI's own debug log is requested only when the runtime names a
        # file for it, which it does under retention; the default launch has none.
        self.assertNotIn("--debug-file", args)
        logged = claude.launch_command(selected, Path("/fixture/work"), self.transport,
                                       ("submit", "get_skill"), environ=self.environment,
                                       debug_file=Path("/fixture/work/logs/native-debug.txt"))
        self.assertEqual(logged.argv[logged.argv.index("--debug-file") + 1],
                         "/fixture/work/logs/native-debug.txt")
        self.assertEqual([item for item in logged.argv if item != "--debug-file"
                          and item != "/fixture/work/logs/native-debug.txt"], list(args))
        # The thinking allowance is a C agent limit passed to the CLI only when set.
        self.assertNotIn("--max-thinking-tokens", args)
        capped = claude.launch_command(selected, Path("/fixture/work"), self.transport,
                                       ("submit",), environ=self.environment, thinking_tokens=4000)
        self.assertEqual(capped.argv[capped.argv.index("--max-thinking-tokens") + 1], "4000")

    async def test_startup_waits_for_exact_inventory_and_rejects_fallback(self):
        gate = claude.ClaudeStartup(MODEL, ("submit", "ledger"))
        waiter = asyncio.create_task(gate.wait())
        await asyncio.sleep(0)
        self.assertFalse(waiter.done())
        gate.observe(init())
        await waiter
        self.assertTrue(gate.verified)
        for mutation in ({"model": "wrong"}, {"permissionMode": "bypassPermissions"},
                         {"mcp_servers": []}, {"mcp_servers": [{"name": "whiel", "status": "failed"}]},
                         {"tools": ["mcp__whiel__submit"]}, {"mcp_server_errors": ["failure"]},
                         {"plugin_errors": ["failure"]}):
            new_gate = claude.ClaudeStartup(MODEL, ("submit", "ledger"))
            with self.subTest(mutation=mutation), self.assertRaises(NativeError):
                new_gate.observe({**init(), **mutation})
            with self.assertRaises(NativeError):
                await new_gate.wait()
        for event in ({"type": "assistant", "message": {"model": "fallback"}}, init()):
            with self.subTest(event=event), self.assertRaises(NativeError):
                gate.observe(event)

    async def test_installed_cli_startup_event_is_accepted_as_reported(self):
        """Regression: a real 2.1.273 init event, sanitized, must pass the gate.

        The installed CLI advertises every built-in tool and whatever account
        MCP servers it loaded, and reports its error fields as null.
        """
        gate = claude.ClaudeStartup(MODEL, INSTALLED_NAMES)
        gate.observe(installed_init())
        self.assertTrue(gate.verified)
        await gate.wait()

    async def test_restricted_launch_init_event_is_accepted_as_reported(self):
        """Regression: the init event a restricted 2.1.273 launch actually emits.

        With C's argv the CLI exposes no built-in tool and no account MCP
        server, omits the error fields entirely, and adds fields C never reads.
        """
        event = {"type": "system", "subtype": "init", "cwd": "/private/tmp/wa-fixture/r1",
                 "session_id": "00000000-0000-4000-8000-000000000000",
                 "tools": sorted("mcp__whiel__" + name for name in INSTALLED_NAMES),
                 "mcp_servers": [{"name": "whiel", "status": "connected"}],
                 "model": MODEL, "permissionMode": "dontAsk", "slash_commands": [],
                 "apiKeySource": "none", "claude_code_version": "2.1.273",
                 "output_style": "default", "agents": [], "skills": [], "plugins": [],
                 "capabilities": ["interrupt_receipt_v1"], "analytics_disabled": True,
                 "uuid": "00000000-0000-4000-8000-000000000001",
                 "fast_mode_state": "off"}
        gate = claude.ClaudeStartup(MODEL, INSTALLED_NAMES)
        gate.observe(event)
        self.assertTrue(gate.verified)
        await gate.wait()

    async def test_cli_generated_error_message_is_reported_not_called_a_fallback(self):
        """Regression: a refused request is a provider error, not a model swap.

        When the provider refuses the request the CLI writes the message itself
        and puts a bracketed placeholder where the model name goes. Reading that
        placeholder as a silent fallback hid every real failure behind a startup
        refusal, so the gate now records the CLI's own error text instead.
        """
        gate = claude.ClaudeStartup(MODEL, INSTALLED_NAMES)
        capture = CliEventCapture(INSTALLED_NAMES, gate)
        event = {"type": "assistant", "error": "authentication_failed",
                 "is_api_error_message": True, "parent_tool_use_id": None,
                 "message": {"id": "msg_fixture", "type": "message", "role": "assistant",
                             "model": "<synthetic>", "stop_reason": "stop_sequence",
                             "content": [{"type": "text", "text": "Not logged in"}]}}
        capture.feed(json.dumps(init(INSTALLED_NAMES)).encode() + b"\n")
        capture.feed(json.dumps(event).encode() + b"\n")
        self.assertTrue(gate.verified)
        self.assertFalse(capture.summary()["startup_rejected"])
        self.assertIsNone(capture.summary()["startup_failure"])
        self.assertEqual(capture.summary()["provider_errors"],
                         ["authentication_failed: Not logged in"])
        await gate.wait()
        # A genuine fallback still names a model, and is still refused.
        with self.assertRaises(NativeError):
            claude.ClaudeStartup(MODEL, INSTALLED_NAMES).observe(
                {"type": "assistant", "message": {"model": "other-model"}})
        self.assertEqual(gate.provider_errors, ["authentication_failed: Not logged in"])
        for _ in range(claude.PROVIDER_ERROR_LIMIT + 3):
            gate.observe(event)
        self.assertEqual(len(gate.provider_errors), claude.PROVIDER_ERROR_LIMIT)
        # An owner stop ends the turn without claiming the CLI was rejected.
        gate.fail("native turn has ended")
        with self.assertRaises(NativeError):
            capture.feed(json.dumps(event).encode() + b"\n")
        self.assertFalse(capture.summary()["startup_rejected"])
        self.assertEqual(capture.summary()["startup_failure"], "native turn has ended")

    def test_startup_refusal_names_predicates_and_excerpts_the_init_event(self):
        """A refusal has to say which predicate failed and what was reported.

        The excerpt carries only the compared fields; the launch argv, relay
        socket, token, session identity and working directory stay out of it.
        """
        event = installed_init()
        event["mcp_servers"] = [{"name": "whiel", "status": "failed"}]
        event["tools"] = [name for name in event["tools"] if name != "mcp__whiel__submit"]
        event["permissionMode"] = "acceptEdits"
        event["mcp_server_errors"] = ["whiel: connection closed"]
        gate = claude.ClaudeStartup(MODEL, INSTALLED_NAMES)
        with self.assertRaises(NativeError) as raised:
            gate.observe(event)
        text = str(raised.exception)
        for expected in ("whiel tools are not exposed: mcp__whiel__submit",
                         "no whiel MCP server entry reports exactly name=whiel status=connected",
                         "the CLI reported mcp_server_errors",
                         "the reported permission mode is not the restricted mode"):
            self.assertIn(expected, text)
        self.assertNotIn("the reported model is not the requested model", text)
        excerpt = json.loads(text.split("| init=", 1)[1])
        self.assertEqual(excerpt["mcp_servers"], [{"name": "whiel", "status": "failed"}])
        self.assertEqual(excerpt["model"], MODEL)
        self.assertEqual(excerpt["permissionMode"], "acceptEdits")
        self.assertNotIn("mcp__whiel__submit", excerpt["mcp_tools"])
        self.assertIn("mcp__whiel__ledger", excerpt["mcp_tools"])
        self.assertEqual(excerpt["other_tool_count"], 16)
        self.assertEqual(excerpt["mcp_server_errors"], ["whiel: connection closed"])
        for secret in ("/private/tmp/wa-fixture", "session_id", "00000000-0000-4000"):
            self.assertNotIn(secret, text)
        self.assertLessEqual(len(text.encode()), claude.STARTUP_DIAGNOSTIC_BYTES)

    def test_capture_retains_the_startup_refusal_and_cli_stderr(self):
        gate = claude.ClaudeStartup(MODEL, INSTALLED_NAMES)
        capture = CliEventCapture(INSTALLED_NAMES, gate)
        event = installed_init(model="other-model")
        with self.assertRaises(NativeError) as raised:
            capture.feed(json.dumps(event).encode() + b"\n")
        self.assertIn("the reported model is not the requested model", str(raised.exception))
        summary = capture.summary()
        self.assertTrue(summary["startup_rejected"])
        self.assertIn("the reported model is not the requested model", summary["startup_failure"])
        self.assertIn('"model":"other-model"', summary["startup_failure"])
        result = ProcessResult(143, "exited", b"", b"[claude-code:unrecognized_model] detail",
                               summary["stdout_bytes"], 38, False, True)
        text = capture_diagnostic(result, capture)
        self.assertIn("stderr=[claude-code:unrecognized_model] detail", text)
        self.assertIn("provider exited: 143", text)
        self.assertIn("the reported model is not the requested model", text)

    async def test_any_installed_cli_version_starts_and_is_never_compared(self):
        for reported in ("0.0.1", "far-future", None):
            with self.subTest(reported=reported):
                gate = claude.ClaudeStartup(MODEL, ("submit", "ledger"))
                value = init()
                if reported is None:
                    value.pop("claude_code_version")
                else:
                    value["claude_code_version"] = reported
                gate.observe(value)
                self.assertTrue(gate.verified)
                await gate.wait()

    async def test_local_skill_requires_startup_name_without_skill_body(self):
        gate = claude.ClaudeStartup(MODEL, ("submit", "get_skill"))
        with self.assertRaises(NativeError):
            gate.observe(init(("submit",)))
        gate = claude.ClaudeStartup(MODEL, ("submit", "get_skill"))
        gate.observe(init(("submit", "get_skill")))
        self.assertTrue(gate.verified)
        gate.fail("cancelled")
        self.assertFalse(gate.verified)
        with self.assertRaises(NativeError):
            await gate.wait()

    def test_capture_counts_reported_types_and_drains_large_lines(self):
        capture = CliEventCapture(("ledger", "submit"))
        payload = (b"x" * 70000 + b'\n{"type":"turn.started"}\n'
                   b'{"type":"error","type":"turn.failed"}\n' + json.dumps({"type": "item.completed",
                    "item": {"type": "mcp_tool_call", "server": "whiel", "tool": "ledger",
                             "arguments": {"secret": "sk-private"}, "result": "private-content"}}).encode()
                   + b'\n{"type":"turn.started"}\n{"type":"turn.completed"}')
        for i in range(0, len(payload), 7):
            capture.feed(payload[i:i + 7])
        capture.finish()
        summary = capture.summary()
        self.assertEqual(summary["stdout_bytes"], len(payload))
        self.assertEqual(summary["invalid_lines"], 2)
        self.assertEqual(summary["events"], {"turn.started": 2, "item.completed": 1,
                                             "turn.completed": 1})
        self.assertNotIn("private", json.dumps(summary))

    def test_capture_bounds_the_number_of_distinct_event_names(self):
        capture = CliEventCapture()
        for index in range(CliEventCapture.MAXIMUM_EVENT_NAMES + 5):
            capture.feed(json.dumps({"type": f"event{index}"}).encode() + b"\n")
        self.assertEqual(len(capture.events), CliEventCapture.MAXIMUM_EVENT_NAMES)
        self.assertEqual(capture.summary()["unknown_events"], 5)


if __name__ == "__main__":
    unittest.main()
