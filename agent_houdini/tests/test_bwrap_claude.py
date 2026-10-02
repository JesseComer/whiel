# Author: Fangzhu Shen
# Framework II adaptation based on Fangzhu Shen's original agent setup.
"""Claude wrapper profile: argument construction only, on any host.

These are synthetic argument-construction tests. They make no claim about real
Linux namespace, mount or credential behavior, which is verified separately on
the target Linux host.
"""
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from agent_houdini import preflight
from agent_houdini.providers import claude as adapter

SOURCE = Path(__file__).resolve().parents[1] / "bwrap.py"
SPEC = importlib.util.spec_from_file_location("agent_houdini_bwrap_claude", SOURCE)
sb = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(sb)


class ClaudeProfileTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.home = self.root / "home"
        self.configuration = self.home / ".claude"
        self.configuration.mkdir(parents=True, mode=0o700)
        self.work = self.root / "request"
        self.work.mkdir(mode=0o700)
        self.executable = self.root / "claude"
        self.executable.write_text("synthetic runtime")
        self.executable.chmod(0o555)
        self.credentials = self.configuration / ".credentials.json"
        self.credentials.write_text('{"synthetic":"login"}')
        self.credentials.chmod(0o600)
        self.env = {"HOME": str(self.home), "CLAUDE_CONFIG_DIR": str(self.configuration),
                    "WHIEL_BWRAP_PROVIDER": "claude", "WHIEL_BWRAP_WORK": str(self.work),
                    "WHIEL_BWRAP_RO": json.dumps([str(self.executable)]),
                    "WHIEL_BWRAP_TIMEOUT_SECS": "10", "WHIEL_BWRAP_AUTH": "required"}
        self.command = [str(self.executable), "-p", "--model", "synthetic-selection"]

    def system(self):
        """Deterministic stand-ins for the host's public CA and DNS mounts."""
        directory = self.root / "system"
        directory.mkdir(exist_ok=True)
        bundle = directory / "tls-ca-bundle.pem"
        bundle.write_text("synthetic public CA")
        return directory, bundle, directory / "cert.pem"

    def build(self, command=None):
        directory, bundle, alias = self.system()
        command = self.command if command is None else command
        config = sb.settings(self.env, command)
        with patch.object(sb, "SYSTEM_READONLY_PATHS", (str(directory),)), \
             patch.object(sb, "SYSTEM_READONLY_BINDINGS", ((str(bundle), str(alias)),)):
            return config, sb.mount_command("/usr/bin/bwrap", config, command)

    def test_claude_profile_argv_is_pinned(self):
        state = self.configuration / ".claude.json"
        state.write_text('{"synthetic":"onboarding"}')
        directory, bundle, alias = self.system()
        # No credential byte is opened, hashed or copied while building argv.
        with patch.object(Path, "read_bytes", side_effect=AssertionError("credential read")), \
             patch.object(Path, "read_text", side_effect=AssertionError("credential read")):
            config = sb.settings(self.env, self.command)
            with patch.object(sb, "SYSTEM_READONLY_PATHS", (str(directory),)), \
                 patch.object(sb, "SYSTEM_READONLY_BINDINGS", ((str(bundle), str(alias)),)):
                argv = sb.mount_command("/usr/bin/bwrap", config, self.command)
        self.assertEqual(argv, [
            "/usr/bin/bwrap", "--unshare-all", "--share-net", "--new-session",
            "--die-with-parent", "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp",
            "--tmpfs", "/run", "--tmpfs", str(self.home), "--perms", "0700",
            "--dir", str(self.configuration),
            "--ro-bind", str(directory), str(directory),
            "--ro-bind", str(bundle), str(alias),
            "--ro-bind", str(self.executable), str(self.executable),
            "--bind", str(self.work), str(self.work),
            "--ro-bind", str(self.credentials), str(self.credentials),
            "--ro-bind", str(state), str(state),
            "--chdir", str(self.work), "--setenv", "HOME", str(self.home),
            "--setenv", "CLAUDE_CONFIG_DIR", str(self.configuration),
            "--setenv", "PATH", "/usr/bin:/bin", "--setenv", "TMPDIR", "/tmp",
            "--setenv", "LANG", "C.UTF-8",
            "--setenv", "CLAUDE_CODE_DISABLE_ATTACHMENTS", "1",
            "--setenv", "CLAUDE_CODE_DISABLE_AUTO_MEMORY", "1",
            "--setenv", "CLAUDE_CODE_DISABLE_CLAUDE_MDS", "1",
            "--setenv", "CLAUDE_CODE_DISABLE_GIT_INSTRUCTIONS", "1",
            "--setenv", "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC", "1",
            "--setenv", "CLAUDE_CODE_DISABLE_OFFICIAL_MARKETPLACE_AUTOINSTALL", "1",
            "--setenv", "ENABLE_CLAUDEAI_MCP_SERVERS", "false",
            "--setenv", "ENABLE_TOOL_SEARCH", "false",
            "--", *self.command])

    def test_login_state_is_only_ever_mounted_readonly(self):
        for name in (".claude.json", "settings.json"):
            (self.configuration / name).write_text("{}")
        _, argv = self.build()
        writable = [argv[index + 1:index + 3]
                    for index, value in enumerate(argv) if value == "--bind"]
        self.assertEqual(writable, [[str(self.work)] * 2])
        readonly = [argv[index + 1:index + 3]
                    for index, value in enumerate(argv) if value == "--ro-bind"]
        for name in (".credentials.json", ".claude.json", "settings.json"):
            self.assertIn([str(self.configuration / name)] * 2, readonly)
        self.assertNotIn([str(self.home)] * 2, writable + readonly)
        self.assertNotIn([str(self.configuration)] * 2, writable + readonly)

    def test_absent_optional_state_is_not_mounted(self):
        _, argv = self.build()
        for name in (".claude.json", "settings.json"):
            self.assertNotIn(str(self.configuration / name), argv)
        self.assertIn(str(self.credentials), argv)
        self.env["WHIEL_BWRAP_AUTH"] = "none"
        self.credentials.unlink()
        _, argv = self.build([str(self.executable), "--version"])
        self.assertNotIn(str(self.credentials), argv)

    def test_unsafe_or_missing_credentials_are_rejected(self):
        self.assertEqual(sb.auth_resources(sb.settings(self.env, self.command)),
                         (self.credentials,))
        identity = sb.private_file(self.credentials)
        self.credentials.rename(self.configuration / "old")
        self.credentials.write_text("synthetic replacement")
        self.credentials.chmod(0o600)
        self.assertNotEqual(identity, sb.private_file(self.credentials))
        for mode in (0o644, 0o666, 0o400):
            self.credentials.chmod(mode)
            with self.subTest(mode=oct(mode)), self.assertRaises(sb.SandboxError):
                sb.private_file(self.credentials)
        self.credentials.chmod(0o600)
        self.credentials.unlink()
        self.credentials.symlink_to(self.configuration / "old")
        with self.assertRaises(sb.SandboxError):
            sb.private_file(self.credentials)
        self.credentials.unlink()
        os.link(self.configuration / "old", self.credentials)
        with self.assertRaises(sb.SandboxError):
            sb.private_file(self.credentials)
        self.credentials.unlink()
        with self.assertRaises(OSError):
            sb.private_file(self.credentials)

    def test_world_writable_credential_ancestor_is_rejected(self):
        self.configuration.chmod(0o707)
        try:
            with self.assertRaises(sb.SandboxError):
                sb.private_file(self.credentials)
        finally:
            self.configuration.chmod(0o700)

    def test_confined_environment_is_the_wrapper_allowlist(self):
        _, argv = self.build()
        environment = {argv[index + 1]: argv[index + 2]
                       for index, value in enumerate(argv) if value == "--setenv"}
        self.assertEqual(environment, {
            "HOME": str(self.home), "CLAUDE_CONFIG_DIR": str(self.configuration),
            "PATH": "/usr/bin:/bin", "TMPDIR": "/tmp", "LANG": "C.UTF-8",
            **adapter.DISABLED_ENVIRONMENT})
        # The wrapper, not the adapter, is authoritative inside the namespace;
        # this pins the two lists together.
        self.assertEqual(dict(sb.PROVIDER_PROFILES["claude"]["environment"]),
                         adapter.DISABLED_ENVIRONMENT)
        self.assertFalse([name for name in environment if name.startswith("CODEX")])
        host = {"PATH": "/host/bin", "HTTPS_PROXY": "http://user:secret@proxy.invalid",
                "NO_PROXY": "localhost,.invalid", "ANTHROPIC_API_KEY": "provider-secret",
                "ANTHROPIC_AUTH_TOKEN": "must-not-pass",
                "CLAUDE_CODE_OAUTH_TOKEN": "must-not-pass",
                "HTTP_PROXY": "http://must-not-pass.invalid",
                "SSL_CERT_FILE": "/private/ca.pem", "WHIEL_BWRAP_WORK": "/private/work"}
        self.assertEqual(sb.child_environment(host),
                         {"PATH": "/usr/bin:/bin", "HTTPS_PROXY": host["HTTPS_PROXY"],
                          "NO_PROXY": host["NO_PROXY"]})
        for name in ("ANTHROPIC_API_KEY", "ANTHROPIC_AUTH_TOKEN", "CLAUDE_CODE_OAUTH_TOKEN"):
            self.assertNotIn(name, argv)

    def test_claude_resources_must_be_executables_outside_the_login_directory(self):
        catalog = self.root / "models.json"
        catalog.write_text("{}")
        catalog.chmod(0o444)
        inside = self.configuration / "extra"
        inside.write_text("synthetic")
        inside.chmod(0o555)
        for path in (catalog, inside):
            self.env["WHIEL_BWRAP_RO"] = json.dumps([str(self.executable), str(path)])
            with self.subTest(path=path.name), self.assertRaises(sb.SandboxError):
                sb.settings(self.env, self.command)

    def test_claude_needs_no_codex_auth_backend_argument(self):
        # The Codex profile requires an explicit file-auth argument; Claude's CLI
        # has no such option, so the command itself carries no auth selection.
        config = sb.settings(self.env, [str(self.executable)])
        self.assertEqual(config.provider, "claude")
        self.assertEqual(config.auth_mode, "required")
        self.assertFalse(any("cli_auth_credentials_store" in argument
                             for argument in self.command))

    def test_request_and_login_directories_may_not_overlap(self):
        for variable, value in (("CLAUDE_CONFIG_DIR", str(self.home)),
                                ("CLAUDE_CONFIG_DIR", str(self.home.parent)),
                                ("CLAUDE_CONFIG_DIR", str(self.work)),
                                ("WHIEL_BWRAP_WORK", str(self.configuration))):
            environment = dict(self.env, **{variable: value})
            with self.subTest(variable=variable, value=value), \
                 self.assertRaises((sb.SandboxError, OSError)):
                sb.settings(environment, self.command)

    def test_unknown_provider_profile_is_rejected(self):
        self.env["WHIEL_BWRAP_PROVIDER"] = "other"
        with self.assertRaisesRegex(sb.SandboxError, "unsupported provider profile"):
            sb.settings(self.env, self.command)
        with patch.object(sb.platform, "system", return_value="Linux"), \
             self.assertRaisesRegex(sb.SandboxError, "unsupported provider profile"):
            sb.wrap_native_command(self.command, {}, self.work, (self.executable,), 10,
                                   provider="other")

    def test_wrapper_invocation_declares_the_selected_profile(self):
        with patch.object(sb.platform, "system", return_value="Linux"):
            argv, environment = sb.wrap_native_command(
                self.command, {"HOME": str(self.home)}, self.work, (self.executable,), 10,
                provider="claude")
        self.assertEqual(argv, (str(SOURCE.with_name("bwrap.sh")), "--", *self.command))
        self.assertEqual(environment["WHIEL_BWRAP_PROVIDER"], "claude")
        with patch.object(sb.platform, "system", return_value="Linux"):
            _, default = sb.wrap_native_command(self.command, {"HOME": str(self.home)},
                                                self.work, (self.executable,), 10,
                                                auth_mode="none")
        self.assertEqual(default["WHIEL_BWRAP_PROVIDER"], "codex")


class PreflightProfileTests(unittest.TestCase):
    """The preflight fixtures are checked for agreement with the wrapper only.

    The kernel fixture itself runs on the target Linux host; nothing here
    executes bubblewrap or a provider CLI.
    """

    def test_preflight_fixtures_match_the_wrapper_profiles(self):
        self.assertEqual(sorted(preflight.PROVIDERS), sorted(sb.PROVIDER_PROFILES))
        for name, fixture in preflight.PROVIDERS.items():
            with self.subTest(provider=name):
                profile = sb.PROVIDER_PROFILES[name]
                self.assertEqual(fixture["home_variable"], profile["home_variable"])
                self.assertEqual(fixture["home_directory"], profile["home_directory"])
                self.assertEqual((fixture["auth_file"],), profile["auth_files"])
                self.assertEqual(fixture["credential_mode"] == "refresh",
                                 profile["auth_bind"] == "--bind")
                self.assertEqual(bool(profile["required_arguments"]),
                                 fixture["marker"] in profile["required_arguments"])
        compile(preflight.PROBE, "<probe>", "exec")

    def test_claude_preflight_needs_no_pinned_installation(self):
        with patch.object(preflight.shutil, "which", return_value=None):
            with self.assertRaisesRegex(RuntimeError, "Claude Code CLI"):
                preflight.cli_identity("claude", None)
        self.assertEqual(preflight.cli_identity("claude", str(SOURCE.with_name("bwrap.sh"))),
                         {"executable": str(SOURCE.with_name("bwrap.sh"))})
        with self.assertRaises(OSError):
            preflight.cli_identity("claude", str(SOURCE.parent / "missing-cli"))


if __name__ == "__main__":
    unittest.main()
