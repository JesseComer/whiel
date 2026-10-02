# Author: Fangzhu Shen
"""Narrow Python-relay command construction, without a Linux namespace claim."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from agent_houdini import bwrap


class LauncherSandboxTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.work = self.root / "request"
        self.work.mkdir(mode=0o700)
        self.home = self.root / "home"
        self.home.mkdir(mode=0o700)
        self.native = self.file("native", 0o555)
        self.catalog = self.file("models.json", 0o444)
        self.python = self.file("python3.12", 0o555)
        self.relay = self.file("mcp_stdio.py", 0o555)
        self.environment = {"HOME": str(self.home), "CODEX_HOME": str(self.home / ".codex"),
                            "HTTPS_PROXY": "http://user:synthetic@proxy.invalid", "NO_PROXY": "local",
                            "HTTP_PROXY": "must-not-pass", "OPENAI_API_KEY": "must-not-pass"}
        self.argv = (str(self.native), "-c", 'cli_auth_credentials_store="file"', "a b")
        self.resources = (self.native, self.catalog, self.python, self.relay)

    def file(self, name, mode):
        path = self.root / name
        path.write_text("synthetic resource")
        path.chmod(mode)
        return path

    def wrap(self, **changes):
        arguments = dict(argv=self.argv, environment=self.environment, work=self.work,
                         readonly_resources=self.resources, timeout_seconds=12.5)
        arguments.update(changes)
        with patch.object(bwrap.platform, "system", return_value="Linux"):
            return bwrap.wrap_native_command(**arguments)

    def test_exact_resources_proxy_and_no_credential_read_or_process(self):
        original = dict(self.environment)
        with patch.object(Path, "read_bytes", side_effect=AssertionError("credential read")), \
             patch.object(Path, "read_text", side_effect=AssertionError("credential read")), \
             patch.object(bwrap.subprocess, "Popen", side_effect=AssertionError("process")):
            argv, env = self.wrap()
            self.assertEqual(argv, (str(Path(bwrap.__file__).with_name("bwrap.sh")), "--", *self.argv))
            self.assertEqual(json.loads(env["WHIEL_BWRAP_RO"]), list(map(str, self.resources)))
            self.assertEqual(env["WHIEL_BWRAP_TIMEOUT_SECS"], "12.5")
            config = bwrap.settings(env, self.argv)
            with patch.object(bwrap, "SYSTEM_READONLY_PATHS", ()), \
                 patch.object(bwrap, "SYSTEM_READONLY_BINDINGS", ()):
                mounts = bwrap.mount_command("/usr/bin/bwrap", config, self.argv)
        self.assertEqual(self.environment, original)
        pairs = [mounts[index + 1:index + 3] for index, value in enumerate(mounts) if value == "--ro-bind"]
        self.assertEqual(pairs, [[str(path), str(path)] for path in self.resources])
        self.assertNotIn(str(self.root), mounts)
        self.assertNotIn("/usr/bin", mounts)
        self.assertEqual(bwrap.child_environment(env), {
            "PATH": "/usr/bin:/bin", "HTTPS_PROXY": original["HTTPS_PROXY"], "NO_PROXY": "local"})
        self.assertNotIn(original["HTTPS_PROXY"], mounts)
        self.assertNotIn(original["HTTPS_PROXY"], argv)

    def test_resources_still_reject_directories_links_and_nonexecutables(self):
        alias = self.root / "relay_alias"
        alias.symlink_to(self.relay)
        plain = self.file("ordinary.py", 0o444)
        certificate = self.root / "Certificate"
        certificate.mkdir()
        proof = certificate / "Valid.lean"
        proof.write_text("synthetic denied material")
        proof.chmod(0o555)
        for extra in (self.root, alias, plain, proof):
            with self.subTest(extra=extra), self.assertRaises(bwrap.SandboxError):
                self.wrap(readonly_resources=(*self.resources, extra))

    def test_configuration_refusal_has_no_local_fallback(self):
        for change in ({"timeout_seconds": 0}, {"timeout_seconds": float("inf")},
                       {"auth_mode": "guess"}, {"readonly_resources": self.resources[1:]},
                       {"argv": (str(self.native), "\0")},
                       {"environment": {**self.environment, "BROKEN=KEY": "value"}}):
            with self.subTest(change=change), self.assertRaises(bwrap.SandboxError):
                self.wrap(**change)
        with patch.object(bwrap.platform, "system", return_value="Darwin"), \
             self.assertRaisesRegex(bwrap.SandboxError, "no local fallback"):
            bwrap.wrap_native_command(self.argv, self.environment, self.work, self.resources, 1)

    def test_relay_requires_system_python_and_an_exact_executable_file(self):
        with self.assertRaisesRegex(bwrap.SandboxError, "absolute"):
            bwrap.python_relay_resources(Path("python3"), self.relay)
        with self.assertRaisesRegex(bwrap.SandboxError, "system /usr/bin"):
            bwrap.python_relay_resources(self.python, self.relay)
        system_python = Path("/usr/bin/python3.12")
        original_resolve, original_lstat = Path.resolve, Path.lstat

        def resolve(path, *args, **kwargs):
            return system_python if path == Path("/usr/bin/python3") else original_resolve(path, *args, **kwargs)

        def lstat(path, *args, **kwargs):
            return original_lstat(self.python) if path == system_python else original_lstat(path, *args, **kwargs)

        with patch.object(Path, "resolve", resolve), patch.object(Path, "lstat", lstat):
            self.assertEqual(bwrap.python_relay_resources(Path("/usr/bin/python3"), self.relay),
                             (system_python, self.relay))
            self.relay.chmod(0o444)
            with self.assertRaises(bwrap.SandboxError):
                bwrap.python_relay_resources(Path("/usr/bin/python3"), self.relay)
            self.relay.chmod(0o555)
            alias = self.root / "relay_alias"
            alias.symlink_to(self.relay)
            with self.assertRaises(bwrap.SandboxError):
                bwrap.python_relay_resources(Path("/usr/bin/python3"), alias)


if __name__ == "__main__":
    unittest.main()
