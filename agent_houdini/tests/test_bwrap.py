# Author: Fangzhu Shen
# Framework II adaptation based on her original agent setup.
"""Synthetic-only wrapper tests; no Linux confinement claim on other hosts."""
import importlib.util
import io
import json
import os
from pathlib import Path
import signal
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[1] / "bwrap.py"
SPEC = importlib.util.spec_from_file_location("agent_houdini_bwrap", SOURCE)
sb = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(sb)


class WrapperTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.home = self.root / "home"
        self.codex = self.home / ".codex"
        self.codex.mkdir(parents=True, mode=0o700)
        self.work = self.root / "request"
        self.work.mkdir(mode=0o700)
        self.executable = self.root / "runtime"
        self.executable.write_text("synthetic runtime")
        self.executable.chmod(0o555)
        self.auth = self.codex / "auth.json"
        self.auth.write_text('{"synthetic":"old"}')
        self.auth.chmod(0o600)
        self.env = {"HOME": str(self.home), "CODEX_HOME": str(self.codex),
                    "WHIEL_BWRAP_WORK": str(self.work),
                    "WHIEL_BWRAP_RO": json.dumps([str(self.executable)]),
                    "WHIEL_BWRAP_TIMEOUT_SECS": "10", "WHIEL_BWRAP_AUTH": "required"}
        self.command = [str(self.executable), "-c", 'cli_auth_credentials_store="file"']

    def test_exact_auth_mount_no_home_copy_or_parent_bind(self):
        config = sb.settings(self.env, self.command)
        with patch.object(Path, "read_bytes", side_effect=AssertionError("credential read")), \
             patch.object(Path, "read_text", side_effect=AssertionError("credential read")):
            sb.private_file(self.auth)
            argv = sb.mount_command("/usr/bin/bwrap", config, self.command)
        mounts = [argv[i + 1:i + 3] for i, value in enumerate(argv) if value == "--bind"]
        self.assertEqual(mounts, [[str(self.work)] * 2, [str(self.auth)] * 2])
        self.assertNotIn([str(self.home)] * 2, mounts)
        self.assertIn("--unshare-all", argv)
        self.assertIn("--die-with-parent", argv)
        self.assertNotIn("--clearenv", argv)
        environment = {argv[i + 1]: argv[i + 2]
                       for i, value in enumerate(argv) if value == "--setenv"}
        self.assertEqual(environment["CODEX_INTERNAL_APP_SERVER_REMOTE_CONTROL_DISABLED"], "1")

    def test_codex_profile_argv_is_pinned(self):
        """Exact Codex construction. A second provider route must not change it."""
        system = self.root / "system"
        system.mkdir()
        bundle = system / "tls-ca-bundle.pem"
        bundle.write_text("synthetic public CA")
        alias = system / "cert.pem"
        config = sb.settings(self.env, self.command)
        with patch.object(sb, "SYSTEM_READONLY_PATHS", (str(system),)), \
             patch.object(sb, "SYSTEM_READONLY_BINDINGS", ((str(bundle), str(alias)),)):
            argv = sb.mount_command("/usr/bin/bwrap", config, self.command)
        self.assertEqual(argv, [
            "/usr/bin/bwrap", "--unshare-all", "--share-net", "--new-session",
            "--die-with-parent", "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp",
            "--tmpfs", "/run", "--tmpfs", str(self.home), "--perms", "0700",
            "--dir", str(self.codex),
            "--ro-bind", str(system), str(system),
            "--ro-bind", str(bundle), str(alias),
            "--ro-bind", str(self.executable), str(self.executable),
            "--bind", str(self.work), str(self.work),
            "--bind", str(self.auth), str(self.auth),
            "--chdir", str(self.work), "--setenv", "HOME", str(self.home),
            "--setenv", "CODEX_HOME", str(self.codex),
            "--setenv", "PATH", "/usr/bin:/bin", "--setenv", "TMPDIR", "/tmp",
            "--setenv", "LANG", "C.UTF-8",
            "--setenv", "CODEX_INTERNAL_APP_SERVER_REMOTE_CONTROL_DISABLED", "1",
            "--", *self.command])

    def test_native_style_in_place_refresh_preserves_identity(self):
        before = sb.private_file(self.auth)
        # Only the fixture imitates native storage; wrapper never reads/writes this file.
        with self.auth.open("w") as stream:
            stream.write('{"synthetic":"refreshed"}')
        self.assertEqual(before, sb.private_file(self.auth))
        self.assertIn("refreshed", self.auth.read_text())

    def test_auth_substitution_links_permissions_and_missing_fail(self):
        identity = sb.private_file(self.auth)
        self.auth.rename(self.codex / "old")
        self.auth.write_text("synthetic replacement")
        self.auth.chmod(0o600)
        self.assertNotEqual(identity, sb.private_file(self.auth))
        self.auth.chmod(0o644)
        with self.assertRaises(sb.SandboxError):
            sb.private_file(self.auth)
        self.auth.unlink()
        self.auth.symlink_to(self.codex / "old")
        with self.assertRaises(sb.SandboxError):
            sb.private_file(self.auth)
        self.auth.unlink()
        os.link(self.codex / "old", self.auth)
        with self.assertRaises(sb.SandboxError):
            sb.private_file(self.auth)
        self.auth.unlink()
        with self.assertRaises(OSError):
            sb.private_file(self.auth)

    def test_certificate_directory_and_link_resources_are_rejected(self):
        certificate = self.root / "Certificate"
        certificate.mkdir()
        proof = certificate / "Valid.lean"
        proof.write_text("synthetic")
        linked = self.root / "linked"
        linked.symlink_to(proof)
        for path in (certificate, proof, linked):
            self.env["WHIEL_BWRAP_RO"] = json.dumps([str(self.executable), str(path)])
            with self.subTest(path=path), self.assertRaises(sb.SandboxError):
                sb.settings(self.env, self.command)

    def test_no_auth_fixture_has_no_credential_mount(self):
        self.env["WHIEL_BWRAP_AUTH"] = "none"
        self.auth.unlink()
        config = sb.settings(self.env, [str(self.executable)])
        argv = sb.mount_command("/usr/bin/bwrap", config, [str(self.executable)])
        self.assertNotIn(str(self.auth), argv)

    def test_public_ca_source_gets_exact_conventional_readonly_binding(self):
        extracted = self.root / "etc/pki/ca-trust/extracted/pem"
        extracted.mkdir(parents=True)
        bundle = extracted / "tls-ca-bundle.pem"
        bundle.write_text("synthetic public CA")
        tls = self.root / "etc/pki/tls"
        tls.mkdir(parents=True)
        alias = tls / "cert.pem"
        config = sb.settings(self.env, self.command)
        with patch.object(sb, "SYSTEM_READONLY_PATHS",
                          (str(extracted),)), \
             patch.object(sb, "SYSTEM_READONLY_BINDINGS",
                          ((str(bundle), str(alias)),)):
            argv = sb.mount_command("/usr/bin/bwrap", config, self.command)
        mounts = [argv[i + 1:i + 3]
                  for i, value in enumerate(argv) if value == "--ro-bind"]
        self.assertIn([str(bundle), str(alias)], mounts)
        self.assertIn([str(extracted), str(extracted)], mounts)
        self.assertNotIn("/etc", sb.SYSTEM_READONLY_PATHS)
        self.assertNotIn("/etc/pki/tls/private", sb.SYSTEM_READONLY_PATHS)
        self.assertFalse(any("private" in source or "private" in target
                             for source, target in sb.SYSTEM_READONLY_BINDINGS))

    def test_ca_binding_does_not_follow_a_substituted_symlink_source(self):
        private = self.root / "private"
        private.mkdir()
        secret = private / "secret.pem"
        secret.write_text("synthetic private material")
        linked_bundle = self.root / "tls-ca-bundle.pem"
        linked_bundle.symlink_to(secret)
        target = self.root / "cert.pem"
        config = sb.settings(self.env, self.command)
        with patch.object(sb, "SYSTEM_READONLY_PATHS", ()), \
             patch.object(sb, "SYSTEM_READONLY_BINDINGS",
                          ((str(linked_bundle), str(target)),)):
            argv = sb.mount_command("/usr/bin/bwrap", config, self.command)
        mounts = [argv[i + 1:i + 3]
                  for i, value in enumerate(argv) if value == "--ro-bind"]
        self.assertNotIn([str(secret), str(target)], mounts)

    def test_only_selected_proxy_environment_is_inherited(self):
        host = {"PATH": "/host/bin", "HTTPS_PROXY": "http://user:secret@proxy.invalid",
                "NO_PROXY": "localhost,.invalid", "OPENAI_API_KEY": "provider-secret",
                "HTTP_PROXY": "http://must-not-pass.invalid", "ALL_PROXY": "socks5://private",
                "https_proxy": "http://lowercase-must-not-pass.invalid",
                "no_proxy": "lowercase-must-not-pass", "SSL_CERT_FILE": "/private/ca.pem",
                "WHIEL_BWRAP_WORK": "/private/work"}
        inherited = sb.child_environment(host)
        self.assertEqual(inherited, {"PATH": "/usr/bin:/bin",
                                     "HTTPS_PROXY": host["HTTPS_PROXY"],
                                     "NO_PROXY": host["NO_PROXY"]})
        config = sb.settings(self.env, self.command)
        argv = sb.mount_command("/usr/bin/bwrap", config, self.command)
        self.assertNotIn(host["HTTPS_PROXY"], argv)
        self.assertNotIn(host["NO_PROXY"], argv)
        self.assertNotIn("HTTPS_PROXY", argv)
        self.assertNotIn("NO_PROXY", argv)

    def test_explicit_file_backend_and_private_work_are_required(self):
        with self.assertRaises(sb.SandboxError):
            sb.settings(self.env, [str(self.executable)])
        self.work.chmod(0o755)
        with self.assertRaises(sb.SandboxError):
            sb.settings(self.env, self.command)

    def test_shared_lock_serializes_and_wait_is_cancellable_and_bounded(self):
        lock = sb.acquire_auth_lock(self.auth, time.monotonic() + 1, lambda: False)
        try:
            self.assertFalse(os.get_inheritable(lock))
            with self.assertRaisesRegex(sb.SandboxError, "timed out"):
                sb.acquire_auth_lock(self.auth, time.monotonic() + 0.03, lambda: False)
            with self.assertRaisesRegex(sb.SandboxError, "cancelled"):
                sb.acquire_auth_lock(self.auth, time.monotonic() + 1, lambda: True)
        finally:
            os.close(lock)
        again = sb.acquire_auth_lock(self.auth, time.monotonic() + 1, lambda: False)
        os.close(again)

    def test_supervisor_kills_and_joins_timed_out_child(self):
        child = subprocess.Popen(["/bin/sleep", "20"], stdout=subprocess.DEVNULL)
        environment = {"PATH": "/usr/bin:/bin", "HTTPS_PROXY": "synthetic"}
        with patch.object(sb.subprocess, "Popen", return_value=child) as launch:
            self.assertEqual(sb.supervise(["synthetic"], time.monotonic(), lambda: False,
                                          environment), 124)
        self.assertIsNotNone(child.poll())
        self.assertTrue(launch.call_args.kwargs["close_fds"])
        self.assertTrue(launch.call_args.kwargs["start_new_session"])
        self.assertEqual(launch.call_args.kwargs["env"], environment)

    def test_supervisor_joins_cancelled_child(self):
        child = subprocess.Popen(["/bin/sleep", "20"], stdout=subprocess.DEVNULL)
        with patch.object(sb.subprocess, "Popen", return_value=child):
            self.assertEqual(sb.supervise(["synthetic"], time.monotonic() + 20, lambda: True,
                                          {"PATH": "/usr/bin:/bin"}), 130)
        self.assertIsNotNone(child.poll())

    def test_supervisor_escalates_term_ignoring_child_and_joins(self):
        child = subprocess.Popen([sys.executable, "-c",
                                  "import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); print('ready',flush=True); time.sleep(20)"],
                                 stdout=subprocess.PIPE)
        self.assertEqual(child.stdout.readline(), b"ready\n")
        try:
            with patch.object(sb.subprocess, "Popen", return_value=child):
                self.assertEqual(sb.supervise(["synthetic"], time.monotonic(), lambda: False,
                                              {"PATH": "/usr/bin:/bin"}), 124)
            self.assertEqual(child.returncode, -signal.SIGKILL)
        finally:
            child.stdout.close()
            if child.poll() is None:
                child.kill()
            child.wait()

    def test_work_cannot_mount_repository_or_linked_proof_material(self):
        for name in ("Input.lean", "lean-toolchain", "Benchmark"):
            path = self.work / name
            path.write_text("synthetic")
            with self.subTest(name=name), self.assertRaises(sb.SandboxError):
                sb.settings(self.env, self.command)
            path.unlink()
        path = self.work / "escape"
        path.symlink_to(self.auth)
        with self.assertRaises(sb.SandboxError):
            sb.settings(self.env, self.command)

    def test_failed_start_releases_auth_lock_without_changing_auth(self):
        before = self.auth.read_bytes()
        with patch.dict(os.environ, self.env, clear=True), patch.object(sb.platform, "system", return_value="Linux"), \
             patch.object(sb.Path, "is_file", return_value=True), \
             patch.object(sb, "supervise", side_effect=OSError("synthetic startup failure")), \
             patch("sys.stderr", new_callable=io.StringIO):
            self.assertEqual(sb.main(self.command), 125)
        lock = sb.acquire_auth_lock(self.auth, time.monotonic() + 1, lambda: False)
        os.close(lock)
        self.assertEqual(before, self.auth.read_bytes())

    def test_no_platform_or_bwrap_fallback(self):
        with patch.object(sb.platform, "system", return_value="Darwin"), \
             patch("sys.stderr", new_callable=io.StringIO), patch.object(sb, "supervise") as launch:
            self.assertEqual(sb.main(self.command), 125)
            launch.assert_not_called()
        with patch.object(sb.platform, "system", return_value="Linux"), \
             patch.object(sb.Path, "is_file", return_value=False), \
             patch("sys.stderr", new_callable=io.StringIO), patch.object(sb, "supervise") as launch:
            self.assertEqual(sb.main(self.command), 125)
            launch.assert_not_called()


if __name__ == "__main__":
    unittest.main()
