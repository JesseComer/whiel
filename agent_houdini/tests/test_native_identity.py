# Author: Fangzhu Shen
"""Identity probes use synthetic executables, never installed providers or login."""

import asyncio
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import AsyncMock, patch

from agent_houdini.json_wire import encode
from agent_houdini.process_tree import OwnedProcess, ProcessResult
from agent_houdini.provider_runtime import (
    CliEventCapture, CommandSpec, NativeError, UNKNOWN_VERSION, capture_diagnostic, probe,
    verify_provider,
)
from agent_houdini.providers import claude, codex
from agent_houdini.runtime_types import NativeOptions
from agent_houdini.tests.test_native_process_tree import Stop, alive, await_events, make_fixture, terminate


class NativeIdentityTests(unittest.IsolatedAsyncioTestCase):
    async def test_known_cancellation_does_not_spawn_probe(self):
        stop = Stop()
        stop.set("deadline")
        with patch.object(OwnedProcess, "start", AsyncMock()) as spawn:
            with self.assertRaises(NativeError) as caught:
                await probe(CommandSpec(("/never-launched",), {}, Path("/tmp")), stop)
            self.assertEqual(caught.exception.code, "deadline")
            spawn.assert_not_called()

    async def test_version_probe_success_status_and_output_bound(self):
        for stdout, exit_code, maximum, accepted in (
            ("9.9.9 (fixture CLI)\n", 0, 1024, True),
            ("9.9.9 (fixture CLI)\n", 7, 1024, False),
            ("x" * 4096, 0, 1024, False),
        ):
            with self.subTest(exit_code=exit_code, size=len(stdout)), tempfile.TemporaryDirectory(dir="/tmp") as name:
                root = Path(name)
                script = make_fixture(root, version=stdout, version_exit=exit_code)
                command = CommandSpec((sys.executable, str(script), "--version"), {}, root)
                if accepted:
                    self.assertEqual(await probe(command, maximum=maximum), stdout.encode())
                else:
                    with self.assertRaises(NativeError):
                        await probe(command, maximum=maximum)

    async def test_setup_sized_output_and_distinct_helper_stderr_bound(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as name:
            root = Path(name)
            script = make_fixture(root, version="x" * 48000)
            command = CommandSpec((sys.executable, str(script), "--version"), {}, root)
            self.assertEqual(len(await probe(command)), 48000)
            make_fixture(root, version="ok", version_stderr="x" * 70000)
            with self.assertRaises(NativeError):
                await probe(command)
            self.assertEqual(await probe(command, stderr_maximum=None), b"ok")

    async def test_claude_accepts_any_installed_version_as_provenance_only(self):
        for version, expected in (("2.1.266 (Claude Code)\n", "2.1.266 (Claude Code)"),
                                  ("99.0.0 (Claude Code)", "99.0.0 (Claude Code)"),
                                  ("", UNKNOWN_VERSION)):
            with self.subTest(version=version), tempfile.TemporaryDirectory(dir="/tmp") as name:
                root = Path(name)
                script = make_fixture(root, version=version)
                script.write_text("#!" + sys.executable + "\n" + script.read_text())
                script.chmod(0o700)
                with patch.dict("os.environ", {"HOME": str(root)}, clear=True):
                    verified = await claude.verify("model-a", "medium", str(script))
                self.assertEqual((verified.model, verified.reasoning_effort), ("model-a", "medium"))
                self.assertEqual(verified.version, expected)
                self.assertEqual(verified.configuration_directory, root / ".claude")
                # A changed executable is no longer an identity failure.
                script.write_text(script.read_text() + "\n# changed\n")

    async def test_failed_version_probe_is_recorded_unknown_but_owner_stop_wins(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as name:
            root = Path(name)
            script = make_fixture(root, version="ignored", version_exit=7)
            script.write_text("#!" + sys.executable + "\n" + script.read_text())
            script.chmod(0o700)
            with patch.dict("os.environ", {"HOME": str(root)}, clear=True):
                verified = await claude.verify("model-a", None, str(script))
                self.assertEqual(verified.version, UNKNOWN_VERSION)
                self.assertIsNone(verified.reasoning_effort)
                stop = Stop()
                stop.set("deadline")
                with self.assertRaises(NativeError) as caught:
                    await claude.verify("model-a", None, str(script), stop)
                self.assertEqual(caught.exception.code, "deadline")

    async def test_providers_resolve_an_explicit_path_or_path_lookup(self):
        for provider, name in ((claude, "claude"), (codex, "codex")):
            with self.subTest(provider=name), tempfile.TemporaryDirectory(dir="/tmp") as directory:
                root = Path(directory)
                script = make_fixture(root, version=name + " 9.9.9\n")
                script.write_text("#!" + sys.executable + "\n" + script.read_text())
                script.chmod(0o700)
                installed = root / "bin"
                installed.mkdir()
                (installed / name).symlink_to(script)
                empty = root / "empty"
                empty.mkdir()
                with patch.dict("os.environ", {"HOME": str(root), "PATH": str(installed)}, clear=True):
                    found = await provider.verify("model-a", "high")
                self.assertEqual(found.executable, str(script.resolve()))
                self.assertEqual(found.version, name + " 9.9.9")
                with patch.dict("os.environ", {"HOME": str(root), "PATH": str(empty)}, clear=True):
                    with self.assertRaisesRegex(NativeError, "explicit path"):
                        await provider.verify("model-a", "high")

    async def test_probe_timeout_and_explicit_stop_join_the_probe_leader(self):
        for cause in ("timeout", "cancelled", "shutdown"):
            with self.subTest(cause=cause), tempfile.TemporaryDirectory(dir="/tmp") as name:
                root = Path(name)
                script = make_fixture(root, behavior="version_stall")
                stop = Stop()
                command = CommandSpec((sys.executable, str(script), "--version"), {}, root)
                task = asyncio.create_task(probe(command, stop, timeout=.3 if cause == "timeout" else 3))
                events = await await_events(root, 2)
                await asyncio.sleep(.05)
                if cause != "timeout":
                    stop.set(cause)
                with self.assertRaises(NativeError) as caught:
                    await asyncio.wait_for(task, 3)
                self.assertEqual(caught.exception.code, "deadline" if cause == "timeout" else cause)
                self.assertFalse(alive(events[0]["pid"]))
                terminate(events[1]["escaped_child_pid"])

    async def test_version_probe_never_reaches_the_provider_setup_installer(self):
        """The runtime selects an installed CLI; the pinned installer is opt-in."""
        with tempfile.TemporaryDirectory(dir="/tmp") as name:
            root = Path(name)
            script = make_fixture(root, version="codex-cli 9.9.9\n")
            script.write_text("#!" + sys.executable + "\n" + script.read_text())
            script.chmod(0o700)
            with patch.dict("os.environ", {"HOME": str(root)}, clear=True):
                verified = await codex.verify("model-a", "medium", str(script))
        self.assertEqual((verified.provider, verified.model, verified.version),
                         ("codex", "model-a", "codex-cli 9.9.9"))
        self.assertFalse(hasattr(verified, "catalog") or hasattr(verified, "binary_sha256"))
        self.assertNotIn("setup_cli", sys.modules.get("agent_houdini.providers.codex").__dict__)

    async def test_invalid_selection_fails_before_probe(self):
        for selection, isolation in (({"provider": "unknown", "model": "model-a"}, "local"),
                                     ({"provider": "claude", "model": "model-a"}, "container"),
                                     ({"provider": "claude"}, "local")):
            with patch.object(codex, "verify", AsyncMock()) as codex_probe, \
                    patch.object(claude, "verify", AsyncMock()) as claude_probe:
                with self.assertRaises((NativeError, ValueError)):
                    await verify_provider(NativeOptions(encode(selection), isolation, Path("/tmp")))
                codex_probe.assert_not_called()
                claude_probe.assert_not_called()

    async def test_rejected_claude_startup_still_drains_and_joins_captures(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as name:
            root = Path(name)
            script = make_fixture(root)
            gate = claude.ClaudeStartup("model-a", ("submit",))
            capture = CliEventCapture(("submit",), gate)
            child = await OwnedProcess.start((sys.executable, str(script), "--capture-test"), {}, root,
                                             observer=capture, stdout_limit=0)
            result = await child.run(timeout=3)
            self.assertTrue(result.capture_failed)
            self.assertTrue(capture.startup_rejected)
            self.assertEqual(result.stderr_bytes, 200000)
            self.assertTrue(child.joined)
            with self.assertRaises(NativeError):
                await gate.wait()

    def test_diagnostics_are_utf8_bounded_and_redacted(self):
        for stderr, expected in ((b"upstream sk-private", "credential redaction"),
                                 (b"upstream unavailable", "upstream unavailable")):
            result = ProcessResult(1, "exited", b"", stderr, 0, len(stderr), False, True)
            text = capture_diagnostic(result, CliEventCapture())
            self.assertIn(expected, text)
            self.assertNotIn("sk-private", text)
        result = ProcessResult(1, "exited", b"", ("é" * 40000).encode(), 0, 80000, False, True)
        text = capture_diagnostic(result, CliEventCapture())
        self.assertLessEqual(len(text.encode()), 65536)
        self.assertNotIn("\ufffd", text)


if __name__ == "__main__":
    unittest.main()
