# Author: Fangzhu Shen
"""Public C entry/configuration with injected dependencies and real local signals."""
import asyncio
import contextlib
from dataclasses import dataclass
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import AsyncMock, Mock, patch

from agent_houdini.launcher import (
    EndpointOptions, build_endpoint_command, endpoint_main, main, native_options,
    parse_campaign_arguments, parse_endpoint_arguments,
)
from agent_houdini.tests.test_native_process_tree import alive, terminate
from agent_houdini.resource_limits import AgentLimits, AgentResourceError
from agent_houdini.runtime_types import CleanupError


ENTRY = Path(__file__).resolve().parents[1] / "__main__.py"
FIXTURE = Path(__file__).with_name("fixtures") / "native_fixture.py"


@dataclass
class Identity:
    schema_version: int = 1
    model: str = "model-a"
    version: str = "fixture-cli 9.9.9"


class LauncherEntryTests(unittest.TestCase):
    def test_endpoint_round_trip_keeps_provider_limits_and_mode_in_c(self):
        with tempfile.TemporaryDirectory() as name:
            options = parse_campaign_arguments([
                "--verifier", sys.executable, "--provider", "claude", "--model", "model-a",
                "--reasoning-effort", "max", "--provider-cli", "/synthetic/native with spaces",
                "--agent-traffic-bytes", "0", "--agent-messages", "7", "--agent-native-seconds", "1.5",
                "--agent-log-parent", name, "--", "--input", "1"])
            expected = EndpointOptions(options.native, options.limits, options.log_parent)
            command = build_endpoint_command(expected)
            self.assertEqual(command[2], "endpoint")
            self.assertNotIn("campaign", command)
            self.assertEqual(parse_endpoint_arguments(command[3:]), expected)
            self.assertTrue(Path(command[0]).is_absolute())
            self.assertTrue(Path(command[1]).is_absolute())

    def test_help_no_proposer_and_invalid_config_do_not_probe_or_create_logs(self):
        verify, execute = AsyncMock(side_effect=AssertionError("native verification")), Mock(return_value=0)
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()), \
             patch("agent_houdini.launcher._log_directory", side_effect=AssertionError("log creation")):
            for args in (["--help"], ["campaign", "run", "--help"], ["endpoint", "--help"]):
                self.assertEqual(main(args, verify=verify, execute=execute), 0)
            self.assertEqual(main(["campaign", "run", "--verifier", sys.executable,
                                   "--no-proposer", "--", "--input", "1"], verify=verify, execute=execute), 0)
            self.assertEqual(execute.call_args.args[1][-1], "--no-proposer")
            self.assertEqual(main(["campaign", "run", "--verifier", sys.executable, "--model", "model-a",
                                   "--", "--help"], verify=verify, execute=execute), 0)
            for own in ([], ["--model", "with\ncontrol"], ["--agent-messages", "-1"],
                        ["--agent-native-seconds", "nan"], ["--agent-workspace-bytes", "-1"],
                        ["--no-proposer", "--agent-messages", "1"],
                        ["--agent-log-parent", "/nonexistent/whiel-agent-log-parent"],
                        ["--agent-scratch-parent", "/nonexistent/whiel-agent-scratch-parent"]):
                self.assertEqual(main(["campaign", "run", "--verifier", sys.executable, *own],
                                      verify=verify, execute=execute), 2)
        verify.assert_not_called()

    def test_launch_preflight_precedes_exec_and_private_provenance_log(self):
        with tempfile.TemporaryDirectory() as name:
            verify, execute = AsyncMock(return_value=Identity()), Mock(return_value=17)
            previous = signal.getsignal(signal.SIGINT)
            with contextlib.redirect_stderr(io.StringIO()):
                status = main(["campaign", "run", "--verifier", sys.executable, "--provider", "claude",
                               "--model", "model-a", "--agent-log-parent", name,
                               "--", "--input", "1"], verify=verify, execute=execute)
            self.assertEqual(status, 17)
            self.assertIs(signal.getsignal(signal.SIGINT), previous)
            verify.assert_awaited_once()
            command = execute.call_args.args[1]
            self.assertEqual(command[:5], (sys.executable, "campaign", "run", "--input", "1"))
            self.assertIn("endpoint", command)
            logs = list(Path(name).glob("whiel-agent-*/launcher.jsonl"))
            self.assertEqual(len(logs), 1)
            self.assertEqual(logs[0].stat().st_mode & 0o777, 0o600)
            self.assertEqual(logs[0].parent.stat().st_mode & 0o777, 0o700)
            fields = json.loads(logs[0].read_text())["fields"]
            self.assertEqual(fields["native_identity"]["version"], "fixture-cli 9.9.9")
            self.assertEqual(fields["selection"]["model"], "model-a")
            self.assertEqual(fields["agent_limits"]["traffic_bytes"], AgentLimits().traffic_bytes)

    def test_agent_log_dir_is_created_fresh_and_handed_to_the_endpoint(self):
        with tempfile.TemporaryDirectory() as name:
            verify, execute = AsyncMock(return_value=Identity()), Mock(return_value=0)
            chosen = Path(name) / "run" / "agent"
            (Path(name) / "run").mkdir()
            with contextlib.redirect_stderr(io.StringIO()):
                status = main(["campaign", "run", "--verifier", sys.executable, "--provider", "codex",
                               "--model", "model-a", "--agent-log-dir", str(chosen),
                               "--", "--input", "1"], verify=verify, execute=execute)
            self.assertEqual(status, 0)
            self.assertTrue((chosen / "launcher.jsonl").is_file())
            self.assertEqual(chosen.stat().st_mode & 0o777, 0o700)
            self.assertEqual(list(Path(name).glob("whiel-agent-*")), [])
            command = execute.call_args.args[1]
            self.assertIn("--agent-log-parent", command)
            self.assertEqual(command[command.index("--agent-log-parent") + 2], str(chosen.resolve()))
            # An existing directory is refused before any native probe or exec.
            verify.reset_mock()
            execute.reset_mock()
            with contextlib.redirect_stderr(io.StringIO()):
                status = main(["campaign", "run", "--verifier", sys.executable, "--provider", "codex",
                               "--model", "model-a", "--agent-log-dir", str(chosen),
                               "--", "--input", "1"], verify=verify, execute=execute)
            self.assertEqual(status, 2)
            verify.assert_not_awaited()
            execute.assert_not_called()
            for arguments in (["--agent-log-dir", str(Path(name) / "missing-parent" / "agent")],
                              ["--agent-log-dir", str(Path(name) / "fresh"), "--agent-log-parent", name],
                              ["--no-proposer", "--agent-log-dir", str(Path(name) / "fresh")]):
                with contextlib.redirect_stderr(io.StringIO()):
                    status = main(["campaign", "run", "--verifier", sys.executable, "--model", "model-a",
                                   *arguments, "--", "--input", "1"], verify=verify, execute=execute)
                self.assertEqual(status, 2, arguments)
                self.assertFalse((Path(name) / "fresh").exists())
            verify.assert_not_awaited()

    def test_endpoint_dispatch_never_invokes_campaign_or_native_preflight(self):
        endpoint = AsyncMock(return_value=130)
        self.assertEqual(main(["endpoint", "--provider", "claude", "--model", "model-a"], endpoint_runner=endpoint,
                              verify=AsyncMock(side_effect=AssertionError("preflight")),
                              execute=Mock(side_effect=AssertionError("campaign"))), 130)
        endpoint.assert_awaited_once()
        self.assertEqual(json.loads(endpoint.call_args.args[0].native.selection_json)["provider"], "claude")

    def test_endpoint_explicit_budget_and_log_lifetime_are_injected(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve()
            factory = Mock()

            async def run(native, budget, events, *, runner_factory, records):
                self.assertIs(runner_factory, factory)
                self.assertEqual(records.retention, "events")
                self.assertTrue(records.directory.name.startswith("input-"))
                self.assertEqual(native.isolation, "local")
                self.assertIsNone(budget.failure())
                with self.assertRaises(AgentResourceError):
                    budget.charge("prompt", 1, 1)
                events.emit("fixture", {"bytes": 1})
                return 0

            options = EndpointOptions(native_options(model="model-a"), AgentLimits(traffic_bytes=0), root)
            self.assertEqual(asyncio.run(endpoint_main(options, run_endpoint=run, runner_factory=factory)), 0)
            records = list(root.glob("input-*/events.jsonl"))
            self.assertEqual(len(records), 1)
            self.assertEqual([json.loads(line)["kind"] for line in records[0].read_text().splitlines()],
                             ["endpoint_configuration", "fixture"])

    def test_real_cleanup_failure_dominates_preflight_interrupt(self):
        async def verify(_, stop):
            stop.set("interrupted")
            raise CleanupError("synthetic owned cleanup failed")

        with contextlib.redirect_stderr(io.StringIO()) as stderr:
            self.assertEqual(main(["campaign", "run", "--verifier", sys.executable, "--model", "model-a"],
                                  verify=verify, execute=Mock(side_effect=AssertionError("exec"))), 2)
        self.assertIn("cleanup failed", stderr.getvalue())

    def test_standalone_entry_bootstraps_own_package_from_private_cwd(self):
        with tempfile.TemporaryDirectory() as name:
            result = subprocess.run([sys.executable, str(ENTRY), "endpoint", "--help"], cwd=name,
                                    env={"PATH": os.defpath}, stdin=subprocess.DEVNULL,
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"agent_houdini endpoint", result.stdout)

    def test_real_setup_failure_stops_before_public_verifier_and_logs(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as name:
            root = Path(name).resolve()
            executable = root / "native.py"
            executable.write_text("#!" + sys.executable + "\n" + FIXTURE.read_text())
            executable.chmod(0o700)
            executable.with_suffix(".json").write_text(json.dumps({
                "synthetic_fixture": True, "events": str(root / "events")}))
            verifier = root / "verifier"
            marker = root / "verifier-started"
            verifier.write_text("#!" + sys.executable + "\nfrom pathlib import Path\nPath(" + repr(str(marker))
                                + ").write_text('unexpected start')\n")
            verifier.chmod(0o700)
            result = subprocess.run([sys.executable, str(ENTRY), "campaign", "run", "--verifier", str(verifier),
                                     "--provider", "claude", "--model", "model-a",
                                     "--provider-cli", str(root / "absent-cli"),
                                     "--agent-log-parent", str(root), "--", "--input", "1"],
                                    cwd=root, env={"PATH": os.defpath, "HOME": str(root)},
                                    stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE, timeout=5)
            self.assertEqual(result.returncode, 2, result.stderr)
            self.assertFalse(marker.exists())
            self.assertEqual(list(root.glob("whiel-agent-*")), [])

    def test_real_sigint_joins_stalled_probe_and_detached_descendant_before_130(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as name:
            root = Path(name).resolve()
            executable = root / "native.py"
            executable.write_text("#!" + sys.executable + "\n" + FIXTURE.read_text())
            executable.chmod(0o700)
            events = root / "events"
            executable.with_suffix(".json").write_text(json.dumps({
                "synthetic_fixture": True, "behavior": "version_stall", "events": str(events)}))
            environment = {"PATH": os.defpath, "HOME": str(root), "CLAUDE_CONFIG_DIR": str(root / ".claude")}
            child = subprocess.Popen([sys.executable, str(ENTRY), "campaign", "run", "--verifier", sys.executable,
                                      "--provider", "claude", "--model", "model-a",
                                      "--provider-cli", str(executable),
                                      "--agent-log-parent", str(root), "--", "--input", "1"],
                                     cwd=root, env=environment, stdin=subprocess.DEVNULL,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            identities = []
            try:
                until = time.monotonic() + 5
                while time.monotonic() < until:
                    if events.exists() and len(events.read_text().splitlines()) >= 2:
                        break
                    if child.poll() is not None:
                        self.fail("launcher stopped before synthetic probe startup: " + str(child.communicate()))
                    time.sleep(.01)
                rows = [json.loads(line) for line in events.read_text().splitlines()]
                identities = [next(iter(row.values())) for row in rows[:2]]
                self.assertTrue(all(alive(pid) for pid in identities))
                child.send_signal(signal.SIGINT)
                stdout, stderr = child.communicate(timeout=5)
                self.assertEqual(child.returncode, 130, (stdout, stderr))
                # The probe leader is joined; its deliberately escaped child is
                # B's provider-neutral cleanup fallback, not C's to chase.
                self.assertFalse(alive(identities[0]))
                self.assertEqual(list(root.glob("whiel-agent-*")), [])
            finally:
                if child.poll() is None:
                    child.kill()
                child.communicate(timeout=5)
                for pid in identities:
                    terminate(pid)


if __name__ == "__main__":
    unittest.main()
