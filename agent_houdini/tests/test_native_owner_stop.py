# Author: Fangzhu Shen
"""Receipt-grace shutdown through actual native process, C bridge and stdio relay."""

import asyncio
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from agent_houdini.agent_transport import McpTransport
from agent_houdini.runtime_types import CleanupError
from agent_houdini.tests import claude_offline_fixture as fixture
from agent_houdini.tests.test_claude_offline_driver import Events


class OwnerStopTests(unittest.IsolatedAsyncioTestCase):
    async def run_native(self, behavior, *, cancel_on_receipt=False):
        with tempfile.TemporaryDirectory(dir="/tmp") as directory:
            root = Path(directory)
            home = root / "home"
            home.mkdir()
            (home / ".claude").mkdir()
            source = (Path(__file__).parent / "fixtures" / "claude_offline_fake.py").read_text()
            source = source.replace("import sys\n", "import sys\nimport time\n")
            submit = next(line for line in source.splitlines() if line.startswith("    call(4,"))
            source = source.replace(submit, submit + "\n" + behavior)
            executable = root / "synthetic-claude"
            executable.write_text("#!" + sys.executable + "\n" + source.split("\n", 1)[1])
            executable.chmod(0o700)
            events = Events()
            stop = fixture.Stop()

            class CancellingAccess(fixture.MeteredRequestAccess):
                """Cancel exactly as B's receipt completes, racing the owner stop."""

                async def submit(self, proposal):
                    await super().submit(proposal)
                    stop.set("deadline")

            access = CancellingAccess if cancel_on_receipt else fixture.MeteredRequestAccess
            with fixture.private_environment(home), patch.object(fixture, "Stop", return_value=stop), \
                    patch.object(fixture, "MeteredRequestAccess", access), \
                    patch("agent_houdini.agent_runtime.RECEIPT_GRACE_SECONDS", .12):
                result = await asyncio.wait_for(fixture.run_composition(executable, root, events), 5)
            self.assertFalse(any(root.glob("wa-*")), "native scratch not joined and removed")
            return result, events.items

    async def test_idle_native_after_receipt_is_intentionally_joined_without_truncation(self):
        result, events = await self.run_native("    time.sleep(120)")
        self.assertEqual(result["native"], {"outcome": "clean_exit", "submission_delivered": True, "diagnostic_code": None})
        self.assertTrue(result["receipt_received"])
        self.assertTrue(result["one_bridge"])
        self.assertTrue(result["opaque_payload_exact"])
        self.assertIn("native_owner_stop", [kind for kind, _ in events])
        self.assertNotIn("mcp_failure", [kind for kind, _ in events])

    async def test_independent_relay_eof_during_grace_remains_failure(self):
        result, events = await self.run_native("    relay.kill()\n    relay.wait()\n    time.sleep(120)")
        self.assertEqual(result["native"], {"outcome": "failed", "submission_delivered": False, "diagnostic_code": "mcp_failure"})
        self.assertNotIn("native_owner_stop", [kind for kind, _ in events])

    async def test_extra_mcp_traffic_after_receipt_is_served_then_joined(self):
        result, events = await self.run_native('    call(5, "tools/list", {})\n    time.sleep(120)')
        self.assertEqual(result["native"], {"outcome": "clean_exit", "submission_delivered": True, "diagnostic_code": None})
        self.assertIn("native_owner_stop", [kind for kind, _ in events])
        self.assertNotIn("mcp_failure", [kind for kind, _ in events])

    async def test_native_nonzero_during_grace_remains_failure(self):
        result, events = await self.run_native("    raise SystemExit(17)")
        self.assertEqual(result["native"]["outcome"], "failed")
        self.assertFalse(result["native"]["submission_delivered"])
        self.assertNotIn("native_owner_stop", [kind for kind, _ in events])

    async def test_authoritative_cancel_racing_delivered_receipt_still_wins(self):
        result, events = await self.run_native("    time.sleep(120)", cancel_on_receipt=True)
        self.assertEqual(result["native"], {"outcome": "cancelled", "submission_delivered": False, "diagnostic_code": "deadline"})
        self.assertNotIn("native_owner_stop", [kind for kind, _ in events])

    async def test_join_failure_still_dominates_intentional_owner_stop(self):
        close = McpTransport.close_and_join

        async def fail_after_physical_join(bridge):
            await close(bridge)
            raise CleanupError("synthetic joined-cleanup failure")

        with patch.object(McpTransport, "close_and_join", fail_after_physical_join):
            with self.assertRaisesRegex(CleanupError, "joined-cleanup"):
                await self.run_native("    time.sleep(120)")
