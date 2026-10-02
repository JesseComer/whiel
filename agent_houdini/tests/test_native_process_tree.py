# Author: Fangzhu Shen
"""Synthetic Unix child/pipe coverage for the C-owned native supervisor."""

import asyncio
import json
import os
from pathlib import Path
import signal
import sys
import tempfile
import unittest
from unittest.mock import patch

from agent_houdini.process_tree import OwnedProcess
from agent_houdini.runtime_types import CleanupError


FIXTURE = Path(__file__).with_name("fixtures") / "native_fixture.py"


class Stop:
    def __init__(self):
        self.event = asyncio.Event()
        self.reason = "cancelled"

    def set(self, reason="cancelled"):
        self.reason = reason
        self.event.set()

    def requested(self):
        return self.event.is_set()

    async def wait(self):
        await self.event.wait()
        return self.reason


def alive(pid):
    """C reaps every process it owns, so a surviving PID means it escaped."""
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    return True


def terminate(pid):
    """Clean up a fixture descendant that deliberately left C's process group."""
    try:
        os.kill(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def make_fixture(root, **config):
    script = root / "native.py"
    script.write_bytes(FIXTURE.read_bytes())
    script.with_suffix(".json").write_text(json.dumps({"synthetic_fixture": True,
        "events": str(root / "events"), **config}))
    return script


async def await_events(root, count):
    for _ in range(200):
        if (root / "events").exists():
            lines = (root / "events").read_text().splitlines()
            if len(lines) >= count:
                return [json.loads(line) for line in lines]
        await asyncio.sleep(.01)
    raise AssertionError("fixture did not publish its process IDs")


class NativeProcessTreeTests(unittest.IsolatedAsyncioTestCase):
    async def start(self, root, **config):
        script = make_fixture(root, **config)
        return await OwnedProcess.start((sys.executable, str(script), "--process-test"),
                                         {"PATH": "/usr/bin:/bin"}, root,
                                         prompt=b"p" * (2 * 1024 * 1024),
                                         stdout_limit=17, stderr_limit=23)

    def assert_quiet(self, pid):
        self.assertFalse(alive(pid), f"owned PID {pid} survived")

    async def test_output_capture_drains_both_streams_with_bounded_retention(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as name:
            child = await self.start(Path(name), behavior="flood")
            result = await child.run(timeout=3)
            self.assertEqual(result.stdout_bytes, 200000)
            self.assertEqual(result.stderr_bytes, 200000)
            self.assertEqual(result.stdout, b"x" * 17)
            self.assertEqual(result.stderr, b"y" * 23)
            self.assertTrue(child.joined)
            self.assertTrue(all(pipe.closed for pipe in
                                (child.process.stdin, child.process.stdout, child.process.stderr)))

    async def test_cancel_joins_the_leader_while_an_escaped_child_is_left_to_b(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as name:
            root = Path(name)
            child = await self.start(root, behavior="escaped")
            stop = Stop()
            task = asyncio.create_task(child.run(stop))
            events = await await_events(root, 2)
            await asyncio.sleep(.05)
            stop.set("deadline")
            result = await asyncio.wait_for(task, 3)
            self.assertEqual(result.reason, "deadline")
            self.assertFalse(result.prompt_written)
            self.assert_quiet(events[0]["pid"])
            # The fixture child left C's session, so C closed its pipe ends and
            # left that descendant to B's provider-neutral cleanup fallback.
            terminate(events[1]["escaped_child_pid"])

    async def test_task_cancellation_joins_before_propagating(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as name:
            root = Path(name)
            child = await self.start(root, behavior="escaped")
            task = asyncio.create_task(child.run())
            events = await await_events(root, 2)
            await asyncio.sleep(.05)
            task.cancel()
            with self.assertRaises(asyncio.CancelledError):
                await asyncio.wait_for(task, 3)
            self.assertTrue(child.joined)
            self.assert_quiet(events[0]["pid"])
            terminate(events[1]["escaped_child_pid"])

    async def test_normal_leader_exit_does_not_wait_for_an_escaped_descendant(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as name:
            root = Path(name)
            script = make_fixture(root, behavior="exit_with_child")
            child = await OwnedProcess.start((sys.executable, str(script), "--process-test"), {}, root)
            result = await asyncio.wait_for(child.run(), 3)
            events = await await_events(root, 2)
            self.assertEqual(result.returncode, 0)
            self.assertEqual(result.reason, "exited")
            self.assert_quiet(events[0]["pid"])
            terminate(events[1]["escaped_child_pid"])

    async def test_failed_join_is_distinct_and_can_be_physically_retried(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as name:
            child = await self.start(Path(name), behavior="escaped")
            with patch("agent_houdini.process_tree.CLEANUP_SECONDS", 0):
                with self.assertRaises(CleanupError):
                    await child.close_and_join(grace=False)
            await child.close_and_join(grace=False)
            self.assertTrue(child.joined)

    async def test_cleanup_error_dominates_task_cancellation(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as name:
            root = Path(name)
            child = await self.start(root, behavior="escaped")
            original = child.close_and_join

            async def failed_join(**kwargs):
                await original(**kwargs)
                raise CleanupError("synthetic failed join")

            with patch.object(child, "close_and_join", failed_join):
                task = asyncio.create_task(child.run())
                await await_events(root, 2)
                task.cancel()
                with self.assertRaisesRegex(CleanupError, "synthetic"):
                    await asyncio.wait_for(task, 3)
            self.assertTrue(child.joined)


if __name__ == "__main__":
    unittest.main()
