# Author: Fangzhu Shen
"""Operational C budgets persist across turns and never inspect B artifacts."""

from pathlib import Path
import shutil
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from agent_houdini.resource_limits import (
    AgentLimits, AgentResourceError, AgentTrafficBudget, NativeAllowance, TRAFFIC_LEGS, U64_MAX,
)


class NativeResourceTests(unittest.IsolatedAsyncioTestCase):
    def test_bare_budget_has_no_hidden_campaign_defaults(self):
        budget = AgentTrafficBudget()
        defaults = AgentLimits()
        budget.charge("prompt", defaults.traffic_bytes + 1, defaults.messages + 1)
        self.assertIsNone(budget.failure())
        self.assertIsNone(NativeAllowance().limits)

    def test_five_legs_charge_once_and_share_latched_cumulative_failure(self):
        budget = AgentTrafficBudget(AgentLimits(traffic_bytes=15, messages=5))
        for index, leg in enumerate(TRAFFIC_LEGS):
            budget.charge(leg, index + 1, 1)
        self.assertEqual(budget.usage()["bytes"], 15)
        self.assertEqual(budget.usage()["messages"], 5)
        with self.assertRaises(AgentResourceError):
            budget.charge("prompt", 1, 0)
        before = budget.usage()
        for leg in TRAFFIC_LEGS:
            with self.assertRaises(AgentResourceError):
                budget.charge(leg, 0, 0)
        self.assertEqual(budget.usage(), before)
        self.assertEqual(budget.failure(), "agent_traffic_exhausted")

    def test_invalid_charge_and_checked_u64_overflow(self):
        budget = AgentTrafficBudget()
        for leg, count, messages in (("other", 1, 0), ("prompt", -1, 0), ("prompt", True, 0),
                                      ("prompt", 0, -1), ("prompt", U64_MAX + 1, 0)):
            with self.assertRaises(ValueError):
                budget.charge(leg, count, messages)
        budget.charge("prompt", U64_MAX, U64_MAX)
        with self.assertRaises(AgentResourceError):
            budget.charge("mcp_reply", 1, 0)

    def test_native_time_is_optional_and_cumulative(self):
        self.assertIsNone(AgentLimits().native_seconds)
        self.assertIsNone(AgentLimits().thinking_tokens)
        self.assertEqual(AgentLimits(thinking_tokens=4000).thinking_tokens, 4000)
        for bad in (0, -1, 1.5, "4000"):
            with self.assertRaises(ValueError):
                AgentLimits(thinking_tokens=bad)
        budget = NativeAllowance(AgentLimits(native_seconds=1))
        budget.record_native_time(.75)
        budget.checkpoint(elapsed=.2)
        with self.assertRaises(AgentResourceError):
            budget.checkpoint(elapsed=.3)
        self.assertEqual(budget.failure(), "agent_native_time_exhausted")
        with self.assertRaises(AgentResourceError):
            budget.checkpoint()

    def test_workspace_growth_beyond_the_cap_latches_one_failure(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            guard = NativeAllowance(AgentLimits(minimum_free_bytes=0, workspace_bytes=1024))
            free = shutil.disk_usage(root).free
            guard.check_workspace(root)
            with patch("agent_houdini.resource_limits.shutil.disk_usage",
                       return_value=SimpleNamespace(free=free - 4096)):
                with self.assertRaises(AgentResourceError):
                    guard.check_workspace(root)
            self.assertEqual(guard.failure(), "agent_workspace_exhausted")
            with self.assertRaises(AgentResourceError):
                guard.check_workspace(root)

    def test_free_space_and_unreadable_scratch_fail_closed_with_one_code(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            guard = NativeAllowance(AgentLimits(minimum_free_bytes=U64_MAX))
            with self.assertRaises(AgentResourceError):
                guard.check_workspace(root)
            self.assertEqual(guard.failure(), "agent_workspace_exhausted")
            guard = NativeAllowance(AgentLimits(minimum_free_bytes=0))
            with self.assertRaises(AgentResourceError):
                guard.check_workspace(root / "missing")
            self.assertEqual(guard.failure(), "agent_workspace_exhausted")

    def test_bare_allowance_never_observes_the_filesystem(self):
        with patch("agent_houdini.resource_limits.shutil.disk_usage") as usage:
            NativeAllowance().check_workspace(Path("/nonexistent-scratch"))
        usage.assert_not_called()


if __name__ == "__main__":
    unittest.main()
