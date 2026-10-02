# Author: Fangzhu Shen
"""Shared C runtime values, without starting providers or API connections."""

from pathlib import Path
import unittest

from agent_houdini.runtime_types import McpLaunch


class RuntimeTypesTests(unittest.TestCase):
    def test_launch_environment_is_a_private_immutable_snapshot(self):
        source = {"C_RELAY_TOKEN": "first"}
        launch = McpLaunch(("python", "relay.py"), source, (Path("relay.py"),))
        source["C_RELAY_TOKEN"] = "changed"
        self.assertEqual(dict(launch.environment), {"C_RELAY_TOKEN": "first"})
        with self.assertRaises(TypeError):
            launch.environment["C_RELAY_TOKEN"] = "changed"


if __name__ == "__main__":
    unittest.main()
