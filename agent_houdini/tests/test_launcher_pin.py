# Author: Fangzhu Shen
"""Agent pin ownership and unchanged safe-parent checks."""

from pathlib import Path
import shutil
import tempfile
import unittest

from agent_houdini import setup_cli


class AgentPinTests(unittest.TestCase):
    def test_c_lock_is_self_contained_without_an_outside_duplicate(self):
        original = setup_cli.REPO / setup_cli.LOCK
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            target = root / setup_cli.LOCK
            target.parent.mkdir(parents=True)
            shutil.copyfile(original, target)
            actual, digest = setup_cli.load_lock(root, setup_cli.TARGET)
            self.assertEqual(digest, setup_cli.sha256(original.read_bytes()))
            self.assertEqual(actual["version"], "0.148.0")
            self.assertFalse((root / "toolchain").exists())

    def test_c_lock_and_each_c_parent_refuse_links(self):
        for selected in ("agent_houdini", "agent_houdini/toolchain", str(setup_cli.LOCK)):
            with tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary).resolve()
                target = root / setup_cli.LOCK
                target.parent.mkdir(parents=True)
                shutil.copyfile(setup_cli.REPO / setup_cli.LOCK, target)
                path = root / selected
                outside = root / "outside"
                path.rename(outside)
                path.symlink_to(outside)
                with self.assertRaises(setup_cli.SetupError):
                    setup_cli.load_lock(root, setup_cli.TARGET)


if __name__ == "__main__":
    unittest.main()
