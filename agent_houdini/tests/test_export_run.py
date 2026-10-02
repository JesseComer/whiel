# Author: Fangzhu Shen
"""The run-directory exporter: what it copies, what it refuses, and why."""

import getpass
import io
from pathlib import Path
import socket
import tempfile
import unittest

from agent_houdini.export_run import (
    check_only, export_run, find_hits, is_excluded, main, unsafe_markers,
)


def write(root, relative, content):
    path = Path(root) / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    if isinstance(content, bytes):
        path.write_bytes(content)
    else:
        path.write_text(content, encoding="utf-8")
    return path


class UnsafeMarkersTests(unittest.TestCase):
    def test_markers_are_read_from_this_process_not_hard_coded(self):
        markers = unsafe_markers()
        self.assertIn(getpass.getuser(), markers)
        self.assertIn(str(Path.home()), markers)
        self.assertIn(socket.gethostname(), markers)
        self.assertIn("/Users/", markers)
        self.assertIn("/home/", markers)
        self.assertIn("/tmp/", markers)
        self.assertIn("/private/", markers)
        self.assertIn("/var/folders/", markers)

    def test_native_files_are_recognized_by_name_alone(self):
        self.assertTrue(is_excluded(Path("agent/Example0001/request-1/native-stdout.jsonl")))
        self.assertTrue(is_excluded(Path("native-debug.txt")))
        self.assertFalse(is_excluded(Path("agent/Example0001/request-1/submissions.jsonl")))
        self.assertFalse(is_excluded(Path("verifier/Example0001/result.json")))


class FindHitsTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def test_a_clean_tree_has_no_hits(self):
        write(self.root, "verifier/Example0001/result.json", '{"status": "valid"}')
        write(self.root, "agent/Example0001/request-1/prompt.txt", "the task and its clauses\n")
        self.assertEqual(find_hits(self.root, skip_excluded=True), [])
        self.assertEqual(find_hits(self.root, skip_excluded=False), [])

    def test_a_text_hit_names_its_line_and_is_not_redacted(self):
        write(self.root, "run.json", '{\n  "cwd": "/Users/example-user/checkout"\n}\n')
        hits = find_hits(self.root, skip_excluded=True)
        self.assertEqual(len(hits), 1)
        relative, marker, location, excerpt = hits[0]
        self.assertEqual(str(relative), "run.json")
        self.assertEqual(marker, "/Users/")
        self.assertEqual(location, "line 2")
        self.assertIn("/Users/example-user/checkout", excerpt)

    def test_a_binary_hit_names_a_byte_offset(self):
        payload = b"\x00\x01" + b"prefix-" + str(Path.home()).encode() + b"-suffix\xff\xfe"
        write(self.root, "verifier/Example0001/artifacts/witness.bin", payload)
        hits = find_hits(self.root, skip_excluded=True)
        markers = {marker for _, marker, _, _ in hits}
        self.assertIn(str(Path.home()), markers)
        locations = {location for _, _, location, _ in hits}
        self.assertTrue(any(location.startswith("byte offset") for location in locations))

    def test_skip_excluded_leaves_out_native_files_only(self):
        write(self.root, "agent/Example0001/request-1/native-stdout.jsonl",
             '{"cwd": "/tmp/native-only"}')
        write(self.root, "agent/Example0001/request-1/submissions.jsonl",
             '{"payload": "/tmp/submitted"}')
        skipped = {str(relative) for relative, *_ in find_hits(self.root, skip_excluded=True)}
        self.assertEqual(skipped, {"agent/Example0001/request-1/submissions.jsonl"})
        both = {str(relative) for relative, *_ in find_hits(self.root, skip_excluded=False)}
        self.assertEqual(both, {"agent/Example0001/request-1/submissions.jsonl",
                                "agent/Example0001/request-1/native-stdout.jsonl"})

    def test_symlinks_are_not_scanned_or_followed(self):
        write(self.root, "verifier/Example0001/result.json", '{"status": "valid"}')
        example = self.root / "examples" / "Example0001"
        example.mkdir(parents=True)
        (example / "verifier").symlink_to("../../verifier/Example0001", target_is_directory=True)
        self.assertEqual(find_hits(self.root, skip_excluded=True), [])


class ExportRunTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.run_dir = self.root / "run"
        self.dest = self.root / "export"

    def test_export_copies_everything_but_native_files(self):
        write(self.run_dir, "run.json", '{"status": "finished"}')
        write(self.run_dir, "verifier/Example0001/result.json", '{"status": "valid"}')
        write(self.run_dir, "agent/Example0001/request-1/submissions.jsonl", '{"submission": 1}')
        write(self.run_dir, "agent/Example0001/request-1/native-stdout.jsonl", '{"type": "assistant"}')
        write(self.run_dir, "agent/Example0001/request-1/native-stderr.txt", "warning\n")
        out, err = io.StringIO(), io.StringIO()
        status = export_run(self.run_dir, self.dest, out=out, err=err)
        self.assertEqual(status, 0, err.getvalue())
        self.assertTrue((self.dest / "run.json").is_file())
        self.assertTrue((self.dest / "verifier/Example0001/result.json").is_file())
        self.assertTrue((self.dest / "agent/Example0001/request-1/submissions.jsonl").is_file())
        self.assertFalse((self.dest / "agent/Example0001/request-1/native-stdout.jsonl").exists())
        self.assertFalse((self.dest / "agent/Example0001/request-1/native-stderr.txt").exists())
        self.assertIn(str(self.dest), out.getvalue())

    def test_export_preserves_the_digests_relative_symlinks(self):
        write(self.run_dir, "verifier/Example0001/result.json", '{"status": "valid"}')
        write(self.run_dir, "agent/Example0001/events.jsonl", "{}")
        example = self.run_dir / "examples" / "Example0001"
        example.mkdir(parents=True)
        (example / "verifier").symlink_to("../../verifier/Example0001", target_is_directory=True)
        (example / "agent").symlink_to("../../agent/Example0001", target_is_directory=True)
        status = export_run(self.run_dir, self.dest, out=io.StringIO(), err=io.StringIO())
        self.assertEqual(status, 0)
        copied = self.dest / "examples" / "Example0001" / "verifier"
        self.assertTrue(copied.is_symlink())
        self.assertTrue((self.dest / "examples" / "Example0001" / "verifier" / "result.json").is_file())

    def test_export_refuses_and_leaves_no_dest_on_an_unsafe_hit(self):
        write(self.run_dir, "run.json", '{"cwd": "/home/example-user/checkout"}')
        out, err = io.StringIO(), io.StringIO()
        status = export_run(self.run_dir, self.dest, out=out, err=err)
        self.assertEqual(status, 1)
        self.assertFalse(self.dest.exists())
        self.assertIn("unsafe", err.getvalue())
        self.assertIn("/home/", err.getvalue())

    def test_export_refuses_a_destination_that_already_exists(self):
        write(self.run_dir, "run.json", "{}")
        self.dest.mkdir()
        status = export_run(self.run_dir, self.dest, out=io.StringIO(), err=io.StringIO())
        self.assertEqual(status, 2)

    def test_export_refuses_a_missing_run_directory(self):
        status = export_run(self.root / "absent", self.dest, out=io.StringIO(), err=io.StringIO())
        self.assertEqual(status, 2)


class CheckOnlyTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def test_reports_nothing_would_block_a_clean_run(self):
        write(self.root, "verifier/Example0001/result.json", '{"status": "valid"}')
        out = io.StringIO()
        self.assertEqual(check_only(self.root, out=out), 0)
        self.assertIn("nothing would block an export", out.getvalue())

    def test_ignores_a_hit_confined_to_a_native_file(self):
        write(self.root, "agent/Example0001/request-1/native-stdout.jsonl",
             '{"cwd": "' + str(Path.home()) + '"}')
        out = io.StringIO()
        self.assertEqual(check_only(self.root, out=out), 0)

    def test_reports_a_hit_outside_a_native_file(self):
        write(self.root, "run.json", '{"cwd": "' + str(Path.home()) + '"}')
        out = io.StringIO()
        self.assertEqual(check_only(self.root, out=out), 1)
        self.assertIn("run.json", out.getvalue())
        self.assertIn(str(Path.home()), out.getvalue())


class MainTests(unittest.TestCase):
    def test_check_only_rejects_extra_positional_arguments(self):
        with self.assertRaises(SystemExit):
            main(["--check-only", "a", "b"])

    def test_missing_destination_is_refused(self):
        with self.assertRaises(SystemExit):
            main(["a"])


if __name__ == "__main__":
    unittest.main()
