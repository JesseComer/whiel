# Author: Fangzhu Shen
"""Skill decoding, stable snapshots and descriptor-based bounded loading."""

from dataclasses import FrozenInstanceError
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import json

from agent_houdini.skills import (
    MAX_SKILL_BYTES, MAX_SKILL_CATALOG_BYTES, MAX_SKILL_COUNT, SKILLS_FILE_ENV, SkillCatalog,
)


ROOT = Path(__file__).resolve().parents[2]
LIBRARY = ROOT / "agent_houdini" / "skills" / "v1"


def write_library(directory, skills):
    """`skills`: {id: (description, applies, text)}; writes index.json and files."""
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    index = []
    for identifier, (description, applies, text) in skills.items():
        (directory / f"{identifier}.md").write_text(text, encoding="utf-8")
        index.append({"id": identifier, "description": description, "applies": applies,
                      "file": f"{identifier}.md"})
    (directory / "index.json").write_text(json.dumps({"skills": index}), encoding="utf-8")
    return directory


class LibraryTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="c-skills-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def test_a_directory_library_is_indexed_served_and_frozen(self):
        directory = write_library(self.root / "lib", {
            "zeta": ("Last by name.", "any loop", "# Zeta\n\nbody ζ\n"),
            "alpha": ("First by name.", "", "# Alpha\n\nbody α\n")})
        catalog = SkillCatalog.from_path(directory)
        self.assertTrue(catalog.enabled())
        self.assertEqual(catalog.ids(), ["alpha", "zeta"])
        self.assertEqual(catalog.index(), [
            {"id": "alpha", "description": "First by name.", "applies": ""},
            {"id": "zeta", "description": "Last by name.", "applies": "any loop"}])
        content, is_error = catalog.get({"id": "zeta"})
        self.assertFalse(is_error)
        self.assertEqual(content, {"id": "zeta", "content": {
            "description": "Last by name.", "applies": "any loop", "text": "# Zeta\n\nbody ζ\n"}})
        self.assertEqual(catalog.get({"id": "missing"})[0]["error"]["code"], "unknown_skill")
        # Later edits do not reach the snapshot; the handoff round-trips it.
        (directory / "zeta.md").write_text("changed", encoding="utf-8")
        self.assertEqual(catalog.get({"id": "zeta"})[0]["content"]["text"], "# Zeta\n\nbody ζ\n")
        again = SkillCatalog.from_handoff_json(catalog.handoff_json())
        self.assertEqual(again.get({"id": "zeta"}), catalog.get({"id": "zeta"}))
        self.assertEqual(SkillCatalog.from_path(directory).get({"id": "zeta"})[0]["content"]["text"], "changed")
        with mock.patch.dict(os.environ, {SKILLS_FILE_ENV: str(directory)}):
            self.assertEqual(SkillCatalog.from_file_environment().ids(), ["alpha", "zeta"])

    def test_library_bounds_and_shapes_are_enforced(self):
        big = write_library(self.root / "big", {"huge": ("d", "", "x" * (MAX_SKILL_BYTES + 1))})
        with self.assertRaisesRegex(ValueError, "exceeds"):
            SkillCatalog.from_directory(big)
        many = write_library(self.root / "many", {f"s{index}": ("d", "", "t") for index in range(MAX_SKILL_COUNT + 1)})
        with self.assertRaisesRegex(ValueError, "at most"):
            SkillCatalog.from_directory(many)
        for broken, message in (
                ({"skills": [{"id": "a", "description": "d", "file": "../escape.md"}]}, "Markdown file beside"),
                ({"skills": [{"id": "bad id", "description": "d", "file": "a.md"}]}, "short names"),
                ({"skills": [{"id": "a", "description": "d", "file": "a.md"},
                             {"id": "a", "description": "d", "file": "a.md"}]}, "repeats"),
                ({"skills": [{"id": "a", "description": 7, "file": "a.md"}]}, "description"),
                ({"skills": {}}, "at most"), ([], "at most")):
            directory = self.root / "broken"
            directory.mkdir(exist_ok=True)
            (directory / "a.md").write_text("text", encoding="utf-8")
            (directory / "index.json").write_text(json.dumps(broken), encoding="utf-8")
            with self.subTest(broken=broken), self.assertRaisesRegex(ValueError, message):
                SkillCatalog.from_directory(directory)
        missing = self.root / "missing-file"
        missing.mkdir()
        (missing / "index.json").write_text(json.dumps({"skills": [{"id": "a", "description": "d", "file": "a.md"}]}))
        with self.assertRaises((ValueError, OSError)):
            SkillCatalog.from_directory(missing)
        (missing / "index.json").write_text(" " * (MAX_SKILL_CATALOG_BYTES + 1))
        with self.assertRaisesRegex(ValueError, "invalid or oversized C skill index"):
            SkillCatalog.from_directory(missing)

    def test_the_hand_written_library_loads_and_every_skill_is_a_procedure(self):
        catalog = SkillCatalog.from_directory(LIBRARY)
        index = catalog.index()
        self.assertEqual(catalog.ids(), [
            "bound-and-frame", "delta-coupling", "ladder-strategy",
            "lagged-closure", "mutual-simulation", "reading-a-countermodel",
        ])
        for entry in index:
            self.assertTrue(entry["description"], entry["id"])
            text = catalog.get({"id": entry["id"]})[0]["content"]["text"]
            self.assertTrue(text.startswith("# "), entry["id"])
        for identifier in ("ladder-strategy", "reading-a-countermodel"):
            text = catalog.get({"id": identifier})[0]["content"]["text"]
            for heading in ("**When it applies.**", "**Which query tests it.**", "**How to read the next failure.**"):
                self.assertIn(heading, text, identifier)
        for identifier in ("phase-flags", "example-closure-other-side"):
            self.assertFalse((LIBRARY / f"{identifier}.md").exists())
            content, is_error = catalog.get({"id": identifier})
            self.assertTrue(is_error)
            self.assertEqual(content["error"]["code"], "unknown_skill")
        listed = json.loads((LIBRARY / "index.json").read_text(encoding="utf-8"))["skills"]
        self.assertTrue(all("provenance" in item for item in listed))


class SkillTests(unittest.TestCase):
    def test_disabled_empty_and_errors_match_rust(self):
        disabled = SkillCatalog()
        self.assertFalse(disabled.enabled())
        self.assertEqual(disabled.handoff_json(), "null")
        self.assertFalse(SkillCatalog.from_handoff_json("null").enabled())
        self.assertEqual(disabled.get({"id": "guide"}),
                         ({"error": {"code": "skill_disabled", "message": "Local skills are disabled."}}, True))
        enabled = SkillCatalog.from_json(b"{}")
        self.assertTrue(enabled.enabled())
        self.assertEqual(enabled.ids(), [])
        self.assertEqual(enabled.get({"id": "missing"})[0]["error"],
                         {"code": "unknown_skill", "message": "No local skill has that ID."})
        for args in [{}, {"id": 1}, {"id": "x", "extra": True}, []]:
            self.assertEqual(enabled.get(args),
                             ({"error": {"code": "invalid_arguments", "message": "Expected exactly one string id."}}, True))

    def test_strict_json_and_size_errors(self):
        for data in [b"null", b"[]", b'{"":1}', b'{"a":1,"a":2}', b'{"a":NaN}',
                     b'{"a":"\\ud800"}', b" " * (MAX_SKILL_CATALOG_BYTES + 1)]:
            with self.subTest(data=data[:50]), self.assertRaises(ValueError):
                SkillCatalog.from_json(data)
        with self.assertRaisesRegex(ValueError, "C skill IDs must be nonempty"):
            SkillCatalog.from_json(b'{"":null}')
        with self.assertRaisesRegex(ValueError, "C skill catalog must map nonempty IDs"):
            SkillCatalog.from_json(b"[]")
        exact = b'{"a":"' + b"x" * (MAX_SKILL_CATALOG_BYTES - 8) + b'"}'
        self.assertEqual(len(exact), MAX_SKILL_CATALOG_BYTES)
        self.assertEqual(len(SkillCatalog.from_json(exact).handoff_json()), MAX_SKILL_CATALOG_BYTES)

    def test_file_changes_and_returned_content_cannot_mutate_prior_snapshot(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "skills.json"
            path.write_bytes(b'{"z":[1],"a":{"text":"before"}}')
            with mock.patch.dict(os.environ, {SKILLS_FILE_ENV: str(path)}):
                before = SkillCatalog.from_file_environment()
            path.write_bytes(b'{"a":{"text":"after"}}')
            after = SkillCatalog.from_file(path)
            self.assertEqual(before.ids(), ["a", "z"])
            content, is_error = before.get({"id": "a"})
            self.assertFalse(is_error)
            content["content"]["text"] = "caller mutation"
            self.assertEqual(before.get({"id": "a"})[0]["content"]["text"], "before")
            self.assertEqual(after.get({"id": "a"})[0]["content"]["text"], "after")
            transported = SkillCatalog.from_handoff_json(before.handoff_json())
            self.assertEqual(transported.get({"id": "a"}), before.get({"id": "a"}))
            with self.assertRaises(FrozenInstanceError):
                before._content = b"{}"

    def test_oversized_file_is_read_only_through_the_fixed_bound(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "large.json"
            path.write_bytes(b" " * (MAX_SKILL_CATALOG_BYTES * 4))
            with mock.patch("agent_houdini.skills.os.read", wraps=os.read) as reads:
                with self.assertRaisesRegex(ValueError, "invalid or oversized C skill catalog JSON"):
                    SkillCatalog.from_file(path)
                self.assertEqual(sum(call.args[1] for call in reads.call_args_list),
                                 MAX_SKILL_CATALOG_BYTES + 1)

    @unittest.skipUnless(hasattr(os, "mkfifo"), "requires POSIX FIFO")
    def test_fifo_without_writer_is_rejected_in_a_bounded_child(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "skills.fifo"
            os.mkfifo(path, 0o600)
            source = (
                "import sys; from agent_houdini.skills import SkillCatalog\n"
                "try: SkillCatalog.from_file(sys.argv[1])\n"
                "except ValueError as error:\n"
                " assert str(error) == 'C skill catalog must be a regular file'\n"
                " print('loader executed')\n"
                "else: raise AssertionError('FIFO was accepted')\n"
            )
            result = subprocess.run([sys.executable, "-c", source, str(path)], cwd=ROOT,
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=3)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, b"loader executed\n")


if __name__ == "__main__":
    unittest.main()
