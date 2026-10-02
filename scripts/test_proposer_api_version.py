"""The API version gate against isolated, real Git fixture repositories."""

import importlib.util
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("check_proposer_api_version.py")
SPEC = importlib.util.spec_from_file_location("proposer_api_version", SCRIPT)
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)


class ApiVersionGateTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="whiel-api-version-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.git("init", "--quiet")
        self.git("config", "user.name", "Version Gate Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.write("README.md", "fixture\n")
        self.initial = self.commit()
        self.version("1.0.0")
        self.write(f"{GATE.API_DIRECTORY}/mod.rs", "pub mod version;\n")
        self.docs("1.0.0")
        self.base = self.commit()

    def git(self, *args):
        return GATE.git(self.root, *args).decode().strip()

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def commit(self):
        self.git("add", "--all")
        self.git("commit", "--quiet", "-m", "fixture")
        return self.git("rev-parse", "HEAD")

    def version(self, version):
        self.write(GATE.VERSION_FILE, f'pub const API_VERSION: &str = "{version}";\n')

    def docs(self, version, detail="Updated API contract."):
        self.write(GATE.DOCUMENTATION, f"# Proposer API\n\n### {version} — contract\n\n{detail}\n")

    def bump(self, version="1.0.1"):
        self.version(version)
        self.docs(version)

    def accepts(self, base=None):
        self.assertTrue(GATE.check(self.root, base or self.base).startswith("PASS:"))

    def rejects(self, pattern, base=None):
        with self.assertRaisesRegex(GATE.VersionGateError, pattern):
            GATE.check(self.root, base or self.base)

    def test_no_api_changes_need_no_update(self):
        self.write("Whiel/Unrelated.lean", "-- backend edit\n")
        self.write("agent_houdini/unrelated.py", "# proposer edit\n")
        self.accepts()

    def test_new_api_directory_accepts_initial_version(self):
        self.accepts(self.initial)

    def test_untracked_initial_api_and_docs_are_included(self):
        self.git("reset", "--mixed", self.initial)
        self.accepts(self.initial)

    def test_edit_requires_bump(self):
        self.write(f"{GATE.API_DIRECTORY}/mod.rs", "pub mod version; // changed\n")
        self.rejects("strictly newer")
        self.bump()
        self.accepts()

    def test_staged_change_is_checked(self):
        self.write(f"{GATE.API_DIRECTORY}/mod.rs", "// staged change\n")
        self.git("add", GATE.API_DIRECTORY)
        self.rejects("strictly newer")

    def test_explicit_base_includes_committed_changes(self):
        self.write(f"{GATE.API_DIRECTORY}/mod.rs", "// committed change\n")
        self.commit()
        self.rejects("strictly newer")
        self.bump()
        self.commit()
        self.accepts()

    def test_untracked_addition_requires_bump(self):
        self.write(f"{GATE.API_DIRECTORY}/new file.rs", "// new\n")
        self.rejects("strictly newer")
        self.bump()
        self.accepts()

    def test_ignored_untracked_addition_is_not_a_bypass(self):
        self.write(".gitignore", "ignored.rs\n")
        self.write(f"{GATE.API_DIRECTORY}/ignored.rs", "// new\n")
        self.rejects("strictly newer")

    def test_deletion_requires_bump(self):
        (self.root / GATE.API_DIRECTORY / "mod.rs").unlink()
        self.rejects("strictly newer")
        self.bump()
        self.accepts()

    def test_rename_outside_directory_requires_bump(self):
        self.git("mv", f"{GATE.API_DIRECTORY}/mod.rs", "outside.rs")
        self.rejects("strictly newer")
        self.bump()
        self.accepts()

    def test_unstaged_rename_outside_directory_requires_bump(self):
        (self.root / GATE.API_DIRECTORY / "mod.rs").rename(self.root / "outside.rs")
        self.rejects("strictly newer")

    def test_rename_into_directory_requires_bump(self):
        self.git("mv", "README.md", f"{GATE.API_DIRECTORY}/readme.md")
        self.rejects("strictly newer")

    def test_missing_or_deleted_version_fails(self):
        (self.root / GATE.VERSION_FILE).unlink()
        self.rejects("cannot read")
        self.rejects("cannot read", self.initial)

    def test_deleting_entire_api_does_not_bypass(self):
        shutil.rmtree(self.root / GATE.API_DIRECTORY)
        self.rejects("cannot read")

    def test_bad_duplicate_or_commented_version_fails(self):
        for text in (
            'pub const API_VERSION: &str = "1.0";',
            'pub const API_VERSION: &str = "01.0.1";',
            'pub const API_VERSION: &str = "1.0.1-rc1";',
            'pub const API_VERSION: &str = "x.y.z";',
            'pub const API_VERSION: &str = "1.0.1";\npub const API_VERSION: &str = "2.0.0";',
            '// pub const API_VERSION: &str = "1.0.1";',
            '/* pub const API_VERSION: &str = "1.0.1"; */',
        ):
            with self.subTest(text=text):
                self.write(GATE.VERSION_FILE, text)
                self.rejects("exactly one")

    def test_missing_or_bad_base_version_fails(self):
        for text in (None, 'pub const API_VERSION: &str = "bad";\n'):
            with self.subTest(text=text):
                if text is None:
                    (self.root / GATE.VERSION_FILE).unlink()
                else:
                    self.write(GATE.VERSION_FILE, text)
                base = self.commit()
                self.bump()
                self.rejects("base.*(missing|exactly one)", base)

    def test_same_or_lower_version_fails(self):
        for version in ("0.9.99", "1.0.0"):
            with self.subTest(version=version):
                self.bump(version)
                self.write(f"{GATE.API_DIRECTORY}/mod.rs", "// change\n")
                self.rejects("strictly newer")

    def test_version_order_is_numeric(self):
        self.bump("1.9.0")
        base = self.commit()
        self.bump("1.10.0")
        self.accepts(base)

    def test_unchanged_missing_and_unmatched_docs_fail(self):
        self.version("1.0.1")
        self.rejects("update to docs")
        self.docs("1.0.0", "Only the old entry changed.")
        self.rejects("needs a ### 1.0.1")
        (self.root / GATE.DOCUMENTATION).unlink()
        self.rejects("cannot read")

    def test_preexisting_matching_entry_cannot_be_reused_with_unrelated_edit(self):
        self.docs("1.0.1")
        base = self.commit()
        self.version("1.0.1")
        path = self.root / GATE.DOCUMENTATION
        path.write_text("Introduction changed.\n" + path.read_text())
        self.rejects("entry must be new or updated", base)
        self.docs("1.0.1", "Actual API update details.")
        self.accepts(base)

    def test_version_heading_inside_code_fence_is_not_entry(self):
        self.version("1.0.1")
        for marker in ("```", "~~~~"):
            with self.subTest(marker=marker):
                self.write(GATE.DOCUMENTATION, f"{marker}\n### 1.0.1\nExample only.\n{marker}\n")
                self.rejects("needs a ###")

    def test_duplicate_and_empty_entries_fail(self):
        self.version("1.0.1")
        self.write(GATE.DOCUMENTATION, "### 1.0.1\n")
        self.rejects("explanatory text")
        self.write(GATE.DOCUMENTATION, "### 1.0.1\nText\n### 1.0.1\nOther\n")
        self.rejects("duplicate")

    def test_symlink_version_and_docs_fail(self):
        self.bump()
        for relative in (GATE.VERSION_FILE, GATE.DOCUMENTATION):
            with self.subTest(relative=relative):
                path = self.root / relative
                source = path.read_text()
                target = self.root / "outside.txt"
                target.write_text(source)
                path.unlink()
                path.symlink_to(target)
                self.rejects("not a symlink")
                path.unlink()
                path.write_text(source)

    def test_nested_comments_do_not_supply_version(self):
        self.bump()
        path = self.root / GATE.VERSION_FILE
        path.write_text('/* outer /* pub const API_VERSION: &str = "9.9.9"; */ inner */\n' + path.read_text())
        self.accepts()

    def test_invalid_base_fails(self):
        self.rejects("valid|revision", "missing-ref")

    def test_cli_requires_base_and_reports_failures(self):
        missing = subprocess.run([sys.executable, str(SCRIPT), "--root", str(self.root)], capture_output=True)
        self.assertEqual(missing.returncode, 2)
        self.assertIn(b"--base", missing.stderr)
        self.write(f"{GATE.API_DIRECTORY}/new.rs", "// changed\n")
        failed = subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(self.root), "--base", self.base], capture_output=True
        )
        self.assertEqual(failed.returncode, 1)
        self.assertIn(b"FAIL:", failed.stderr)
        self.bump()
        passed = subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(self.root), "--base", self.base], capture_output=True
        )
        self.assertEqual(passed.returncode, 0, passed.stderr)
        self.assertIn(b"PASS:", passed.stdout)


if __name__ == "__main__":
    unittest.main()
