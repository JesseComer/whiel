"""Unit tests for scripts/verifier_freeze.py.

Covers the Rust/Lean comment-and-whitespace normalisers, add/remove/change
detection on a synthetic tree, and the real `check` gate against this repo's
checked-in manifest.
"""

import argparse
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "verifier_freeze.py"
REPO_ROOT = SCRIPT.parents[1]
SPEC = importlib.util.spec_from_file_location("verifier_freeze", SCRIPT)
VF = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = VF
SPEC.loader.exec_module(VF)


class RustNormaliserTest(unittest.TestCase):
    def norm(self, source: str) -> str:
        return VF._collapse_whitespace(VF.strip_rust_comments(source))

    def test_line_comment_stripped(self):
        self.assertEqual(self.norm("let x = 1; // trailing\n"), "let x = 1;")

    def test_block_comment_stripped(self):
        self.assertEqual(self.norm("let x /* mid */ = 1;"), "let x = 1;")

    def test_nested_block_comment(self):
        self.assertEqual(self.norm("/* outer /* inner */ still */let x = 1;"), "let x = 1;")

    def test_doc_comment_stripped(self):
        self.assertEqual(self.norm("/// docs\nfn f() {}"), "fn f() {}")

    def test_comment_marker_inside_string_preserved(self):
        self.assertEqual(self.norm('let s = "not // a comment";'), 'let s = "not // a comment";')

    def test_block_comment_marker_inside_string_preserved(self):
        self.assertEqual(self.norm('let s = "a /* not a comment */ b";'), 'let s = "a /* not a comment */ b";')

    def test_raw_string_contents_preserved(self):
        self.assertEqual(self.norm('let s = r"a // b /* c */ d";'), 'let s = r"a // b /* c */ d";')

    def test_raw_string_with_hashes(self):
        self.assertEqual(
            self.norm('let s = r#"contains "quotes" and // slashes"#;'),
            'let s = r#"contains "quotes" and // slashes"#;',
        )

    def test_raw_string_hash_count_disambiguates_closer(self):
        # A lone `"##` inside the body must not be mistaken for the real
        # `"###` closer that ends the literal.
        source = 'let s = r###"body "## still inside"###;'
        self.assertEqual(self.norm(source), self.norm(source))
        self.assertTrue(self.norm(source).endswith('"###;'))

    def test_byte_string_preserved(self):
        self.assertEqual(self.norm(b'let s = b"raw // bytes";'.decode()), 'let s = b"raw // bytes";')

    def test_escaped_quote_in_string(self):
        self.assertEqual(self.norm('let s = "a \\" b"; // c'), 'let s = "a \\" b";')

    def test_char_literal_slash_not_a_comment_start(self):
        self.assertEqual(self.norm("if c == '/' { x() } // trailing"), "if c == '/' { x() }")

    def test_char_literal_escaped_quote(self):
        self.assertEqual(self.norm("let c = '\\''; // comment"), "let c = '\\'';")

    def test_lifetime_is_not_treated_as_unterminated_char(self):
        source = "fn f<'a>(x: &'a str) -> &'a str { x } // trailing"
        normalised = self.norm(source)
        self.assertEqual(normalised, "fn f<'a>(x: &'a str) -> &'a str { x }")
        self.assertIn("'a", normalised)

    def test_reindentation_does_not_change_normalised_text(self):
        a = "fn f(x: i32) -> i32 {\n    x + 1\n}\n"
        # Only whitespace/blank-line changes around identical tokens: extra
        # blank lines and indentation collapse to the same normalised text.
        b = "fn f(x: i32) -> i32 {\n\n\n    x + 1\n\n}\n"
        self.assertEqual(self.norm(a), self.norm(b))
        self.assertNotEqual(a, b)


class LeanNormaliserTest(unittest.TestCase):
    def norm(self, source: str) -> str:
        return VF._collapse_whitespace(VF.strip_lean_comments(source))

    def test_line_comment_stripped(self):
        self.assertEqual(self.norm("def x := 1 -- trailing\n"), "def x := 1")

    def test_block_comment_stripped(self):
        self.assertEqual(self.norm("def x /- mid -/ := 1"), "def x := 1")

    def test_nested_block_comment(self):
        self.assertEqual(self.norm("/- outer /- inner -/ still -/def x := 1"), "def x := 1")

    def test_doc_comment_stripped(self):
        self.assertEqual(self.norm("/-- docs -/\ndef f := 1"), "def f := 1")

    def test_module_doc_comment_stripped(self):
        self.assertEqual(self.norm("/-! module docs -/\ndef f := 1"), "def f := 1")

    def test_double_dash_inside_string_preserved(self):
        self.assertEqual(self.norm('def s := "not -- a comment"'), 'def s := "not -- a comment"')

    def test_block_marker_inside_string_preserved(self):
        self.assertEqual(self.norm('def s := "a /- not a comment -/ b"'), 'def s := "a /- not a comment -/ b"')

    def test_char_literal_preserved(self):
        self.assertEqual(self.norm("def c : Char := '-' -- trailing"), "def c : Char := '-'")


class SyntheticTreeTest(unittest.TestCase):
    """Add/remove/change detection over a small synthetic file set, using
    the same primitives `list`/`check`/`bless` are built from."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="verifier-freeze-synthetic-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "whiel_runner" / "src" / "framework2").mkdir(parents=True)
        (self.root / "whiel_runner" / "src" / "campaign_certify.rs").write_text(
            "fn certify() {}\n"
        )
        (self.root / "whiel_runner" / "src" / "framework2" / "search.rs").write_text(
            "fn run() { 1 }\n"
        )
        (self.root / "whiel_runner" / "src" / "framework2" / "search_tests.rs").write_text(
            "#[test] fn t() {}\n"
        )
        (self.root / "whiel_runner" / "Cargo.toml").write_text("[package]\n")
        (self.root / "Whiel").mkdir()
        (self.root / "Whiel" / "Worker.lean").write_text("def worker := 1\n")
        (self.root / "lakefile.toml").write_text("name = \"x\"\n")
        (self.root / "lake-manifest.json").write_text("{}\n")
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.0.0\n")
        (self.root / "toolchain.lock.json").write_text("{}\n")
        self.data = {
            "rust_roots": ["whiel_runner/src", "whiel_runner/Cargo.toml", "whiel_runner/Cargo.lock"],
            "rust_exclusions": [
                {"path": "whiel_runner/src/campaign_certify.rs", "reason": "test fixture"}
            ],
            "lean_root_module": "Whiel.Worker",
            "lean_source_roots": ["Whiel"],
            "lean_extra_files": ["lakefile.toml", "lake-manifest.json", "lean-toolchain"],
            "pins": ["toolchain.lock.json"],
        }

    def test_exclusion_and_test_pattern_applied(self):
        files = VF.rust_files(self.root, self.data)
        self.assertIn("whiel_runner/src/framework2/search.rs", files)
        self.assertNotIn("whiel_runner/src/campaign_certify.rs", files)
        self.assertNotIn("whiel_runner/src/framework2/search_tests.rs", files)

    def test_file_root_included_when_present(self):
        files = VF.rust_files(self.root, self.data)
        self.assertIn("whiel_runner/Cargo.toml", files)

    def test_file_root_silently_absent_when_missing(self):
        # "whiel_runner/Cargo.lock" is listed in rust_roots but never
        # created in this fixture: an individual-file root that does not
        # exist is skipped, matching the old rust_extra_files behaviour.
        files = VF.rust_files(self.root, self.data)
        self.assertNotIn("whiel_runner/Cargo.lock", files)

    def test_excluded_file_root_is_not_included(self):
        data = dict(self.data)
        data["rust_exclusions"] = self.data["rust_exclusions"] + [
            {"path": "whiel_runner/Cargo.toml", "reason": "test fixture"}
        ]
        files = VF.rust_files(self.root, data)
        self.assertNotIn("whiel_runner/Cargo.toml", files)

    def test_lean_closure_reaches_root_only(self):
        files = VF.lean_files(self.root, self.data)
        self.assertIn("Whiel/Worker.lean", files)
        self.assertIn("lakefile.toml", files)

    def test_add_remove_change_detected(self):
        before = VF.compute_manifest(self.root, self.data)

        # change: edit a token in a tracked verifier file
        search_path = self.root / "whiel_runner" / "src" / "framework2" / "search.rs"
        search_path.write_text("fn run() { 2 }\n")
        # add: a new tracked file
        (self.root / "whiel_runner" / "src" / "framework2" / "new_module.rs").write_text(
            "fn helper() {}\n"
        )
        after_add_change = VF.compute_manifest(self.root, self.data)

        self.assertNotEqual(before["overall_digest"], after_add_change["overall_digest"])
        changed = {
            relative
            for relative in set(before["files"]) & set(after_add_change["files"])
            if before["files"][relative] != after_add_change["files"][relative]
        }
        added = set(after_add_change["files"]) - set(before["files"])
        self.assertIn("whiel_runner/src/framework2/search.rs", changed)
        self.assertIn("whiel_runner/src/framework2/new_module.rs", added)

        # remove: delete the new file again
        (self.root / "whiel_runner" / "src" / "framework2" / "new_module.rs").unlink()
        after_remove = VF.compute_manifest(self.root, self.data)
        removed = set(after_add_change["files"]) - set(after_remove["files"])
        self.assertIn("whiel_runner/src/framework2/new_module.rs", removed)

    def test_comment_and_whitespace_only_edit_does_not_change_digest(self):
        before = VF.compute_manifest(self.root, self.data)
        search_path = self.root / "whiel_runner" / "src" / "framework2" / "search.rs"
        search_path.write_text("// a helpful comment\nfn run() {\n    1\n}\n")
        after = VF.compute_manifest(self.root, self.data)
        self.assertEqual(before["overall_digest"], after["overall_digest"])

    def test_excluded_file_edit_does_not_change_digest(self):
        before = VF.compute_manifest(self.root, self.data)
        certify_path = self.root / "whiel_runner" / "src" / "campaign_certify.rs"
        certify_path.write_text("fn certify() { do_more_work(); }\n")
        after = VF.compute_manifest(self.root, self.data)
        self.assertEqual(before["overall_digest"], after["overall_digest"])


class CertificateTransformScopeTest(unittest.TestCase):
    """The reviewed correction is exact, not a subtree exemption."""

    names = ("mod", "canonical", "prenex", "projection", "lrat")
    prefix = "whiel_runner/src/framework2/proof_transform/"

    def test_real_exclusions_are_exact_and_keep_mixed_sources(self):
        data = VF.load_data()
        excluded = {item["path"] for item in data["rust_exclusions"]}
        expected = {self.prefix + name + ".rs" for name in self.names}
        self.assertEqual({p for p in excluded if p.startswith(self.prefix)}, expected)
        retained = VF.rust_files(REPO_ROOT, data)
        for path in (
            "whiel_runner/src/certificate_cli.rs",
            "whiel_runner/src/campaign_run.rs",
            "whiel_runner/src/framework2/leancheck.rs",
            "whiel_runner/src/framework2/certificate_profiles.rs",
            "whiel_runner/src/framework2/publication.rs",
            "whiel_runner/src/framework2/production.rs",
            "whiel_runner/src/framework2/search.rs",
        ):
            self.assertIn(path, retained)

    def test_excluded_edits_ignored_but_new_and_search_sources_tracked(self):
        with tempfile.TemporaryDirectory(prefix="certifier-freeze-scope-") as tmp:
            root = Path(tmp)
            data = VF.load_data()
            transform = root / self.prefix
            transform.mkdir(parents=True)
            for name in self.names:
                (transform / (name + ".rs")).write_text("fn certify() {}\n")
            search = root / "whiel_runner/src/framework2/search.rs"
            search.write_text("fn search() { 1 }\n")
            before = {p: VF.file_digest(f) for p, f in VF.rust_files(root, data).items()}
            for name in self.names:
                (transform / (name + ".rs")).write_text("fn certify() { changed(); }\n")
            after = {p: VF.file_digest(f) for p, f in VF.rust_files(root, data).items()}
            self.assertEqual(before, after)
            search.write_text("fn search() { 2 }\n")
            (transform / "new_helper.rs").write_text("fn helper() {}\n")
            changed = {p: VF.file_digest(f) for p, f in VF.rust_files(root, data).items()}
            search_key = search.relative_to(root).as_posix()
            self.assertNotEqual(before[search_key], changed[search_key])
            self.assertIn(self.prefix + "new_helper.rs", changed)


class BlessRefusalTest(unittest.TestCase):
    def test_bless_without_flag_refuses(self):
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "bless"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("--approved-by-owner", result.stderr + result.stdout)


class DigestVersionTest(unittest.TestCase):
    """`check` must refuse outright on a version mismatch, without ever
    reaching (and misreporting) an ordinary file-set comparison."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="verifier-freeze-version-")
        self.addCleanup(self.tmp.cleanup)
        self.manifest_path = Path(self.tmp.name) / "verifier_freeze_manifest.json"

    def _run_check_against(self, manifest: dict):
        self.manifest_path.write_text(json.dumps(manifest))
        original = VF.MANIFEST_FILE
        VF.MANIFEST_FILE = self.manifest_path
        try:
            return VF.cmd_check(argparse.Namespace(lean=False))
        finally:
            VF.MANIFEST_FILE = original

    def test_rust_digest_version_mismatch_refuses_without_diffing_files(self):
        data = VF.load_data()
        current = VF.compute_manifest(VF.REPO_ROOT, data)
        current["rust_digest_version"] = VF.RUST_DIGEST_VERSION + 1
        rc = self._run_check_against(current)
        self.assertEqual(rc, 1)

    def test_lean_digest_version_mismatch_refuses(self):
        data = VF.load_data()
        current = VF.compute_manifest(VF.REPO_ROOT, data)
        current["lean_digest_version"] = VF.LEAN_DIGEST_VERSION + 1
        rc = self._run_check_against(current)
        self.assertEqual(rc, 1)

    def test_matching_versions_do_not_trip_on_version_alone(self):
        data = VF.load_data()
        current = VF.compute_manifest(VF.REPO_ROOT, data)
        # Versions match and the file set is untouched, so this must behave
        # exactly like the ordinary `check` against a freshly blessed
        # manifest: success.
        rc = self._run_check_against(current)
        self.assertEqual(rc, 0)


class ParseLeanDeclsTest(unittest.TestCase):
    """Pure parsing of the declaration tool's TSV output. Deliberately does
    not invoke `scripts/verifier_freeze_decls.lean` itself: that needs a
    built library and tens of seconds, so it stays out of this gate (see
    `AGENTS.md`'s "Verifier Freeze" section)."""

    def test_parses_well_formed_lines(self):
        stdout = (
            "Whiel.Foo.bar\tWhiel.Foo\tdef\tabc123\n"
            "Whiel.Foo.Baz\tWhiel.Foo\tinductive\tdeadbeef\n"
        )
        decls = VF.parse_lean_decls(stdout)
        self.assertEqual(
            decls["Whiel.Foo.bar"],
            {"module": "Whiel.Foo", "kind": "def", "hash": "abc123"},
        )
        self.assertEqual(len(decls), 2)

    def test_ignores_blank_lines(self):
        decls = VF.parse_lean_decls("Whiel.Foo.bar\tWhiel.Foo\tdef\tabc123\n\n")
        self.assertEqual(len(decls), 1)

    def test_malformed_line_raises(self):
        with self.assertRaises(SystemExit):
            VF.parse_lean_decls("not-enough-fields\n")

    def test_overall_digest_stable_regardless_of_input_order(self):
        # compute_lean_declarations sorts by name before hashing, so the
        # tool's own (already-sorted) output order is not load-bearing.
        a = VF.parse_lean_decls(
            "Whiel.A\tWhiel\tdef\t1\nWhiel.B\tWhiel\tdef\t2\n"
        )
        b = VF.parse_lean_decls(
            "Whiel.B\tWhiel\tdef\t2\nWhiel.A\tWhiel\tdef\t1\n"
        )
        self.assertEqual(a, b)


class DeclsToolPresenceTest(unittest.TestCase):
    """Sanity checks that need no Lean invocation: the standalone tool
    exists, is not wired into any lake target, and is not imported by any
    library module."""

    def test_tool_file_exists(self):
        self.assertTrue(VF.DECLS_TOOL.is_file())

    def test_tool_not_registered_as_a_lake_target(self):
        lakefile = (REPO_ROOT / "lakefile.toml").read_text()
        self.assertNotIn("verifier_freeze_decls", lakefile)

    def test_tool_not_imported_by_any_lean_source_file(self):
        needle = "verifier_freeze_decls"
        for root_name in ("Whiel", "Databases", "Benchmark", "VampLean"):
            root = REPO_ROOT / root_name
            if not root.is_dir():
                continue
            for path in root.rglob("*.lean"):
                self.assertNotIn(
                    needle,
                    path.read_text(),
                    msg=f"{path} appears to reference the standalone tool",
                )


class RealRepoCheckTest(unittest.TestCase):
    """The actual gate: the checked-in manifest must match the repository as
    it stands. A failure here prints the same protocol text `check` prints
    on a real tripped freeze."""

    def test_check_passes_against_checked_in_manifest(self):
        manifest_path = SCRIPT.parent / "verifier_freeze_manifest.json"
        if not manifest_path.is_file():
            self.skipTest("no recorded manifest yet (run bless --approved-by-owner)")
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "check"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, msg=result.stdout + result.stderr)

    def test_list_runs_and_reports_three_groups(self):
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "list"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, msg=result.stdout + result.stderr)
        for heading in ("# rust", "# lean", "# pins"):
            self.assertIn(heading, result.stdout)


if __name__ == "__main__":
    unittest.main()
