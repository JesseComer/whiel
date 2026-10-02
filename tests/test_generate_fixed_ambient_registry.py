"""Closed-world output validation with open-ended input discovery."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "registry_generator", Path(__file__).resolve().parents[1]
    / "scripts/generate_fixed_ambient_registry.py")
generator = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = generator
SPEC.loader.exec_module(generator)

PLACE_SPEC = importlib.util.spec_from_file_location(
    "place_certificates", Path(__file__).resolve().parents[1] / "scripts/place_certificates.py")
placement = importlib.util.module_from_spec(PLACE_SPEC)
sys.modules[PLACE_SPEC.name] = placement
PLACE_SPEC.loader.exec_module(placement)


class GeneratorTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "Benchmark").mkdir()
        self.add_input("Zeta9")
        self.add_input("Alpha")

    def input_text(self, id):
        # Plain text standing in for a Lean file; Lean itself is never run here.
        # Only the five canonical declarations and their exact spelling matter.
        return (
            "-- Benchmark contributors: Fangzhu Shen, Leo Zhang\n"
            "import Foo\n\n"
            f"namespace Whiel\nnamespace Benchmark\nnamespace {id}\n\nopen Concrete\n\n"
            f'def inputSchema : String :=\n  "{id}-schema"\n\n'
            f'def inputPre : String :=\n  "{id}-pre"\n\n'
            f'def inputCmd : String :=\n  "{id}-cmd"\n\n'
            f'def inputPost : String :=\n  "{id}-post"\n\n'
            f'def inputPreproc : String :=\n  "{id}-preproc"\n\n'
            "set_option linter.hashCommand false in\n#eval inputPreproc.display\n\n"
            f"end {id}\nend Benchmark\nend Whiel\n"
        )

    def add_input(self, id):
        directory = self.root / "Benchmark" / id
        directory.mkdir()
        (directory / "Input.lean").write_text(self.input_text(id))
        (directory / "Metadata.json").write_text(json.dumps({"canonicalId": id}))

    def add_certificate(self, id, name, marked):
        directory = self.root / "Benchmark" / id / "Certificate"
        directory.mkdir(parents=True, exist_ok=True)
        text = (generator.EMITTER_MARK + "\n-- generated certificate body\n" if marked
                 else "-- hand-written certificate, not emitter output\n")
        (directory / f"{name}.lean").write_text(text)
        self.write_ledger()

    def write_ledger(self, certificates=None, raw=None):
        """A current ledger for every certified case; `certificates` overrides entries."""
        if raw is not None:
            (self.root / generator.PLACEMENT).write_text(raw)
            return
        entries = {}
        for case in placement.certified_cases(self.root):
            entries[case] = {"treeSha256": placement.tree_digest(self.root / "Benchmark" / case),
                             "fits": True, "peakKb": 1000}
        for case, entry in (certificates or {}).items():
            entries.setdefault(case, {"treeSha256": "0" * 64, "peakKb": 1000}).update(entry)
            if entries[case].get("fits") is False:
                entries[case].setdefault("note", "peak above the limit")
        payload = {"version": placement.LEDGER_VERSION, "limitKb": 4194304, "certificates": entries}
        (self.root / generator.PLACEMENT).write_text(json.dumps(payload))

    def snapshot(self):
        return {str(p.relative_to(self.root)): (p.read_bytes(), p.stat().st_mtime_ns)
                for p in self.root.rglob("*") if p.is_file()}

    def metadata(self, id="Alpha", **changes):
        p = self.root / "Benchmark" / id / "Metadata.json"
        data = json.loads(p.read_text())
        data.update(changes)
        p.write_text(json.dumps(data))

    # -- core generation behaviour --------------------------------------

    def test_dynamic_sorted_full_inventory_and_determinism(self):
        self.assertEqual(generator.generate(self.root), ["Alpha", "Zeta9"])
        before = self.snapshot()
        generator.generate(self.root)
        generator.generate(self.root, check=True)
        self.assertEqual(before, self.snapshot())
        self.add_input("Future_99")
        self.assertEqual(generator.generate(self.root), ["Alpha", "Future_99", "Zeta9"])

    def test_check_missing_nonmutating(self):
        before = self.snapshot()
        with self.assertRaises(generator.RegistryError):
            generator.generate(self.root, check=True)
        self.assertEqual(before, self.snapshot())

    def test_source_drift_check_and_intentional_regeneration(self):
        generator.generate(self.root)
        source = self.root / "Benchmark/Alpha/Input.lean"
        original = source.read_text()
        source.write_text(original.replace('"Alpha-cmd"', '"Alpha-cmd-changed"'))
        before = self.snapshot()
        with self.assertRaisesRegex(generator.RegistryError, "stale"):
            generator.generate(self.root, check=True)
        self.assertEqual(before, self.snapshot())
        generator.generate(self.root)
        generator.generate(self.root, check=True)
        self.assertIn('"Alpha-cmd-changed"', source.read_text())
        generated = (self.root / generator.OUTPUT / "Generated/Alpha.lean").read_text()
        self.assertNotIn(hashlib.sha256(original.encode()).hexdigest()[:32], generated)

    def test_removal_detects_stale_and_removes_generated_file(self):
        generator.generate(self.root)
        (self.root / "Benchmark/Alpha/Input.lean").unlink()
        before = self.snapshot()
        with self.assertRaisesRegex(generator.RegistryError, "stale"):
            generator.generate(self.root, check=True)
        self.assertEqual(before, self.snapshot())
        self.assertEqual(generator.generate(self.root), ["Zeta9"])
        self.assertFalse((self.root / generator.OUTPUT / "Generated/Alpha.lean").exists())

    def test_generated_deletion_detected_and_repaired(self):
        generator.generate(self.root)
        (self.root / generator.OUTPUT / "Generated/Alpha.lean").unlink()
        with self.assertRaisesRegex(generator.RegistryError, "stale"):
            generator.generate(self.root, check=True)
        generator.generate(self.root)
        generator.generate(self.root, check=True)

    def test_explicit_subset_never_changes_default(self):
        self.assertEqual(generator.generate(self.root, ids=["Zeta9"]), ["Zeta9"])
        generator.generate(self.root, check=True, ids=["Zeta9"])
        with self.assertRaises(generator.RegistryError):
            generator.generate(self.root, check=True)
        self.assertEqual(generator.generate(self.root), ["Alpha", "Zeta9"])
        for ids in [[], ["Alpha", "Alpha"], ["Absent"]]:
            with self.subTest(ids=ids), self.assertRaises(generator.RegistryError):
                generator.generate(self.root, ids=ids)

    # -- metadata: relaxed requirements ----------------------------------

    def test_metadata_with_only_canonical_id_is_accepted(self):
        (self.root / "Benchmark/Alpha/Metadata.json").write_text(
            json.dumps({"canonicalId": "Alpha"}))
        self.assertEqual(generator.generate(self.root), ["Alpha", "Zeta9"])

    def test_metadata_unknown_keys_are_ignored(self):
        (self.root / "Benchmark/Alpha/Metadata.json").write_text(json.dumps({
            "canonicalId": "Alpha", "canonicalModule": "Legacy.Wrong.Module",
            "declarationNamespace": "Other.Namespace", "formatVersion": "not a number",
            "sourceRecords": "not even a list"}))
        self.assertEqual(generator.generate(self.root), ["Alpha", "Zeta9"])

    def test_metadata_canonical_id_mismatch_refused(self):
        self.metadata("Alpha", canonicalId="NotAlpha")
        with self.assertRaisesRegex(generator.RegistryError, "canonicalId mismatch"):
            generator.generate(self.root)

    def test_metadata_unsafe_canonical_id_refused(self):
        self.metadata("Alpha", canonicalId="../escape")
        with self.assertRaisesRegex(generator.RegistryError, "unsafe canonical id"):
            generator.generate(self.root)

    def test_unsafe_directory_name_refused(self):
        directory = self.root / "Benchmark" / "bad-name"
        directory.mkdir()
        (directory / "Input.lean").write_text(self.input_text("bad-name"))
        (directory / "Metadata.json").write_text(json.dumps({"canonicalId": "bad-name"}))
        with self.assertRaisesRegex(generator.RegistryError, "unsafe canonical directory"):
            generator.generate(self.root)

    def test_metadata_duplicate_canonical_id(self):
        self.metadata("Zeta9", canonicalId="Alpha")
        with self.assertRaisesRegex(generator.RegistryError, "duplicate canonical"):
            generator.generate(self.root)

    def test_malformed_missing_and_duplicate_key_metadata(self):
        p = self.root / "Benchmark/Alpha/Metadata.json"
        for value in ["{bad", "[]", '{"canonicalId":"Alpha","canonicalId":"Alpha"}']:
            p.write_text(value)
            with self.assertRaises(generator.RegistryError):
                generator.generate(self.root)
        p.unlink()
        with self.assertRaises(generator.RegistryError):
            generator.generate(self.root)

    # -- declaration digest -----------------------------------------------

    def test_comment_only_edit_leaves_check_clean(self):
        generator.generate(self.root)
        source = self.root / "Benchmark/Alpha/Input.lean"
        original = source.read_text()
        edited = original.replace("import Foo", "import Foo  -- pull in shared definitions")
        edited = edited.replace(
            "namespace Whiel\n", "/- a description, updated for clarity -/\nnamespace Whiel\n", 1)
        edited = edited.replace("Fangzhu Shen, Leo Zhang", "Leo Zhang", 1)
        edited = edited.replace('  "Alpha-schema"', '\n    "Alpha-schema"')
        edited = edited + "\n\n"
        source.write_text(edited)
        self.assertNotEqual(edited, original)
        generator.generate(self.root, check=True)

    def test_declaration_edit_detected_and_changes_digest(self):
        generator.generate(self.root)
        gen_path = self.root / generator.OUTPUT / "Generated/Alpha.lean"
        before = gen_path.read_text()
        source = self.root / "Benchmark/Alpha/Input.lean"
        source.write_text(source.read_text().replace('"Alpha-pre"', '"Alpha-pre-changed"'))
        with self.assertRaisesRegex(generator.RegistryError, "stale"):
            generator.generate(self.root, check=True)
        generator.generate(self.root)
        after = gen_path.read_text()
        self.assertNotEqual(before, after)

    def test_imports_do_not_affect_digest(self):
        generator.generate(self.root)
        gen_path = self.root / generator.OUTPUT / "Generated/Alpha.lean"
        before = gen_path.read_text()
        source = self.root / "Benchmark/Alpha/Input.lean"
        source.write_text(source.read_text().replace("import Foo", "import Foo\nimport Bar"))
        generator.generate(self.root, check=True)
        self.assertEqual(before, gen_path.read_text())

    def refused(self, text, pattern):
        with self.assertRaisesRegex(generator.RegistryError, pattern):
            generator.declaration_digest(text, "Alpha")

    def test_commands_outside_the_fixed_shape_are_refused(self):
        base = self.input_text("Alpha")
        anchor = "def inputSchema"
        for extra in ("def helper : Nat :=\n  0\n\n",
                      'notation "X" => inputSchema\n\n',
                      "open Other in\n",
                      "@[simp]\n",
                      "private def inputSchema : String :=\n  \"p\"\n\n",
                      "set_option pp.all true\n\n",
                      "open Other\n\n"):
            self.refused(base.replace(anchor, extra + anchor, 1), "unexpected top-level line")
        # A qualified definition hiding behind a decoy in another namespace.
        self.refused(base.replace("namespace Alpha", "namespace Other", 1),
                     "unexpected top-level line")
        self.refused(base.replace("def inputPre :", "def Whiel.Benchmark.Alpha.inputPre :", 1),
                     "unexpected top-level line")
        # Elaboration options are part of the shape.
        generator.declaration_digest(
            base.replace(anchor, "set_option maxRecDepth 4096\n\n" + anchor, 1), "Alpha")

    def test_continuation_at_column_zero_is_refused(self):
        text = self.input_text("Alpha").replace('  "Alpha-cmd"', '"Alpha-cmd"', 1)
        self.refused(text, "unexpected top-level line")

    def test_block_opener_inside_a_line_comment_hides_nothing(self):
        base = self.input_text("Alpha")
        hidden = base.replace("def inputCmd", "-- /-\ndef inputCmd", 1).replace(
            "def inputPost", "-- -/\ndef inputPost", 1)
        self.assertEqual(generator.declaration_digest(hidden, "Alpha"),
                         generator.declaration_digest(base, "Alpha"))
        changed = hidden.replace('"Alpha-cmd"', '"Alpha-cmd-2"', 1)
        self.assertNotEqual(generator.declaration_digest(changed, "Alpha"),
                            generator.declaration_digest(base, "Alpha"))

    def test_quote_inside_a_comment_does_not_unbalance_strings(self):
        base = self.input_text("Alpha")
        quoted = base.replace("def inputPre", '-- an odd " quote\ndef inputPre', 1)
        self.assertEqual(generator.declaration_digest(quoted, "Alpha"),
                         generator.declaration_digest(base, "Alpha"))

    def test_string_literals_are_hashed_verbatim(self):
        base = self.input_text("Alpha")
        one = base.replace('"Alpha-schema"', '"a  b"', 1)
        two = base.replace('"Alpha-schema"', '"a b"', 1)
        marker = base.replace('"Alpha-schema"', '"-- not a comment /- nor this"', 1)
        digests = {generator.declaration_digest(text, "Alpha") for text in (base, one, two, marker)}
        self.assertEqual(len(digests), 4)

    def test_missing_declaration_detected_through_generate(self):
        text = self.input_text("Alpha")
        start = text.index("def inputPreproc")
        end = text.index("set_option")
        (self.root / "Benchmark/Alpha/Input.lean").write_text(text[:start] + text[end:])
        with self.assertRaisesRegex(generator.RegistryError, "missing canonical declarations"):
            generator.generate(self.root)

    def test_duplicate_declaration_raises(self):
        text = self.input_text("Alpha").replace(
            "def inputPre :", 'def inputSchema : String :=\n  "dup"\n\ndef inputPre :', 1)
        self.refused(text, "duplicate declaration")

    def test_nested_block_comments_are_comments(self):
        base = self.input_text("Alpha")
        text = "/- outer /- inner -/ still outer -/\n" + base
        self.assertEqual(generator.declaration_digest(text, "Alpha"),
                         generator.declaration_digest(base, "Alpha"))

    def test_unterminated_block_comment_raises(self):
        self.refused(self.input_text("Alpha") + "\n/- never closed\n", "unterminated block comment")

    def test_unbalanced_namespaces_raise(self):
        text = self.input_text("Alpha").replace("end Whiel\n", "", 1)
        self.refused(text, "unbalanced namespaces")

    # -- generated-region safety ------------------------------------------

    def test_unknown_generated_format_fails_before_any_mutation(self):
        generator.generate(self.root)
        p = self.root / generator.OUTPUT / "Generated/Zeta9.lean"
        p.write_text(p.read_text().replace("format: 1", "format: 2"))
        source = self.root / "Benchmark/Alpha/Input.lean"
        source.write_text(source.read_text().replace('"Alpha-cmd"', '"Alpha-cmd-drift"'))
        before = self.snapshot()
        with self.assertRaisesRegex(generator.RegistryError, "unknown generated-region"):
            generator.generate(self.root)
        self.assertEqual(before, self.snapshot())

    def test_nested_and_legacy_inputs_are_not_discovered(self):
        p = self.root / "Benchmark/group/nested"
        p.mkdir(parents=True)
        (p / "Input.lean").write_text("nested")
        p = self.root / "Legacy/Benchmark/Old"
        p.mkdir(parents=True)
        (p / "Input.lean").write_text("legacy")
        self.assertEqual(generator.generate(self.root), ["Alpha", "Zeta9"])

    def test_symlink_sources_metadata_directories_and_outputs_refused(self):
        for relative in ["Benchmark/Alpha/Input.lean", "Benchmark/Alpha/Metadata.json",
                         "Benchmark/Alpha", "Benchmark",
                         str(generator.OUTPUT / "Generated/Alpha.lean"),
                         str(generator.OUTPUT / "Generated"), str(generator.OUTPUT)]:
            with self.subTest(path=relative):
                generator.generate(self.root)
                path = self.root / relative
                moved = path.with_name(path.name + "-saved")
                path.rename(moved)
                path.symlink_to(moved, target_is_directory=moved.is_dir())
                with self.assertRaisesRegex(generator.RegistryError, "symlink"):
                    generator.generate(self.root)
                path.unlink()
                moved.rename(path)

    def test_only_shared_constructor_and_no_certificate_imports(self):
        generator.generate(self.root)
        text = (self.root / generator.OUTPUT / "Generated/Alpha.lean").read_text()
        self.assertEqual(text.count("Entry.ofInput identity manifest inputPreproc"), 1)
        self.assertIn("liftedTaskJson% identity", text)
        self.assertIn("Hoare.preprocess inputPre inputCmd inputPost", text)
        self.assertNotIn("Certificate", text)

    # -- library roots and the case axiom audit ----------------------------

    def test_inputs_root_sorted_imports(self):
        generator.generate(self.root)
        text = (self.root / generator.INPUTS_ROOT).read_text()
        imports = [line for line in text.splitlines() if line.startswith("import ")]
        self.assertEqual(imports, ["import Benchmark.Alpha.Input", "import Benchmark.Zeta9.Input"])

    def test_v2_and_unknown_markers_are_consistent_with_placement(self):
        self.add_certificate("Alpha", "Valid", marked=True)
        root = self.root / "Benchmark/Alpha/Certificate/Valid.lean"
        v2 = "-- Generated by the Lean-owned fixed-ambient certificate-emitter-v2."
        for marker, accepted in ((v2, True), (v2 + " extra", False), ("", False),
                                 (v2.replace("v2", "v3"), False)):
            with self.subTest(marker=marker):
                root.write_text(marker)
                self.write_ledger()
                generator.generate(self.root)
                generated = (self.root / generator.CERTIFICATES_ROOT).read_text()
                self.assertEqual("Benchmark.Alpha.Certificate.Valid" in generated, accepted)

    def test_certificates_root_gated_by_emitter_mark(self):
        self.add_certificate("Alpha", "Invalid", marked=True)
        self.add_certificate("Zeta9", "Invalid", marked=False)
        generator.generate(self.root)
        text = (self.root / generator.CERTIFICATES_ROOT).read_text()
        self.assertIn("import Benchmark.Alpha.Certificate.Invalid", text)
        self.assertNotIn("import Benchmark.Zeta9.Certificate.Invalid", text)
        self.assertNotIn("Zeta9", (self.root / generator.OUTSIDE_ROOT).read_text())

    def test_library_roots_case_removal_detected_and_repaired(self):
        generator.generate(self.root)
        (self.root / "Benchmark/Alpha/Input.lean").unlink()
        with self.assertRaisesRegex(generator.RegistryError, "stale"):
            generator.generate(self.root, check=True)
        generator.generate(self.root)
        text = (self.root / generator.INPUTS_ROOT).read_text()
        self.assertNotIn("Alpha", text)
        self.assertIn("import Benchmark.Zeta9.Input", text)

    def test_hand_written_single_root_replaced_without_error(self):
        (self.root / generator.INPUTS_ROOT).write_text(
            "-- hand-written root; no generated markers here\nimport Something.Else\n")
        generator.generate(self.root)
        text = (self.root / generator.INPUTS_ROOT).read_text()
        self.assertTrue(text.startswith(generator.MARKER))
        self.assertIn("import Benchmark.Alpha.Input", text)

    def test_case_audit_blocks_and_stale_on_addition(self):
        generator.generate(self.root)
        text = (self.root / generator.CASE_AUDIT).read_text()
        self.assertEqual(text.count("#print axioms"), 2)
        self.assertIn("FixedAmbientRegistry.Alpha.inputPreproc_eq_preprocess", text)
        self.assertIn("FixedAmbientRegistry.Zeta9.inputPreproc_eq_preprocess", text)
        self.add_input("Beta")
        with self.assertRaisesRegex(generator.RegistryError, "stale"):
            generator.generate(self.root, check=True)
        generator.generate(self.root)
        text = (self.root / generator.CASE_AUDIT).read_text()
        self.assertEqual(text.count("#print axioms"), 3)

    def test_ids_do_not_touch_single_files(self):
        generator.generate(self.root, ids=["Zeta9"])
        for single in (generator.INPUTS_ROOT, generator.CERTIFICATES_ROOT,
                       generator.OUTSIDE_ROOT, generator.FIDELITY_ROOT, generator.CASE_AUDIT):
            self.assertFalse((self.root / single).exists())

    def test_ids_do_not_modify_existing_single_files(self):
        generator.generate(self.root)
        before = {single: (self.root / single).read_bytes()
                  for single in (generator.INPUTS_ROOT, generator.CERTIFICATES_ROOT,
                                 generator.OUTSIDE_ROOT, generator.FIDELITY_ROOT, generator.CASE_AUDIT)}
        generator.generate(self.root, ids=["Zeta9"])
        for single, content in before.items():
            self.assertEqual(content, (self.root / single).read_bytes())

    def test_fidelity_root_lists_only_cases_with_a_fidelity_module(self):
        fidelity = self.root / "Benchmark" / "Alpha" / "Fidelity"
        fidelity.mkdir()
        (fidelity / "Alpha.lean").write_text("-- fidelity proof\n")
        generator.generate(self.root)
        text = (self.root / "Benchmark" / "Fidelity.lean").read_text()
        self.assertIn("import Benchmark.Alpha.Fidelity.Alpha\n", text)
        self.assertNotIn("Zeta9", text)
        generator.generate(self.root, check=True)
        (fidelity / "Alpha.lean").unlink()
        with self.assertRaises(generator.RegistryError):
            generator.generate(self.root, check=True)

    # -- certificate placement ledger --------------------------------------

    def test_ledger_moves_certificate_between_roots_and_back(self):
        self.add_certificate("Alpha", "Invalid", marked=True)
        generator.generate(self.root)
        self.assertIn("import Benchmark.Alpha.Certificate.Invalid\n",
                      (self.root / generator.CERTIFICATES_ROOT).read_text())
        self.assertNotIn("Alpha", (self.root / generator.OUTSIDE_ROOT).read_text())

        digest = placement.tree_digest(self.root / "Benchmark" / "Alpha")
        self.write_ledger({"Alpha": {"treeSha256": digest, "fits": False}})
        with self.assertRaisesRegex(generator.RegistryError, "stale"):
            generator.generate(self.root, check=True)
        generator.generate(self.root)
        self.assertNotIn("Alpha", (self.root / generator.CERTIFICATES_ROOT).read_text())
        self.assertIn("import Benchmark.Alpha.Certificate.Invalid\n",
                      (self.root / generator.OUTSIDE_ROOT).read_text())

        self.write_ledger({"Alpha": {"treeSha256": digest, "fits": True}})
        with self.assertRaisesRegex(generator.RegistryError, "stale"):
            generator.generate(self.root, check=True)
        generator.generate(self.root)
        self.assertIn("import Benchmark.Alpha.Certificate.Invalid\n",
                      (self.root / generator.CERTIFICATES_ROOT).read_text())
        self.assertNotIn("Alpha", (self.root / generator.OUTSIDE_ROOT).read_text())

    def test_ledger_that_is_not_current_is_refused(self):
        self.add_certificate("Alpha", "Invalid", marked=True)
        generator.generate(self.root)
        pattern = "placement ledger is not current"
        # A re-emitted certificate whose entry still describes the old tree.
        certificate = self.root / "Benchmark/Alpha/Certificate/Invalid.lean"
        certificate.write_text(certificate.read_text() + "-- re-emitted\n")
        with self.assertRaisesRegex(generator.RegistryError, pattern):
            generator.generate(self.root)
        self.write_ledger()
        generator.generate(self.root)
        # A certified case with no ledger at all.
        (self.root / generator.PLACEMENT).unlink()
        with self.assertRaisesRegex(generator.RegistryError, pattern):
            generator.generate(self.root)
        # An entry for a case that has no certificate.
        self.write_ledger({"Zeta9": {"fits": True}})
        with self.assertRaisesRegex(generator.RegistryError, pattern):
            generator.generate(self.root)

    def test_malformed_ledger_refused(self):
        self.add_certificate("Alpha", "Invalid", marked=True)
        digest = placement.tree_digest(self.root / "Benchmark" / "Alpha")
        entry = {"treeSha256": digest, "peakKb": 1000}
        payloads = ["{not json", "{}", "[]", json.dumps({"version": 1, "certificates": {}}),
                    json.dumps({"version": placement.LEDGER_VERSION, "limitKb": 4194304,
                                "certificates": {"Alpha": {**entry, "fits": "false"}}}),
                    json.dumps({"version": placement.LEDGER_VERSION, "limitKb": 4194304,
                                "certificates": {"Alpha": {**entry, "fits": 0}}})]
        for payload in payloads:
            with self.subTest(payload=payload):
                self.write_ledger(raw=payload)
                with self.assertRaisesRegex(generator.RegistryError, "placement ledger"):
                    generator.generate(self.root)

    def test_corpus_without_certificates_needs_no_ledger(self):
        self.assertFalse((self.root / generator.PLACEMENT).exists())
        generator.generate(self.root)
        generator.generate(self.root, check=True)

    def test_symlinked_ledger_refused(self):
        target = self.root / "placement-elsewhere.json"
        target.write_text(json.dumps({"version": 1, "certificates": {}}))
        (self.root / generator.PLACEMENT).symlink_to(target)
        with self.assertRaisesRegex(generator.RegistryError, "symlink"):
            generator.generate(self.root)

    def test_metadata_outside_library_keys_are_ignored(self):
        self.add_certificate("Alpha", "Invalid", marked=True)
        for value in (True, "yes", "needs more memory than the watched build allows"):
            with self.subTest(value=value):
                self.metadata("Alpha", certificateOutsideLibrary=value,
                              certificateNote="ignored regardless of content")
                generator.generate(self.root)
                self.assertIn("import Benchmark.Alpha.Certificate.Invalid\n",
                              (self.root / generator.CERTIFICATES_ROOT).read_text())
                self.assertNotIn("Alpha", (self.root / generator.OUTSIDE_ROOT).read_text())

    # -- notation round-trip modules ---------------------------------------

    def test_round_trip_module_per_case_and_aggregate_sorted(self):
        generator.generate(self.root)
        for id in ("Alpha", "Zeta9"):
            text = (self.root / generator.ROUND_TRIP / "Cases" / f"{id}.lean").read_text()
            self.assertIn(f"import Benchmark.{id}.Input\n", text)
            self.assertIn("import Whiel.Synthesis.Tests.BenchmarkNotationRoundTrip\n", text)
            self.assertIn(f"#roundTrip Whiel.Benchmark.{id}", text)
        aggregate = (self.root
                     / "Whiel/Synthesis/Tests/BenchmarkNotationRoundTripCases.lean").read_text()
        imports = [line for line in aggregate.splitlines() if line.startswith("import ")]
        self.assertEqual(imports, [
            "import Whiel.Synthesis.Tests.BenchmarkNotationRoundTrip.Cases.Alpha",
            "import Whiel.Synthesis.Tests.BenchmarkNotationRoundTrip.Cases.Zeta9"])

    def test_round_trip_stale_on_case_added_or_removed(self):
        generator.generate(self.root)
        self.add_input("Beta")
        with self.assertRaisesRegex(generator.RegistryError, "stale"):
            generator.generate(self.root, check=True)
        generator.generate(self.root)
        self.assertTrue((self.root / generator.ROUND_TRIP / "Cases" / "Beta.lean").exists())
        (self.root / "Benchmark/Beta/Input.lean").unlink()
        with self.assertRaisesRegex(generator.RegistryError, "stale"):
            generator.generate(self.root, check=True)
        generator.generate(self.root)
        self.assertFalse((self.root / generator.ROUND_TRIP / "Cases" / "Beta.lean").exists())

    def test_round_trip_unknown_file_refused_before_any_mutation(self):
        generator.generate(self.root)
        (self.root / generator.ROUND_TRIP / "Cases" / "not-safe.lean").write_text("stray")
        self.add_input("Beta")
        before = self.snapshot()
        with self.assertRaisesRegex(generator.RegistryError, "unknown generated file"):
            generator.generate(self.root)
        self.assertEqual(before, self.snapshot())

    def test_round_trip_comment_only_edit_leaves_check_clean(self):
        generator.generate(self.root)
        source = self.root / "Benchmark/Alpha/Input.lean"
        before = (self.root / generator.ROUND_TRIP / "Cases" / "Alpha.lean").read_text()
        source.write_text(source.read_text().replace("import Foo", "import Foo  -- shared"))
        generator.generate(self.root, check=True)
        self.assertEqual(before, (self.root / generator.ROUND_TRIP / "Cases" / "Alpha.lean").read_text())

    def test_contributor_header_is_required_known_and_ordered(self):
        source = self.root / "Benchmark/Alpha/Input.lean"
        text = source.read_text()
        header = text.split("\n", 1)[0]
        for bad, pattern in (
                ("-- Author: Leo Zhang", "missing contributor header"),
                ("-- Benchmark contributors: Leo Zhang, Fangzhu Shen", "out of order"),
                ("-- Benchmark contributors: Val Tannen, Leo Zhang", "out of order"),
                ("-- Benchmark contributors: Leo Zhang, Leo Zhang", "repeated or out of order"),
                ("-- Benchmark contributors: Leo Zhang (converted)", "unknown contributor"),
                ("-- Benchmark contributors: Someone Else", "unknown contributor")):
            source.write_text(text.replace(header, bad, 1))
            with self.assertRaisesRegex(generator.RegistryError, pattern):
                generator.generate(self.root)
        source.write_text(text.replace(
            header, "-- Benchmark contributors: Jesse Comer, Leo Zhang, Sudeepa Roy, Val Tannen", 1))
        generator.generate(self.root)
        # The header is a comment: changing it never moves an identity.
        generator.generate(self.root, check=True)

    def test_carriage_returns_are_refused(self):
        source = self.root / "Benchmark/Alpha/Input.lean"
        source.write_bytes(source.read_bytes().replace(b"\n", b"\r\n"))
        with self.assertRaisesRegex(generator.RegistryError, "carriage return"):
            generator.generate(self.root)

    def test_preprocessed_round_trip_module_per_case_and_aggregate(self):
        generator.generate(self.root)
        base = self.root / generator.PREPROC_ROUND_TRIP
        for case in ("Alpha", "Zeta9"):
            text = (base / "Cases" / f"{case}.lean").read_text()
            self.assertIn(f"import Benchmark.{case}.Input\n", text)
            self.assertIn("import Whiel.Synthesis.Tests.BenchmarkPreprocRoundTrip\n", text)
            self.assertIn(f"#roundTripPreproc Whiel.Benchmark.{case}\n", text)
        aggregate = Path(str(base) + "Cases.lean").read_text()
        self.assertLess(aggregate.index("Cases.Alpha"), aggregate.index("Cases.Zeta9"))
        self.add_input("Beta")
        with self.assertRaisesRegex(generator.RegistryError, "stale"):
            generator.generate(self.root, check=True)
        generator.generate(self.root)
        self.assertTrue((base / "Cases" / "Beta.lean").is_file())
        (base / "Cases" / "stray.txt").write_text("not generated")
        before = self.snapshot()
        with self.assertRaisesRegex(generator.RegistryError, "unknown generated file"):
            generator.generate(self.root)
        self.assertEqual(before, self.snapshot())


if __name__ == "__main__":
    unittest.main()
