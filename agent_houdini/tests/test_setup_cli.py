# Author: Fangzhu Shen
# Framework II adaptation based on her original agent setup.
"""Focused setup boundary tests. Synthetic binaries are never executed."""
import copy
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import urllib.request

SOURCE = Path(__file__).resolve().parents[1] / "setup_cli.py"
SPEC = importlib.util.spec_from_file_location("setup_provider_cli", SOURCE)
cli = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cli)
RAW_LOCK = json.loads((SOURCE.parent.parent / cli.LOCK).read_text())
REAL_LOCK, _ = cli.load_lock(SOURCE.parent.parent, cli.TARGET)


def catalog():
    return {"metadata": {"kept": [1, "λ", None]}, "models": [
        {"slug": "gpt-5.4", "apply_patch_tool_type": "freeform",
         "supported_reasoning_levels": [{"effort": "low"}, {"effort": "medium"}]},
        {"slug": "gpt-5.5", "apply_patch_tool_type": "freeform", "tool_mode": None,
         "experimental_supported_tools": [],
         "supported_reasoning_levels": [{"effort": "medium"}, {"effort": "high"}], "instructions": "complete original instruction",
         "context_window": 123, "nested": {"semantics": [True, 17]}}]}


def encoded(value):
    return json.dumps(value, ensure_ascii=False).encode()


def archive_bytes(binary, name=None, kind=tarfile.REGTYPE, extra=False):
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode="w:gz") as archive:
        member = tarfile.TarInfo(name or f"codex-{cli.TARGET}")
        member.type = kind
        member.size = len(binary) if kind == tarfile.REGTYPE else 0
        member.linkname = "../../outside"
        archive.addfile(member, io.BytesIO(binary) if member.isfile() else None)
        if extra:
            archive.addfile(tarfile.TarInfo("extra"))
    return output.getvalue()


class CatalogTests(unittest.TestCase):
    def test_only_exact_patch_field_changes_and_restores_entire_catalog(self):
        original = catalog()
        transformed = cli.decode_json(cli.transform_catalog(encoded(original)))
        self.assertIsNone(transformed["models"][1]["apply_patch_tool_type"])
        transformed["models"][1]["apply_patch_tool_type"] = "freeform"
        self.assertEqual(original, transformed)

    def test_missing_duplicate_or_approximate_model_is_rejected(self):
        for slug in ("openai/gpt-5.5", "gpt-5.5-extra", "gpt-5", None):
            value = catalog()
            value["models"][1]["slug"] = slug
            with self.subTest(slug=slug), self.assertRaises(cli.SetupError):
                cli.transform_catalog(encoded(value))
        value = catalog()
        value["models"].append(copy.deepcopy(value["models"][1]))
        with self.assertRaises(cli.SetupError):
            cli.transform_catalog(encoded(value))

    def test_unsupported_metadata_is_rejected(self):
        for key, value in (("apply_patch_tool_type", None), ("tool_mode", "code"),
                           ("experimental_supported_tools", ["test_sync_tool"]),
                           ("experimental_supported_tools", None),
                           ("experimental_supported_tools", [1])):
            model_catalog = catalog()
            model_catalog["models"][1][key] = value
            with self.subTest(key=key, value=value), self.assertRaises(cli.SetupError):
                cli.transform_catalog(encoded(model_catalog))

    def test_duplicate_keys_nonfinite_and_nonobject_json_are_rejected(self):
        for raw in (b'{"models": [], "models": []}', b'{"x": NaN}', b'[]', b'\xff'):
            with self.subTest(raw=raw), self.assertRaises(cli.SetupError):
                cli.decode_json(raw)


class SetupTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.repo = Path(self.temporary.name).resolve()
        self.binary = struct.pack("<4I", 0xFEEDFACF, 0x0100000C, 0, 2) + b"synthetic non-executable"
        self.original = encoded(catalog())
        self.modified = cli.transform_catalog(self.original)
        self.archive = archive_bytes(self.binary)
        self.lock = copy.deepcopy(REAL_LOCK)
        self.lock["package"].update(sha256=cli.sha256(self.archive), size=len(self.archive),
                                    binary_sha256=cli.sha256(self.binary), binary_size=len(self.binary))
        self.lock["catalog"].update(original_sha256=cli.sha256(self.original),
                                    original_size=len(self.original), modified_sha256=cli.sha256(self.modified))
        (self.repo / cli.LOCK).parent.mkdir(parents=True)
        self.write_lock(self.lock)
        self.platform = patch.object(cli, "check_platform")
        self.platform.start()
        self.version = patch.object(cli, "check_version", return_value="codex-cli 0.148.0")
        self.version_mock = self.version.start()
        self.addCleanup(self.platform.stop)
        self.addCleanup(self.version.stop)
        self.addCleanup(self.cleanup)

    def write_lock(self, selected):
        raw = copy.deepcopy(RAW_LOCK)
        raw.update({k: v for k, v in selected.items() if k not in ("package", "platform", "architecture", "target")})
        raw["packages"][cli.TARGET] = selected["package"]
        (self.repo / cli.LOCK).write_bytes(encoded(raw))

    def cleanup(self):
        for root, dirs, files in os.walk(self.repo):
            Path(root).chmod(0o755)
            for name in files:
                path = Path(root) / name
                if not path.is_symlink():
                    path.chmod(0o644)
        self.temporary.cleanup()

    def download(self, url, destination, digest, size):
        value = self.archive if url == self.lock["package"]["url"] else self.original
        self.assertEqual((cli.sha256(value), len(value)), (digest, size))
        destination.write_bytes(value)

    def install(self):
        with patch.object(cli, "download", side_effect=self.download) as download:
            identity = cli.install(self.repo, self.lock, "a" * 64)
        self.assertEqual(download.call_count, 2)
        return identity

    def root(self):
        return self.repo / "artifacts" / "provider-cli" / cli.VERSION / cli.TARGET

    def test_clean_install_and_network_free_verification(self):
        identity = self.install()
        with patch.object(cli, "download", side_effect=AssertionError("network during verification")):
            self.assertEqual(identity, cli.verify(self.repo, self.lock, "a" * 64))
            self.assertEqual(identity, cli.install(self.repo, self.lock, "a" * 64))
        self.assertEqual(identity["executable"], str(self.root() / "codex"))
        self.assertEqual(identity["catalog_sha256"], cli.sha256(self.modified))
        self.assertEqual(identity["architecture"], "aarch64")
        self.assertEqual((self.root() / "models.original.json").read_bytes(), self.original)

    def test_every_changed_artifact_is_rejected_before_execution(self):
        self.install()
        for name in cli.FILES.values():
            path = self.root() / name
            original = path.read_bytes()
            path.chmod(0o644)
            path.write_bytes(bytes([original[0] ^ 1]) + original[1:])
            path.chmod(0o555 if name == "codex" else 0o444)
            self.version_mock.reset_mock()
            with self.subTest(name=name), self.assertRaises(cli.SetupError):
                cli.verify(self.repo, self.lock, "a" * 64)
            self.version_mock.assert_not_called()
            path.chmod(0o644)
            path.write_bytes(original)
            path.chmod(0o555 if name == "codex" else 0o444)

    def test_changed_install_is_not_repaired(self):
        self.install()
        target = self.root() / "models.json"
        target.chmod(0o644)
        target.write_bytes(b"changed")
        with patch.object(cli, "download", side_effect=AssertionError("repair download")):
            with self.assertRaises(cli.SetupError):
                cli.install(self.repo, self.lock, "a" * 64)
        self.assertEqual(target.read_bytes(), b"changed")

    def test_missing_extra_permission_and_linked_artifacts_fail(self):
        self.install()
        root = self.root()
        root.chmod(0o755)
        with self.assertRaises(cli.SetupError):
            cli.verify(self.repo, self.lock, "a" * 64)
        root.chmod(0o555)
        target = root / "models.json"
        target.chmod(0o644)
        with self.assertRaises(cli.SetupError):
            cli.verify(self.repo, self.lock, "a" * 64)
        target.chmod(0o444)
        root.chmod(0o755)
        target.unlink()
        root.chmod(0o555)
        with self.assertRaises(cli.SetupError):
            cli.verify(self.repo, self.lock, "a" * 64)
        root.chmod(0o755)
        target.symlink_to(root / "models.original.json")
        root.chmod(0o555)
        with self.assertRaises(cli.SetupError):
            cli.verify(self.repo, self.lock, "a" * 64)
        root.chmod(0o755)
        target.unlink()
        os.link(root / "models.original.json", target)
        root.chmod(0o555)
        with self.assertRaises(cli.SetupError):
            cli.verify(self.repo, self.lock, "a" * 64)
        root.chmod(0o755)
        target.unlink()
        target.write_bytes(self.modified)
        target.chmod(0o444)
        (root / "extra").write_text("unexpected")
        root.chmod(0o555)
        with self.assertRaises(cli.SetupError):
            cli.verify(self.repo, self.lock, "a" * 64)

    def test_runtime_parent_symlink_is_rejected(self):
        (self.repo / "outside").mkdir()
        (self.repo / "artifacts").symlink_to(self.repo / "outside")
        with self.assertRaises(cli.SetupError):
            cli.artifact_root(self.repo, create=True)

    def test_nosync_target_is_allowed_but_further_symlink_is_not(self):
        (self.repo / "artifacts.nosync").mkdir()
        (self.repo / "artifacts").symlink_to(self.repo / "artifacts.nosync")
        root = cli.artifact_root(self.repo, create=True)
        self.assertEqual(root, self.repo / "artifacts.nosync/provider-cli" / cli.VERSION / cli.TARGET)
        shutil.rmtree(self.repo / "artifacts.nosync/provider-cli")
        (self.repo / "outside").mkdir()
        (self.repo / "artifacts.nosync/provider-cli").symlink_to(self.repo / "outside")
        with self.assertRaises(cli.SetupError):
            cli.artifact_root(self.repo, create=True)

    def test_wrong_architecture_is_rejected_even_with_updated_digest(self):
        self.install()
        target = self.root() / "codex"
        wrong = struct.pack("<4I", 0xFEEDFACF, 0x01000007, 0, 2) + self.binary[16:]
        target.chmod(0o644)
        target.write_bytes(wrong)
        target.chmod(0o555)
        self.lock["package"]["binary_sha256"] = cli.sha256(wrong)
        self.version_mock.reset_mock()
        with self.assertRaisesRegex(cli.SetupError, "arm64"):
            cli.verify(self.repo, self.lock, "a" * 64)
        self.version_mock.assert_not_called()

    def test_failed_install_never_publishes_partial_runtime(self):
        def interrupted(*args):
            raise cli.SetupError("interrupted download")
        with patch.object(cli, "download", side_effect=interrupted):
            with self.assertRaises(cli.SetupError):
                cli.install(self.repo, self.lock, "a" * 64)
        self.assertFalse(self.root().exists())
        self.assertEqual(list(self.root().parent.iterdir()), [])
        self.version_mock.assert_not_called()

    def test_verify_only_missing_runtime_and_wrong_model_never_download(self):
        with patch.object(cli, "REPO", self.repo), patch.object(cli, "download") as download:
            with patch("sys.stderr", new_callable=io.StringIO) as error:
                self.assertEqual(cli.main(["--verify-only", "--json"]), 1)
                self.assertIn("error", json.loads(error.getvalue()))
            for model in ("openai/gpt-5.5", "gpt-5.5-extra"):
                with patch("sys.stderr", new_callable=io.StringIO), self.assertRaises(SystemExit):
                    cli.main(["--json", "--model", model])
            download.assert_not_called()
            self.version_mock.assert_not_called()

    def test_selected_model_catalogs_coexist_and_verify_without_writes(self):
        original = self.install()
        selected = cli.prepare_model(self.repo, self.lock, "a" * 64, "gpt-5.4", "low")
        self.assertNotEqual(original["catalog"], selected["catalog"])
        self.assertEqual(Path(original["catalog"]).read_bytes(), self.modified)
        catalog_path = Path(selected["catalog"])
        before = catalog_path.stat().st_mtime_ns
        checked = cli.verify(self.repo, self.lock, "a" * 64, "gpt-5.4", "medium")
        self.assertEqual(checked["model"], "gpt-5.4")
        self.assertEqual(checked["reasoning_effort"], "medium")
        self.assertEqual(catalog_path.stat().st_mtime_ns, before)
        restored = cli.decode_json(catalog_path.read_bytes())
        restored["models"][0]["apply_patch_tool_type"] = "freeform"
        self.assertEqual(restored, cli.decode_json(self.original))
        self.assertEqual(cli.verify(self.repo, self.lock, "a" * 64)["catalog"], original["catalog"])

    def test_selected_model_missing_tampered_linked_and_effort_fail_closed(self):
        self.install()
        with self.assertRaises(cli.SetupError):
            cli.verify(self.repo, self.lock, "a" * 64, "gpt-5.4", "low")
        selected = cli.prepare_model(self.repo, self.lock, "a" * 64, "gpt-5.4", "low")
        with self.assertRaises(cli.SetupError):
            cli.verify(self.repo, self.lock, "a" * 64, "gpt-5.4", "high")
        target = Path(selected["catalog"])
        target.chmod(0o644)
        target.write_bytes(self.modified)
        target.chmod(0o444)
        with self.assertRaises(cli.SetupError):
            cli.verify(self.repo, self.lock, "a" * 64, "gpt-5.4", "low")
        target.unlink()
        target.symlink_to(self.root() / "models.json")
        with self.assertRaises(cli.SetupError):
            cli.prepare_model(self.repo, self.lock, "a" * 64, "gpt-5.4", "low")

    def test_strict_lock_refuses_unapproved_fields_and_values(self):
        for key, value in (("version", "0.149.0"), ("provider", "other"),
                           ("schema_version", True), ("model", "gpt-5.5-extra"), ("extra", 1)):
            changed = copy.deepcopy(self.lock)
            changed[key] = value
            self.write_lock(changed)
            with self.subTest(key=key), self.assertRaises(cli.SetupError):
                cli.load_lock(self.repo)
        for key, value in (("url", "https://example.com/package"), ("sha256", "z" * 64),
                           ("size", True), ("archive_member", "../codex"), ("extra", 1)):
            changed = copy.deepcopy(self.lock)
            changed["package"][key] = value
            self.write_lock(changed)
            with self.subTest(key=key), self.assertRaises(cli.SetupError):
                cli.load_lock(self.repo)

    def test_linked_lock_parent_is_rejected(self):
        (self.repo / "agent_houdini").rename(self.repo / "alternate")
        (self.repo / "agent_houdini").symlink_to(self.repo / "alternate")
        with self.assertRaises(cli.SetupError):
            cli.load_lock(self.repo)

    def test_unsafe_archive_members_are_not_extracted(self):
        for name, kind, extra in (("../escape", tarfile.REGTYPE, False),
                                  (None, tarfile.SYMTYPE, False),
                                  (None, tarfile.LNKTYPE, False),
                                  (None, tarfile.REGTYPE, True)):
            archive = self.repo / "input.tar.gz"
            archive.write_bytes(archive_bytes(self.binary, name, kind, extra))
            output = self.repo / "output"
            with self.subTest(name=name, kind=kind, extra=extra), self.assertRaises(cli.SetupError):
                cli.extract_binary(archive, output, self.lock["package"])
            self.assertFalse(output.exists())
            self.assertFalse((self.repo.parent / "escape").exists())


class ExternalBoundaryTests(unittest.TestCase):
    def test_linux_platform_selection_and_locked_packages(self):
        for machine, target in (("x86_64", "x86_64-unknown-linux-musl"),
                                ("aarch64", "aarch64-unknown-linux-musl")):
            with patch.object(cli.platform, "system", return_value="Linux"), \
                 patch.object(cli.platform, "machine", return_value=machine):
                self.assertEqual(cli.host_target(), target)
                lock, _ = cli.load_lock(SOURCE.parent.parent)
                self.assertEqual((lock["platform"], lock["architecture"]), ("linux", machine))
                self.assertEqual(lock["package"]["archive_member"], f"codex-{target}")

    def test_elf_machine_class_and_type_must_match_target(self):
        with tempfile.TemporaryDirectory() as temp:
            binary = Path(temp) / "binary"
            for target, machine in (("x86_64-unknown-linux-musl", 62),
                                    ("aarch64-unknown-linux-musl", 183)):
                header = b"\x7fELF\x02\x01\x01" + bytes(9) + struct.pack("<HH", 2, machine)
                binary.write_bytes(header)
                cli.check_binary(binary, target)
                for bad in (header[:4] + b"\x01" + header[5:], header[:18] + b"\x00\x00",
                            header[:16] + b"\x01\x00" + header[18:]):
                    binary.write_bytes(bad)
                    with self.assertRaises(cli.SetupError):
                        cli.check_binary(binary, target)

    def test_host_platform_has_no_fallback(self):
        for system, machine in (("Linux", "riscv64"), ("Darwin", "x86_64")):
            with patch.object(cli.platform, "system", return_value=system), \
                 patch.object(cli.platform, "machine", return_value=machine):
                with self.assertRaises(cli.SetupError):
                    cli.check_platform()

    def test_version_uses_only_exact_binary_and_minimal_environment(self):
        executable = Path("/project/artifacts/provider-cli/codex")
        for status, output, accepted in ((0, b"codex-cli 0.148.0\n", True),
                                          (0, b"codex-cli 0.145.0\n", False),
                                          (1, b"codex-cli 0.148.0\n", False)):
            result = subprocess.CompletedProcess([], status, stdout=output, stderr=b"")
            with patch.object(cli.subprocess, "run", return_value=result) as run:
                if accepted:
                    cli.check_version(executable)
                else:
                    with self.assertRaises(cli.SetupError):
                        cli.check_version(executable)
                args, kwargs = run.call_args
                self.assertEqual(args[0], [str(executable), "--version"])
                self.assertEqual(kwargs["env"], {"PATH": "/usr/bin:/bin"})
                self.assertEqual(kwargs["stdin"], subprocess.DEVNULL)

    def test_download_refuses_size_and_hash_mismatch(self):
        for size, digest in ((2, cli.sha256(b"abc")), (4, cli.sha256(b"abc")), (3, "0" * 64)):
            with tempfile.TemporaryDirectory() as temp:
                response = io.BytesIO(b"abc")
                with patch.object(cli.urllib.request, "build_opener") as opener:
                    opener.return_value.open.return_value = response
                    with self.assertRaises(cli.SetupError):
                        cli.download("https://github.com/openai/codex", Path(temp) / "download", digest, size)
                    handlers = opener.call_args.args
                    self.assertEqual(handlers[0].proxies, {})

    def test_redirect_cannot_leave_official_https_hosts(self):
        request = urllib.request.Request("https://github.com/openai/codex")
        for url in ("http://github.com/file", "https://example.com/file", "https://user:password@github.com/file"):
            with self.subTest(url=url), self.assertRaises(cli.SetupError):
                cli.OfficialRedirect().redirect_request(request, None, 302, "Found", {}, url)


if __name__ == "__main__":
    unittest.main()
