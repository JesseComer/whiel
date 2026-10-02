#!/usr/bin/env python3
# Author: Fangzhu Shen
# Framework II adaptation based on her original agent setup.
"""Install or verify the locked, project-local provider CLI; never load auth.

Only --version is executed, after byte and native executable identity checks. Production
confinement and pre-spawn enforcement belong to the Python native runtime. The chmod
modes here are defense in depth, not a replacement for that OS confinement.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import stat
import struct
import subprocess
import sys
import tarfile
import tempfile
import urllib.parse
import urllib.request

REPO = Path(__file__).resolve().parent.parent
VERSION = "0.148.0"
TARGET = "aarch64-apple-darwin"
MODEL = "gpt-5.5"
SUPPORTED_MODELS = ("gpt-5.5", "gpt-5.4", "gpt-5.4-mini", "gpt-5.2")
EFFORTS = ("low", "medium", "high", "xhigh")
TRANSFORMATION = "gpt-5.5-apply-patch-null-v1"
LOCK = Path("agent_houdini/toolchain/cli-lock.json")
FILES = {"executable": "codex", "original_catalog": "models.original.json",
         "catalog": "models.json", "package": "package.tar.gz"}


class SetupError(Exception):
    """A required locked input or runtime artifact is unavailable or changed."""


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SetupError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_hash(path: Path) -> str:
    with path.open("rb") as source:
        digest = hashlib.sha256()
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON object key")
        result[key] = value
    return result


def decode_json(data: bytes) -> dict:
    def invalid_constant(_: str) -> None:
        raise SetupError("non-finite JSON number")
    try:
        value = json.loads(data, object_pairs_hook=unique_object,
                           parse_constant=invalid_constant)
    except (ValueError, UnicodeError) as error:
        raise SetupError("invalid JSON") from error
    require(isinstance(value, dict), "expected JSON object")
    return value


def fields(value: dict, expected: set[str], label: str) -> None:
    require(isinstance(value, dict) and set(value) == expected,
            f"unexpected or missing {label} fields")


def load_lock(repo: Path, target: str | None = None) -> tuple[dict, str]:
    path = repo / LOCK
    for parent in (repo / "agent_houdini", path.parent):
        require(parent.is_dir() and not parent.is_symlink() and parent.resolve() == parent,
                "missing or linked CLI lock parent")
    require(path.is_file() and not path.is_symlink(), "missing or linked CLI lock")
    data = path.read_bytes()
    lock = decode_json(data)
    fields(lock, {"schema_version", "provider", "version", "release_tag",
                  "release_commit", "release_tag_object", "model", "reasoning_effort",
                  "transformation", "packages", "catalog", "authenticity"}, "lock")
    for key, expected in {"schema_version": 2, "provider": "codex", "version": VERSION,
                          "release_tag": f"rust-v{VERSION}",
                          "model": MODEL, "reasoning_effort": "medium",
                          "transformation": TRANSFORMATION}.items():
        require(type(lock[key]) is type(expected) and lock[key] == expected,
                f"unsupported lock {key}")
    for key in ("release_commit", "release_tag_object"):
        require(isinstance(lock[key], str) and re.fullmatch(r"[0-9a-f]{40}", lock[key]) is not None,
                f"invalid {key}")
    fields(lock["packages"], set(TARGETS), "platform packages")
    for package_target, package in lock["packages"].items():
        fields(package, {"url", "sha256", "size", "archive_member", "binary_sha256",
                         "binary_size", "version_output", "release_asset_id"}, "package")
        require(package["url"] == f"https://github.com/openai/codex/releases/download/rust-v{VERSION}/codex-{package_target}.tar.gz",
                "unapproved package URL")
        require(package["archive_member"] == f"codex-{package_target}", "wrong archive member")
        require(package["version_output"] == f"codex-cli {VERSION}", "wrong version pin")
        for key in ("sha256", "binary_sha256"):
            require(isinstance(package[key], str) and re.fullmatch(r"[0-9a-f]{64}", package[key]) is not None,
                    "invalid package SHA256 pin")
        for key in ("size", "binary_size", "release_asset_id"):
            require(type(package[key]) is int and package[key] > 0, "invalid size or asset ID")
    target = target or host_target()
    require(target in TARGETS, "unsupported target")
    lock["target"] = target
    lock["platform"], lock["architecture"] = TARGETS[target]
    lock["package"] = lock.pop("packages")[target]
    package = lock["package"]
    catalog = lock["catalog"]
    fields(catalog, {"url", "original_sha256", "original_size", "modified_sha256"}, "catalog")
    require(catalog["url"] == f"https://raw.githubusercontent.com/openai/codex/{lock['release_commit']}/codex-rs/models-manager/models.json",
            "catalog is not from the pinned official commit")
    for value in (package["sha256"], package["binary_sha256"],
                  catalog["original_sha256"], catalog["modified_sha256"]):
        require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None,
                "invalid SHA256 pin")
    for value in (package["size"], package["binary_size"], package["release_asset_id"], catalog["original_size"]):
        require(type(value) is int and value > 0, "invalid size or asset ID")
    fields(lock["authenticity"], {"package_digest_source", "package_digest_kind",
                                 "tag_signature", "binary_digest_kind", "catalog_digest_kind"}, "authenticity")
    require(lock["authenticity"]["package_digest_source"] ==
            f"https://api.github.com/repos/openai/codex/releases/tags/rust-v{VERSION}",
            "unapproved digest provenance")
    require(lock["authenticity"]["package_digest_kind"] == "github_release_asset_sha256",
            "unsupported package digest provenance")
    require(lock["authenticity"]["tag_signature"] == "unsigned",
            "unsupported signature assertion")
    require(lock["authenticity"]["binary_digest_kind"] == "local_sha256_of_verified_archive_member",
            "unsupported binary digest provenance")
    require(lock["authenticity"]["catalog_digest_kind"] == "local_sha256_of_commit_pinned_https_source",
            "unsupported catalog digest provenance")
    return lock, sha256(data)


def selected_model(data: bytes, model: str = MODEL) -> tuple[dict, int]:
    require(model in SUPPORTED_MODELS, "unsupported Codex model; see --help")
    original = decode_json(data)
    models = original.get("models")
    require(isinstance(models, list) and all(isinstance(m, dict) for m in models),
            "catalog models must be objects")
    indices = [i for i, entry in enumerate(models) if entry.get("slug") == model]
    require(len(indices) == 1, "catalog must contain exactly one selected exact model slug")
    index = indices[0]
    require(models[index].get("apply_patch_tool_type") == "freeform", "wrong original patch type")
    require(models[index].get("tool_mode") is None, "unsupported model tool mode")
    supported = models[index].get("experimental_supported_tools", [])
    require(isinstance(supported, list) and all(isinstance(tool, str) for tool in supported),
            "malformed experimental tools")
    require(not supported, "model exposes unsupported experimental tools")
    return original, index


def validate_effort(data: bytes, model: str, effort: str) -> None:
    original, index = selected_model(data, model)
    levels = original["models"][index].get("supported_reasoning_levels")
    require(isinstance(levels, list) and all(isinstance(level, dict)
            and isinstance(level.get("effort"), str) for level in levels),
            "model lacks supported reasoning levels")
    require(effort in EFFORTS and effort in [level["effort"] for level in levels],
            "unsupported reasoning effort for selected model")


def transform_catalog(data: bytes, model: str = MODEL) -> bytes:
    original, index = selected_model(data, model)
    modified = copy.deepcopy(original)
    modified["models"][index]["apply_patch_tool_type"] = None
    restored = copy.deepcopy(modified)
    restored["models"][index]["apply_patch_tool_type"] = "freeform"
    require(restored == original, "catalog restoration failed")
    return (json.dumps(modified, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode("utf-8")


TARGETS = {"aarch64-apple-darwin": ("darwin", "aarch64"),
           "x86_64-unknown-linux-musl": ("linux", "x86_64"),
           "aarch64-unknown-linux-musl": ("linux", "aarch64")}


def host_target() -> str:
    system, machine = platform.system(), platform.machine()
    if system == "Darwin" and machine in ("arm64", "aarch64"):
        return TARGET
    if system == "Linux" and machine in ("x86_64", "aarch64", "arm64"):
        return f"{'aarch64' if machine == 'arm64' else machine}-unknown-linux-musl"
    raise SetupError("unsupported native platform/architecture; no fallback")


def check_platform(target: str = TARGET) -> None:
    require(host_target() == target, "runtime target differs from native host")


def artifact_root(repo: Path, create: bool, target: str = TARGET) -> Path:
    artifacts = repo / "artifacts"
    if artifacts.is_symlink():
        require(artifacts.resolve() == repo / "artifacts.nosync",
                "artifacts symlink must be the repository's setup_nosync target")
        artifacts = repo / "artifacts.nosync"
    require(not artifacts.is_symlink(), "linked artifacts target")
    for part in (artifacts, artifacts / "provider-cli", artifacts / "provider-cli" / VERSION):
        if create and not part.exists():
            part.mkdir(mode=0o755)
        require(part.is_dir() and not part.is_symlink(), "missing or linked runtime parent")
        require(part.resolve() == part, "runtime parent escapes project")
        require(not part.stat().st_mode & 0o022, "runtime parent is group/world writable")
    return artifacts / "provider-cli" / VERSION / target


def checked_file(path: Path, expected_hash: str, size: int | None, executable: bool = False) -> None:
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1, "runtime file is not a single regular file")
    require(info.st_mode & 0o777 == (0o555 if executable else 0o444), "runtime file permissions changed")
    require(size is None or info.st_size == size, "runtime file size changed")
    require(file_hash(path) == expected_hash, "runtime file digest changed")


def check_macho(path: Path) -> None:
    with path.open("rb") as source:
        header = source.read(16)
    require(len(header) == 16 and struct.unpack("<4I", header)[:2] == (0xFEEDFACF, 0x0100000C)
            and struct.unpack("<4I", header)[3] == 2, "binary is not an arm64 Mach-O executable")


def check_binary(path: Path, target: str) -> None:
    if target == TARGET:
        check_macho(path)
        return
    require(target in TARGETS, "unsupported executable target")
    with path.open("rb") as source:
        header = source.read(20)
    machine = 183 if target.startswith("aarch64-") else 62
    require(len(header) == 20 and header[:7] == b"\x7fELF\x02\x01\x01"
            and int.from_bytes(header[16:18], "little") in (2, 3)
            and int.from_bytes(header[18:20], "little") == machine,
            "binary ELF identity differs from native target")


def check_version(path: Path) -> str:
    result = subprocess.run([str(path), "--version"], stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            cwd=path.parent, env={"PATH": "/usr/bin:/bin"}, timeout=15,
                            check=False)
    require(result.returncode == 0 and result.stdout == f"codex-cli {VERSION}\n".encode(),
            "CLI version output does not match pin")
    return result.stdout.decode().strip()


def verify(repo: Path, lock: dict, lock_hash: str, model: str = MODEL, effort: str = "medium") -> dict:
    require(model in SUPPORTED_MODELS, "unsupported Codex model; see --help")
    check_platform(lock["target"])
    root = artifact_root(repo, create=False, target=lock["target"])
    require(root.is_dir() and not root.is_symlink() and root.resolve() == root, "missing or linked runtime directory")
    require(root.stat().st_mode & 0o777 == 0o555, "runtime directory permissions changed")
    require({p.name for p in root.iterdir()} == set(FILES.values()), "missing or unexpected runtime artifacts")
    p, c = lock["package"], lock["catalog"]
    checked_file(root / FILES["package"], p["sha256"], p["size"])
    checked_file(root / FILES["executable"], p["binary_sha256"], p["binary_size"], executable=True)
    checked_file(root / FILES["original_catalog"], c["original_sha256"], c["original_size"])
    checked_file(root / FILES["catalog"], c["modified_sha256"], None)
    expected = transform_catalog((root / FILES["original_catalog"]).read_bytes())
    require(expected == (root / FILES["catalog"]).read_bytes(), "catalog transformation differs")
    original = (root / FILES["original_catalog"]).read_bytes()
    validate_effort(original, model, effort)
    selected_catalog = root / FILES["catalog"]
    selected_bytes = transform_catalog(original, model)
    if model != MODEL:
        selected_catalog = derived_catalog_path(root, model, create=False)
        checked_file(selected_catalog, sha256(selected_bytes), len(selected_bytes))
    check_binary(root / FILES["executable"], lock["target"])
    check_version(root / FILES["executable"])
    return {"schema_version": 1, "provider": "codex", "version": VERSION,
            "release_tag": lock["release_tag"], "release_commit": lock["release_commit"],
            "platform": lock["platform"], "architecture": lock["architecture"], "model": model,
            "reasoning_effort": effort, **{key: str(root / FILES[key]) for key in FILES},
            "catalog": str(selected_catalog),
            "package_sha256": p["sha256"], "binary_sha256": p["binary_sha256"],
            "original_catalog_sha256": c["original_sha256"], "catalog_sha256": sha256(selected_bytes),
            "transformation": f"{model}-apply-patch-null-v1", "lock_sha256": lock_hash}


def derived_catalog_path(root: Path, model: str, create: bool) -> Path:
    # Each model has its own immutable catalog; the base runtime stays frozen.
    parent = root.parent / "catalogs" / root.name / model
    for directory in (parent.parent.parent, parent.parent, parent):
        if create and not directory.exists():
            directory.mkdir(mode=0o755)
        require(directory.is_dir() and not directory.is_symlink()
                and directory.resolve() == directory
                and not directory.stat().st_mode & 0o022,
                "missing or unsafe selected-model catalog directory")
    return parent / "models.json"


def prepare_model(repo: Path, lock: dict, lock_hash: str, model: str, effort: str) -> dict:
    require(model in SUPPORTED_MODELS and effort in EFFORTS,
            "unsupported Codex model or reasoning effort")
    install(repo, lock, lock_hash)
    root = artifact_root(repo, create=False, target=lock["target"])
    original = (root / FILES["original_catalog"]).read_bytes()
    validate_effort(original, model, effort)
    if model != MODEL:
        target = derived_catalog_path(root, model, create=True)
        expected = transform_catalog(original, model)
        if not target.exists() and not target.is_symlink():
            descriptor, name = tempfile.mkstemp(prefix=".catalog-", dir=target.parent)
            staged = Path(name)
            try:
                with os.fdopen(descriptor, "wb") as output:
                    output.write(expected)
                staged.chmod(0o444)
                # Exclusive publication: another setup never replaces our file.
                try:
                    os.link(staged, target)
                except FileExistsError:
                    pass
            finally:
                staged.unlink()
    return verify(repo, lock, lock_hash, model, effort)


class OfficialRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        parsed = urllib.parse.urlsplit(newurl)
        require(parsed.scheme == "https" and parsed.hostname in
                {"github.com", "release-assets.githubusercontent.com", "objects.githubusercontent.com", "raw.githubusercontent.com"}
                and not parsed.username and not parsed.password, "unapproved download redirect")
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def download(url: str, destination: Path, expected_hash: str, expected_size: int) -> None:
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), OfficialRedirect())
    digest, total = hashlib.sha256(), 0
    with opener.open(url, timeout=60) as response, destination.open("xb") as output:
        while chunk := response.read(1024 * 1024):
            total += len(chunk)
            require(total <= expected_size, "download exceeds pinned size")
            output.write(chunk)
            digest.update(chunk)
    require(total == expected_size and digest.hexdigest() == expected_hash, "download identity mismatch")


def extract_binary(archive: Path, destination: Path, package: dict, target: str = TARGET) -> None:
    with tarfile.open(archive, "r:gz") as source:
        members = source.getmembers()
        require(len(members) == 1, "archive must contain exactly one binary")
        member = members[0]
        require(member.name == package["archive_member"] and member.isfile()
                and not member.issym() and not member.islnk()
                and member.size == package["binary_size"], "unsafe or unexpected archive member")
        stream = source.extractfile(member)
        require(stream is not None, "archive binary is unreadable")
        with stream, destination.open("xb") as output:
            shutil.copyfileobj(stream, output, 1024 * 1024)
    require(file_hash(destination) == package["binary_sha256"], "extracted binary digest mismatch")
    check_binary(destination, target)


def install(repo: Path, lock: dict, lock_hash: str) -> dict:
    check_platform(lock["target"])
    root = artifact_root(repo, create=True, target=lock["target"])
    if root.exists() or root.is_symlink():
        return verify(repo, lock, lock_hash)
    staging = Path(tempfile.mkdtemp(prefix=".setup-", dir=root.parent))
    try:
        p, c = lock["package"], lock["catalog"]
        download(p["url"], staging / FILES["package"], p["sha256"], p["size"])
        download(c["url"], staging / FILES["original_catalog"], c["original_sha256"], c["original_size"])
        extract_binary(staging / FILES["package"], staging / FILES["executable"], p, lock["target"])
        transformed = transform_catalog((staging / FILES["original_catalog"]).read_bytes())
        require(sha256(transformed) == c["modified_sha256"], "modified catalog digest mismatch")
        (staging / FILES["catalog"]).write_bytes(transformed)
        for key, name in FILES.items():
            (staging / name).chmod(0o555 if key == "executable" else 0o444)
        check_version(staging / FILES["executable"])
        require(not root.exists() and not root.is_symlink(), "runtime appeared during setup")
        staging.rename(root)
        root.chmod(0o555)
    finally:
        if staging.exists():
            shutil.rmtree(staging)
    return verify(repo, lock, lock_hash)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", action="store_true", help="verify only; never download or repair")
    parser.add_argument("--json", action="store_true", help="print the structured frozen CLI identity")
    parser.add_argument("--model", default=MODEL, choices=SUPPORTED_MODELS)
    parser.add_argument("--reasoning-effort", default="medium", choices=EFFORTS)
    args = parser.parse_args(argv)
    try:
        lock, lock_hash = load_lock(REPO)
        identity = (verify(REPO, lock, lock_hash, args.model, args.reasoning_effort)
                    if args.verify_only else prepare_model(REPO, lock, lock_hash, args.model, args.reasoning_effort))
        print(json.dumps(identity, sort_keys=True) if args.json else f"verified Codex {VERSION}: {identity['executable']}")
        return 0
    except (SetupError, OSError, ValueError, tarfile.TarError, subprocess.SubprocessError) as error:
        print(json.dumps({"schema_version": 1, "error": str(error)}) if args.json else f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
