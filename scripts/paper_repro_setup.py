"""PAPER REPRODUCTION CODE: additive installation and independent worker login."""
from __future__ import annotations

import hashlib
import os
from pathlib import Path
import platform
import re
import shutil
import stat
import sys
import tarfile
import tempfile
import urllib.parse
import urllib.request
import uuid

from scripts.paper_repro_common import ReproError, atomic_json, command, digest, read_json, require

VERSIONS = ("0.148.0", "0.154.0")
TARGET = "x86_64-unknown-linux-musl"
ASTRA_API = "https://api.github.com/repos/openai/codex/releases/tags/rust-v0.154.0"
ASTRA_URL = ("https://github.com/openai/codex/releases/download/rust-v0.154.0/"
             f"codex-{TARGET}.tar.gz")
MEMBER = f"codex-{TARGET}"
HOSTS = {"api.github.com", "github.com", "release-assets.githubusercontent.com",
         "objects.githubusercontent.com"}


def cli_path(ctx, version):
    """Return the fixed project-local executable path; perform no execution."""
    require(version in VERSIONS, "Unsupported paper Codex version.")
    return ctx.repo / "artifacts" / "provider-cli" / version / TARGET / "codex"


def _log(ctx, label):
    return ctx.output_root / "setup-logs" / f"{label}-{uuid.uuid4().hex}.log"


def _native(path):
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1 and
            info.st_mode & 0o111 and not info.st_mode & 0o022,
            "Codex must be an unlinked, non-writable native executable.")
    with path.open("rb") as stream:
        header = stream.read(20)
    require(len(header) == 20 and header[:7] == b"\x7fELF\x02\x01\x01" and
            int.from_bytes(header[16:18], "little") in (2, 3) and
            int.from_bytes(header[18:20], "little") == 62,
            "Codex must be a Linux x86_64 ELF executable.")


def _version(ctx, path, version):
    log = _log(ctx, f"codex-{version}-version")
    command(ctx, ["timeout", "--signal=TERM", "--kill-after=5", "15", str(path), "--version"],
            log, env={"PATH": os.defpath}, cleanup_group=True)
    require(log.read_bytes() == f"codex-cli {version}\n".encode(),
            f"Codex version must be exactly {version}; inspect {ctx.rel(log)}.")


def _metadata(value):
    require(isinstance(value, dict) and value.get("tag_name") == "rust-v0.154.0" and
            value.get("draft") is False, "Unexpected official Codex release metadata.")
    assets = value.get("assets")
    require(isinstance(assets, list), "Official release asset list is missing.")
    matches = [row for row in assets if isinstance(row, dict) and
               row.get("name") == MEMBER + ".tar.gz"]
    require(len(matches) == 1, "Expected one official Linux x86_64 Codex archive.")
    asset = matches[0]
    require(asset.get("browser_download_url") == ASTRA_URL,
            "Unexpected Codex release download URL.")
    require(type(asset.get("size")) is int and asset["size"] > 0 and
            type(asset.get("id")) is int and asset["id"] > 0,
            "Official release asset size/identity is missing.")
    checksum = asset.get("digest")
    require(isinstance(checksum, str) and re.fullmatch(r"sha256:[0-9a-f]{64}", checksum),
            "Official release has no published SHA-256; refusing an unverified download.")
    return asset


class _Redirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, fp, code, message, headers, url):
        parsed = urllib.parse.urlsplit(url)
        require(parsed.scheme == "https" and parsed.hostname in HOSTS and
                not parsed.username and not parsed.password and parsed.port in (None, 443),
                "Unofficial Codex download redirect refused.")
        return super().redirect_request(request, fp, code, message, headers, url)


def _download(url, path, maximum, expected_hash=None):
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), _Redirect())
    request = urllib.request.Request(url, headers={"User-Agent": "whiel-paper-reproduction",
                                                 "Accept": "application/vnd.github+json"}
                                     if url == ASTRA_API else
                                     {"User-Agent": "whiel-paper-reproduction"})
    total = 0
    checksum = hashlib.sha256()
    with opener.open(request, timeout=60) as response, path.open("xb") as stream:
        while chunk := response.read(1024 * 1024):
            total += len(chunk)
            require(total <= maximum, "Codex download exceeds its published size.")
            checksum.update(chunk)
            stream.write(chunk)
    if expected_hash is not None:
        require(total == maximum and checksum.hexdigest() == expected_hash,
                "Codex archive differs from the official release digest or size.")


def _extract(archive, binary):
    with tarfile.open(archive, "r:gz") as stream:
        members = stream.getmembers()
        require(len(members) == 1, "Codex archive must contain exactly one binary.")
        member = members[0]
        require(member.name == MEMBER and member.isfile() and member.size > 0,
                "Codex archive member must be the named regular binary.")
        source = stream.extractfile(member)
        require(source is not None, "Codex archive member cannot be read.")
        with source, binary.open("xb") as target:
            shutil.copyfileobj(source, target)
        require(binary.stat().st_size == member.size, "Truncated Codex archive member.")
    binary.chmod(0o555)
    _native(binary)


def _artifact_parent(ctx, path):
    artifacts = (ctx.repo / "artifacts").resolve()
    require(artifacts == ctx.repo / "artifacts" or artifacts == ctx.repo / "artifacts.nosync",
            "Unexpected artifacts symlink target.")
    artifacts.mkdir(exist_ok=True)
    require(path.resolve().is_relative_to(artifacts), "CLI installation escapes artifacts/.")
    current = artifacts
    for component in path.relative_to(ctx.repo / "artifacts").parts:
        current = current / component
        current.mkdir(exist_ok=True)
        info = current.lstat()
        require(stat.S_ISDIR(info.st_mode) and not info.st_mode & 0o022,
                "CLI installation parent is linked or writable by other users.")
    return current


def _install_astra(ctx):
    binary = cli_path(ctx, "0.154.0")
    if binary.parent.exists() or binary.parent.is_symlink():
        return verify_cli(ctx, "0.154.0")
    parent = _artifact_parent(ctx, binary.parent.parent)
    with tempfile.TemporaryDirectory(prefix=".codex-download-", dir=parent) as temporary:
        stage = Path(temporary)
        metadata_path = stage / "release.json"
        _download(ASTRA_API, metadata_path, 2 * 1024 * 1024)
        asset = _metadata(read_json(metadata_path))
        archive = stage / "package.tar.gz"
        _download(ASTRA_URL, archive, asset["size"], asset["digest"].split(":", 1)[1])
        _extract(archive, stage / "codex")
        _version(ctx, stage / "codex", "0.154.0")
        atomic_json(stage / "installation.json", {
            "schema_version": 1, "version": "0.154.0", "target": TARGET,
            "metadata_url": ASTRA_API, "archive_url": ASTRA_URL,
            "asset_id": asset["id"], "archive_sha256": asset["digest"].split(":", 1)[1],
            "archive_size": asset["size"], "binary_sha256": digest(stage / "codex"),
            "binary_size": (stage / "codex").stat().st_size,
            "provenance": "Official release metadata fetched at setup; not a shipped paper binary pin.",
        })
        for path in stage.iterdir():
            path.chmod(0o555 if path.name == "codex" else 0o444)
        require(not binary.parent.exists(), "Codex destination appeared during setup.")
        stage.rename(binary.parent)
    return verify_cli(ctx, "0.154.0")


def verify_cli(ctx, version):
    """Check native bytes/provenance and exact version, returning its Path."""
    path = cli_path(ctx, version)
    require(path.is_file(), f"Missing Codex {version}; run setup first.")
    _native(path)
    if version == "0.148.0":
        package = read_json(ctx.repo / "agent_houdini/toolchain/cli-lock.json")["packages"][TARGET]
        require(path.stat().st_size == package["binary_size"] and
                digest(path) == package["binary_sha256"], "Codex 0.148.0 differs from its shipped pin.")
    else:
        receipt = read_json(path.parent / "installation.json")
        asset = _metadata(read_json(path.parent / "release.json"))
        expected = {"schema_version": 1, "version": version, "target": TARGET,
                    "metadata_url": ASTRA_API, "archive_url": ASTRA_URL,
                    "asset_id": asset["id"], "archive_size": asset["size"],
                    "archive_sha256": asset["digest"].split(":", 1)[1]}
        require(all(receipt.get(key) == value for key, value in expected.items()),
                "Codex 0.154.0 installation provenance disagrees with its release metadata.")
        archive = path.parent / "package.tar.gz"
        require(archive.stat().st_size == asset["size"] and digest(archive) == expected["archive_sha256"] and
                path.stat().st_size == receipt.get("binary_size") and
                digest(path) == receipt.get("binary_sha256"), "Codex 0.154.0 installation bytes changed.")
    _version(ctx, path, version)
    return path


def _requirements(ctx):
    require(platform.system() == "Linux" and platform.machine() == "x86_64",
            "Paper reproduction requires Linux x86_64.")
    require(sys.version_info >= (3, 11), "Python 3.11 or newer is required.")
    from agent_houdini.bwrap import SandboxError, python_relay_resources

    try:
        interpreter, _ = python_relay_resources(
            Path(sys.executable), (ctx.repo / "agent_houdini/mcp_stdio.py").resolve())
    except (OSError, SandboxError) as error:
        raise ReproError(f"Unsupported Python relay environment: {error}") from error
    python = shutil.which("python3")
    require(python is not None and Path(python).resolve() == interpreter,
            "python3 on PATH must select the same system interpreter used for this command.")
    tools = ("git", "cargo", "elan", "lake", "cc", "c++", "cmake", "make", "ps",
             "pgrep", "pkill", "parallel", "taskset", "lscpu", "bwrap", "timeout")
    missing = [name for name in tools if shutil.which(name) is None]
    require(not missing, "Install required system tools: " + ", ".join(missing))


def setup(ctx):
    """Install pinned dependencies and build with the existing public commands."""
    _requirements(ctx)
    ctx.output_root.mkdir(parents=True, exist_ok=True)
    manifest = read_json(ctx.repo / "lake-manifest.json")
    require(isinstance(manifest.get("packages"), list) and manifest["packages"],
            "Setup requires the shipped populated Lake manifest; it never creates or updates one.")
    protected = ("lake-manifest.json", "lakefile.toml", "lean-toolchain",
                 "toolchain.lock.json", "agent_houdini/toolchain/cli-lock.json")
    original = {name: digest(ctx.repo / name) for name in protected}

    def unchanged():
        changed = [name for name in protected
                   if not (ctx.repo / name).is_file() or digest(ctx.repo / name) != original[name]]
        require(not changed, "Setup changed protected source settings: " + ", ".join(changed))

    env = dict(os.environ, LEAN_NUM_THREADS="1", LIMIT_KB="4194304")
    steps = [
        ["bash", "scripts/setup_nosync.sh"],
        ["elan", "toolchain", "install", (ctx.repo / "lean-toolchain").read_text().strip()],
        ["scripts/watchdog.sh", "4194304", "lake", "exe", "cache", "get"],
        [sys.executable, "scripts/build_leancheck_vampire.py", "--jobs", "4", "--json"],
        ["scripts/watchdog.sh", "4194304", sys.executable, "scripts/check_toolchain.py"],
        ["scripts/lake_build_watched.sh"],
        ["scripts/lake_build_watched.sh", "fixed_ambient_encoding_worker", "VampLean",
         "Mathlib.Tactic.Linter.UnusedTactic", "Mathlib.Tactic.Sat.FromLRAT",
         "Whiel.Vampire.ClauseProjection", "Whiel.Vampire.EmptyDomainLRAT",
         "Whiel.Synthesis.FrameworkII.FixedAmbient.CertifyJob", "Whiel.Concrete.Notation",
         "Whiel.Hoare.Concrete", "Benchmark.Inputs"],
        ["cargo", "build", "--release", "--locked", "--manifest-path", "whiel_runner/Cargo.toml", "--bins"],
        ["cargo", "build", "--locked", "--manifest-path", "whiel_runner/direct_lean/Cargo.toml"],
        [sys.executable, "agent_houdini/setup_cli.py", "--json"],
        [sys.executable, "agent_houdini/setup_cli.py", "--verify-only", "--json"],
    ]
    for index, arguments in enumerate(steps, 1):
        try:
            command(ctx, arguments, _log(ctx, f"setup-{index:02}"), env=env, cleanup_group=True)
        finally:
            unchanged()
    try:
        verify_cli(ctx, "0.148.0")
        _install_astra(ctx)
    finally:
        unchanged()
    atomic_json(ctx.output_root / "setup.json", {"schema_version": 1, "state": "complete",
                "versions": {version: ctx.rel(cli_path(ctx, version)) for version in VERSIONS}})


def login(ctx):
    """Create four independent native stores, reusing valid existing logins."""
    _requirements(ctx)
    executable = verify_cli(ctx, "0.148.0")
    sys.path.insert(0, str(ctx.repo))
    from agent_houdini.bwrap import private_file
    from agent_houdini.lean_baseline_utils import worker_homes

    root = ctx.auth_root
    require(not root.is_symlink(), "Worker login root must not be a symlink.")
    root.mkdir(parents=True, mode=0o700, exist_ok=True)
    root.chmod(0o700)
    for slot in range(1, 5):
        home = root / f"worker-{slot}"
        require(not home.is_symlink(), "Worker login directory must not be a symlink.")
        home.mkdir(mode=0o700, exist_ok=True)
        home.chmod(0o700)
        auth = home / "auth.json"
        if auth.exists() or auth.is_symlink():
            private_file(auth.resolve() if not auth.is_symlink() else auth)
            continue
        environment = dict(os.environ, CODEX_HOME=str(home.resolve()))
        command(ctx, [str(executable), "-c", 'cli_auth_credentials_store="file"',
                      "login", "--device-auth"], env=environment, interactive=True)
        require(auth.is_file() and not auth.is_symlink(), "Native login did not create auth.json.")
        auth.chmod(0o600)
        private_file(auth.resolve())
    worker_homes(root.resolve(), 4)
