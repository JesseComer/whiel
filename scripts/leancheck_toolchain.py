#!/usr/bin/env python3
"""Identity of the repository-pinned leancheck Vampire.

The pin lives in ``toolchain.lock.json`` under the ``leancheck_vampire``
role: an upstream source commit, the checked-in emitter patch, the
deterministic commit the patch produces, the build command, and the
resolved binary digest per supported platform. This module reads and
verifies that identity without importing ``whiel_synth``.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path, PurePosixPath
import platform
import re
import subprocess
from typing import Mapping, Sequence


REPO = Path(__file__).resolve().parent.parent
LOCK_FILENAME = "toolchain.lock.json"
LOCK_FORMAT_VERSION = 3
ROLE = "leancheck_vampire"
HEX_SHA256 = re.compile(r"[0-9a-f]{64}")
HEX_SHA1 = re.compile(r"[0-9a-f]{40}")
VERSION_COMMIT = re.compile(r"\bcommit\s+([0-9a-f]{7,40})\b")


class LeancheckPinError(Exception):
    """The leancheck pin is missing, malformed, or not satisfied."""


@dataclass(frozen=True)
class Check:
    name: str
    ok: bool
    detail: str

    def to_json(self) -> dict[str, object]:
        return asdict(self)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def host_platform_key() -> str:
    return f"{platform.system()}-{platform.machine()}"


def load_lock(repository: Path = REPO) -> dict[str, object]:
    path = repository.resolve() / LOCK_FILENAME
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise LeancheckPinError(f"cannot read {LOCK_FILENAME}: {error}") from error
    if not isinstance(value, dict):
        raise LeancheckPinError("toolchain lock must be a JSON object")
    found = value.get("format_version")
    if found != LOCK_FORMAT_VERSION:
        raise LeancheckPinError(
            f"unsupported toolchain lock format {found!r}; "
            f"this reader accepts {LOCK_FORMAT_VERSION} only"
        )
    if not isinstance(value.get("roles"), dict):
        raise LeancheckPinError("toolchain lock has no role map")
    return value


def _require(mapping: Mapping[str, object], key: str, label: str) -> object:
    if key not in mapping:
        raise LeancheckPinError(f"{label} has no {key}")
    return mapping[key]


def _require_str(mapping: Mapping[str, object], key: str, label: str) -> str:
    value = _require(mapping, key, label)
    if not isinstance(value, str) or not value:
        raise LeancheckPinError(f"{label} {key} must be a nonempty string")
    return value


def _require_map(
    mapping: Mapping[str, object], key: str, label: str
) -> Mapping[str, object]:
    value = _require(mapping, key, label)
    if not isinstance(value, dict):
        raise LeancheckPinError(f"{label} {key} must be an object")
    return value


def _require_list(
    mapping: Mapping[str, object], key: str, label: str
) -> list[str]:
    value = _require(mapping, key, label)
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item for item in value
    ):
        raise LeancheckPinError(f"{label} {key} must be a list of strings")
    return list(value)


def leancheck_role(lock: Mapping[str, object]) -> Mapping[str, object]:
    roles = lock["roles"]
    role = roles.get(ROLE) if isinstance(roles, dict) else None
    if not isinstance(role, dict):
        raise LeancheckPinError(f"toolchain lock has no {ROLE} role")
    label = ROLE
    _require_str(role, "path", label)
    source = _require_map(role, "source", label)
    _require_str(source, "url", f"{label} source")
    commit = _require_str(source, "commit", f"{label} source")
    if HEX_SHA1.fullmatch(commit) is None:
        raise LeancheckPinError(f"{label} source commit is not a SHA-1")
    patches = _require(role, "patches", label)
    if not isinstance(patches, list) or not patches:
        raise LeancheckPinError(f"{label} patches must be a nonempty list")
    # The tree the series builds up, file by file: a patch that touches a
    # file an earlier patch touched must state that file's post-patch digest
    # as its own pre-patch digest. A series recorded against a different
    # order, or against a base one of its own members does not produce, is
    # refused here rather than part-way through a build.
    tree: dict[str, str] = {}
    for position, patch in enumerate(patches):
        if not isinstance(patch, dict):
            raise LeancheckPinError(f"{label} patch {position} is not an object")
        where = f"{label} patch {position}"
        _require_str(patch, "path", where)
        digest = _require_str(patch, "sha256", where)
        if HEX_SHA256.fullmatch(digest) is None:
            raise LeancheckPinError(f"{where} sha256 is malformed")
        files = _require_map(patch, "files", where)
        if not files:
            raise LeancheckPinError(f"{where} touches no file")
        for name, value in files.items():
            if not isinstance(value, dict):
                raise LeancheckPinError(f"{where} file {name} is malformed")
            for key in ("before_sha256", "after_sha256"):
                item = value.get(key)
                if not isinstance(item, str) or HEX_SHA256.fullmatch(item) is None:
                    raise LeancheckPinError(
                        f"{where} file {name} has no valid {key}"
                    )
        applied = _require_map(patch, "commit", where)
        for key in ("message", "author", "email", "date"):
            _require_str(applied, key, f"{where} commit")
        sha = _require_str(applied, "sha", f"{where} commit")
        if HEX_SHA1.fullmatch(sha) is None:
            raise LeancheckPinError(f"{where} commit sha is not a SHA-1")
        abbrev = applied.get("abbrev")
        if not isinstance(abbrev, int) or not 7 <= abbrev <= 40:
            raise LeancheckPinError(f"{where} commit abbrev is invalid")
        for name, value in files.items():
            expected = tree.get(name)
            if expected is not None and expected != value["before_sha256"]:
                raise LeancheckPinError(
                    f"{where} expects {name} at a digest the series does not "
                    "leave behind"
                )
            tree[name] = value["after_sha256"]
    build = _require_map(role, "build", label)
    _require_list(build, "configure", f"{label} build")
    _require_list(build, "compile", f"{label} build")
    _require_list(role, "version_contains", label)
    digests = _require_map(role, "sha256", label)
    for key, value in digests.items():
        if not isinstance(value, str) or HEX_SHA256.fullmatch(value) is None:
            raise LeancheckPinError(f"{label} sha256 for {key} is malformed")
    return role


def repository_path(repository: Path, relative: str, *, label: str) -> Path:
    parts = PurePosixPath(relative)
    if parts.is_absolute() or ".." in parts.parts or not parts.parts:
        raise LeancheckPinError(f"{label} path is not repository-relative")
    return repository.resolve().joinpath(*parts.parts)


def locked_binary_path(repository: Path, role: Mapping[str, object]) -> Path:
    return repository_path(repository, str(role["path"]), label=ROLE)


def locked_checkout_path(repository: Path, role: Mapping[str, object]) -> Path:
    """The source checkout that owns the locked ``build/vampire`` binary."""
    relative = PurePosixPath(str(role["path"]))
    if relative.parts[-2:] != ("build", "vampire"):
        raise LeancheckPinError(f"{ROLE} path must end in build/vampire")
    return repository_path(
        repository, str(PurePosixPath(*relative.parts[:-2])), label=ROLE
    )


def command_output(
    command: Sequence[str],
    *,
    cwd: Path,
    timeout: float = 60.0,
    env: Mapping[str, str] | None = None,
) -> str:
    completed = subprocess.run(
        list(command),
        cwd=cwd,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
        env=dict(env) if env is not None else None,
    )
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout).strip()
        raise LeancheckPinError(
            f"{command[0]} exited with status {completed.returncode}"
            + (f": {detail[-2000:]}" if detail else "")
        )
    return "\n".join(
        value.strip()
        for value in (completed.stdout, completed.stderr)
        if value.strip()
    )


def locked_patches(role: Mapping[str, object]) -> list[Mapping[str, object]]:
    """The patch series, in the order the build script applies it."""
    return [dict(patch) for patch in role["patches"]]


def applied_commit(role: Mapping[str, object]) -> Mapping[str, object]:
    """The commit the last patch of the series produces: the built HEAD."""
    return dict(locked_patches(role)[-1]["commit"])


def check_patch(repository: Path, role: Mapping[str, object]) -> list[Check]:
    checks: list[Check] = []
    for position, patch in enumerate(locked_patches(role)):
        name = f"patch_file_{position}"
        path = repository_path(repository, str(patch["path"]), label="patch")
        if not path.is_file() or path.is_symlink():
            checks.append(Check(name, False, f"missing patch file {path}"))
            continue
        digest = sha256_file(path)
        checks.append(Check(
            name,
            digest == patch["sha256"],
            f"{path.name} SHA-256 "
            + ("matches" if digest == patch["sha256"] else "mismatch"),
        ))
    return checks


def check_binary(
    repository: Path,
    role: Mapping[str, object],
    *,
    binary: Path | None = None,
    platform_key: str | None = None,
) -> tuple[list[Check], dict[str, object]]:
    """Verify one binary against the pinned identity, failing closed."""
    platform_key = platform_key or host_platform_key()
    path = binary if binary is not None else locked_binary_path(repository, role)
    identity: dict[str, object] = {
        "platform": platform_key,
        "binary": str(path),
        "source_commit": role["source"]["commit"],
        "patch_sha256": [
            patch["sha256"] for patch in locked_patches(role)
        ],
        "applied_commit": applied_commit(role)["sha"],
    }
    checks: list[Check] = []
    expected = role["sha256"].get(platform_key)
    identity["expected_sha256"] = expected
    if expected is None:
        checks.append(Check(
            "platform", False, f"no pinned binary for platform {platform_key}"
        ))
    if not path.is_file() or path.is_symlink():
        checks.append(Check("binary_file", False, "locked path is not a real file"))
        return checks, identity
    digest = sha256_file(path)
    identity["sha256"] = digest
    if expected is not None:
        checks.append(Check(
            "binary_sha256",
            digest == expected,
            "SHA-256 matches" if digest == expected else "SHA-256 mismatch",
        ))
    try:
        version = command_output([str(path), "--version"], cwd=repository)
    except (LeancheckPinError, OSError, subprocess.TimeoutExpired) as error:
        checks.append(Check("version", False, str(error)))
        return checks, identity
    identity["version"] = version
    missing = [
        fragment for fragment in role["version_contains"]
        if fragment not in version
    ]
    checks.append(Check(
        "version_fragments",
        not missing,
        "version matches" if not missing
        else "version output is missing " + ", ".join(map(repr, missing)),
    ))
    match = VERSION_COMMIT.search(version)
    applied = str(applied_commit(role)["sha"])
    if match is None:
        checks.append(Check("version_commit", False, "version names no commit"))
    else:
        token = match.group(1)
        ok = applied.startswith(token)
        checks.append(Check(
            "version_commit",
            ok,
            "version commit is the applied patch commit" if ok
            else f"version commit {token} is not the applied patch commit",
        ))
    return checks, identity


def probe(
    repository: Path = REPO,
    *,
    binary: Path | None = None,
    platform_key: str | None = None,
) -> dict[str, object]:
    """Machine-readable identity probe of the pinned leancheck Vampire."""
    lock = load_lock(repository)
    role = leancheck_role(lock)
    checks = check_patch(repository, role)
    binary_checks, identity = check_binary(
        repository, role, binary=binary, platform_key=platform_key
    )
    checks.extend(binary_checks)
    identity["checks"] = [check.to_json() for check in checks]
    identity["ok"] = all(check.ok for check in checks)
    return identity
