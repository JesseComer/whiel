"""Repository-owned Tier-1 toolchain lock validation."""
from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path, PurePosixPath
import platform
import re
import subprocess
from typing import Mapping, Sequence


LOCK_FILENAME = "toolchain.lock.json"
LOCK_FORMAT_VERSION = 3
HEX_SHA256 = re.compile(r"[0-9a-f]{64}")


class ToolchainLockError(Exception):
    """The repository toolchain lock is missing or inconsistent."""


@dataclass(frozen=True)
class LeancheckVampireSelection:
    path: Path
    required_sha256: str | None
    source: str


@dataclass(frozen=True)
class ToolchainCheck:
    role: str
    ok: bool
    detail: str
    path: str | None = None

    def to_json(self) -> dict[str, object]:
        return asdict(self)


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def host_platform_key() -> str:
    return f"{platform.system()}-{platform.machine()}"


def _load_json(path: Path) -> object:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ToolchainLockError(
            f"cannot read {LOCK_FILENAME}: {error}"
        ) from error


def load_toolchain_lock(repository: Path) -> dict[str, object]:
    value = _load_json(repository.resolve() / LOCK_FILENAME)
    if not isinstance(value, dict):
        raise ToolchainLockError("toolchain lock must be a JSON object")
    found = value.get("format_version")
    if found != LOCK_FORMAT_VERSION:
        raise ToolchainLockError(
            f"unsupported toolchain lock format {found!r}; "
            f"this reader accepts {LOCK_FORMAT_VERSION} only"
        )
    roles = value.get("roles")
    if not isinstance(roles, dict):
        raise ToolchainLockError("toolchain lock has no role map")
    return value


def _role(lock: Mapping[str, object], name: str) -> Mapping[str, object]:
    roles = lock.get("roles")
    value = roles.get(name) if isinstance(roles, dict) else None
    if not isinstance(value, dict):
        raise ToolchainLockError(f"toolchain lock has no {name} role")
    return value


def _relative_locked_path(
    role: Mapping[str, object],
    *,
    label: str,
) -> PurePosixPath:
    raw = role.get("path")
    if not isinstance(raw, str):
        raise ToolchainLockError(f"{label} has no locked relative path")
    relative = PurePosixPath(raw)
    if relative.is_absolute() or ".." in relative.parts or not relative.parts:
        raise ToolchainLockError(f"{label} path is not repository-relative")
    return relative


def _locked_path(
    repository: Path,
    role: Mapping[str, object],
    *,
    label: str,
) -> Path:
    relative = _relative_locked_path(role, label=label)
    return repository.resolve().joinpath(*relative.parts)


def _locked_sha256(
    role: Mapping[str, object],
    *,
    label: str,
    platform_key: str | None = None,
) -> str:
    raw = role.get("sha256")
    if isinstance(raw, str):
        digest = raw
    elif isinstance(raw, dict):
        digest = raw.get(platform_key or host_platform_key())
    else:
        digest = None
    if not isinstance(digest, str) or HEX_SHA256.fullmatch(digest) is None:
        raise ToolchainLockError(
            f"{label} has no SHA-256 for {platform_key or host_platform_key()}"
        )
    return digest


def locked_leancheck_vampire_path(repository: Path) -> Path:
    lock = load_toolchain_lock(repository)
    return _locked_path(
        repository,
        _role(lock, "leancheck_vampire"),
        label="leancheck Vampire",
    )


def locked_leancheck_vampire_sha256(
    repository: Path,
    *,
    platform_key: str | None = None,
) -> str:
    lock = load_toolchain_lock(repository)
    return _locked_sha256(
        _role(lock, "leancheck_vampire"),
        label="leancheck Vampire",
        platform_key=platform_key,
    )


def resolve_leancheck_vampire(
    repository: Path,
    *,
    requested_path: Path | None,
    required_sha256: str | None,
) -> LeancheckVampireSelection:
    if required_sha256 is not None and HEX_SHA256.fullmatch(
        required_sha256
    ) is None:
        raise ToolchainLockError("required Vampire SHA-256 is malformed")
    if requested_path is not None:
        return LeancheckVampireSelection(
            path=requested_path,
            required_sha256=required_sha256,
            source="explicit",
        )
    return LeancheckVampireSelection(
        path=locked_leancheck_vampire_path(repository),
        required_sha256=(
            required_sha256 or locked_leancheck_vampire_sha256(repository)
        ),
        source="toolchain-lock",
    )


def _command_text(
    command: Sequence[str],
    *,
    cwd: Path,
) -> str:
    completed = subprocess.run(
        list(command),
        cwd=cwd,
        text=True,
        capture_output=True,
        timeout=30,
        check=False,
    )
    if completed.returncode != 0:
        raise ToolchainLockError(
            f"{command[0]} exited with status {completed.returncode}"
        )
    return "\n".join(
        value.strip()
        for value in (completed.stdout, completed.stderr)
        if value.strip()
    )


def _check_file_sha(
    *,
    role: str,
    path: Path,
    expected_sha256: str,
) -> ToolchainCheck:
    if not path.is_file() or path.is_symlink():
        return ToolchainCheck(
            role, False, "locked path is not a real file", str(path)
        )
    digest = _sha256(path)
    if digest != expected_sha256:
        return ToolchainCheck(role, False, "SHA-256 mismatch", str(path))
    return ToolchainCheck(role, True, "SHA-256 matches", str(path))


def _version_contains(
    *,
    role: str,
    output: str,
    expected: object,
    path: Path,
) -> ToolchainCheck:
    fragments = expected if isinstance(expected, list) else [expected]
    if not all(isinstance(fragment, str) for fragment in fragments):
        return ToolchainCheck(
            role, False, "lock has invalid version fragments", str(path)
        )
    missing = [fragment for fragment in fragments if fragment not in output]
    if missing:
        return ToolchainCheck(
            role,
            False,
            "version output is missing "
            + ", ".join(repr(item) for item in missing),
            str(path),
        )
    return ToolchainCheck(role, True, "version matches", str(path))


def check_toolchain(repository: Path) -> list[ToolchainCheck]:
    repository = repository.resolve()
    lock = load_toolchain_lock(repository)
    platform_key = host_platform_key()
    results: list[ToolchainCheck] = []

    locked_toolchain = lock.get("lean_toolchain")
    toolchain_path = repository / "lean-toolchain"
    try:
        actual_toolchain = toolchain_path.read_text(encoding="utf-8").strip()
    except OSError as error:
        actual_toolchain = None
        results.append(ToolchainCheck(
            "lean_toolchain", False, f"cannot read lean-toolchain: {error}",
            str(toolchain_path),
        ))
    if actual_toolchain is not None:
        results.append(ToolchainCheck(
            "lean_toolchain",
            actual_toolchain == locked_toolchain,
            (
                "lean-toolchain matches"
                if actual_toolchain == locked_toolchain
                else "lean-toolchain differs from lock"
            ),
            str(toolchain_path),
        ))

    vampire_role = _role(lock, "leancheck_vampire")
    vampire = _locked_path(repository, vampire_role, label="leancheck Vampire")
    results.append(_check_file_sha(
        role="leancheck_vampire",
        path=vampire,
        expected_sha256=_locked_sha256(
            vampire_role, label="leancheck Vampire", platform_key=platform_key
        ),
    ))
    if vampire.is_file():
        try:
            version = _command_text([str(vampire), "--version"], cwd=repository)
            results.append(_version_contains(
                role="leancheck_vampire",
                output=version,
                expected=vampire_role.get("version_contains"),
                path=vampire,
            ))
        except ToolchainLockError as error:
            results.append(ToolchainCheck(
                "leancheck_vampire", False, str(error), str(vampire)
            ))

    patches = vampire_role.get("patches")
    if not isinstance(patches, list) or not patches:
        results.append(ToolchainCheck(
            "leancheck_vampire_patches",
            False,
            "leancheck Vampire role pins no patch series",
            None,
        ))
    else:
        for position, patch in enumerate(patches):
            if not isinstance(patch, dict):
                results.append(ToolchainCheck(
                    f"leancheck_vampire_patch_{position}",
                    False,
                    "patch entry is not an object",
                    None,
                ))
                continue
            patch_path = _locked_path(
                repository, patch, label="leancheck Vampire patch"
            )
            results.append(_check_file_sha(
                role=f"leancheck_vampire_patch_{position}",
                path=patch_path,
                expected_sha256=_locked_sha256(
                    patch, label="leancheck Vampire patch"
                ),
            ))

    vamplean_role = _role(lock, "vamplean_runtime")
    vamplean = _locked_path(repository, vamplean_role, label="VampLean runtime")
    results.append(_check_file_sha(
        role="vamplean_runtime",
        path=vamplean,
        expected_sha256=_locked_sha256(vamplean_role, label="VampLean runtime"),
    ))

    try:
        lean = Path(_command_text(
            ["lake", "env", "which", "lean"], cwd=repository
        )).resolve()
    except ToolchainLockError as error:
        results.append(ToolchainCheck("lean", False, str(error), None))
        return results

    lean_role = _role(lock, "lean")
    results.append(_check_file_sha(
        role="lean",
        path=lean,
        expected_sha256=_locked_sha256(
            lean_role, label="Lean", platform_key=platform_key
        ),
    ))
    try:
        version = _command_text([str(lean), "--version"], cwd=repository)
        results.append(_version_contains(
            role="lean",
            output=version,
            expected=lean_role.get("version_contains"),
            path=lean,
        ))
    except ToolchainLockError as error:
        results.append(ToolchainCheck("lean", False, str(error), str(lean)))

    lake_role = _role(lock, "lake")
    lake = lean.parent / ("lake.exe" if platform.system() == "Windows" else "lake")
    results.append(_check_file_sha(
        role="lake",
        path=lake,
        expected_sha256=_locked_sha256(
            lake_role, label="Lake", platform_key=platform_key
        ),
    ))
    if lake.is_file():
        try:
            version = _command_text([str(lake), "--version"], cwd=repository)
            results.append(ToolchainCheck(
                "lake",
                version == lake_role.get("version"),
                (
                    "version matches"
                    if version == lake_role.get("version")
                    else "version differs from lock"
                ),
                str(lake),
            ))
        except ToolchainLockError as error:
            results.append(ToolchainCheck("lake", False, str(error), str(lake)))

    cadical_role = _role(lock, "kernel_lrat_cadical")
    cadical = lean.parent / (
        "cadical.exe" if platform.system() == "Windows" else "cadical"
    )
    results.append(_check_file_sha(
        role="kernel_lrat_cadical",
        path=cadical,
        expected_sha256=_locked_sha256(
            cadical_role, label="kernel LRAT CaDiCaL",
            platform_key=platform_key,
        ),
    ))
    if cadical.is_file():
        try:
            version = _command_text([str(cadical), "--version"], cwd=repository)
            results.append(ToolchainCheck(
                "kernel_lrat_cadical",
                version == cadical_role.get("version"),
                (
                    "version matches"
                    if version == cadical_role.get("version")
                    else "version differs from lock"
                ),
                str(cadical),
            ))
        except ToolchainLockError as error:
            results.append(ToolchainCheck(
                "kernel_lrat_cadical", False, str(error), str(cadical)
            ))
    return results


def validate_toolchain(repository: Path) -> None:
    results = check_toolchain(repository)
    failures = [result for result in results if not result.ok]
    if failures:
        detail = "; ".join(
            f"{failure.role}: {failure.detail}" for failure in failures
        )
        raise ToolchainLockError(detail)
