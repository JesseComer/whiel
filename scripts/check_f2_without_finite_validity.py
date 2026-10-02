#!/usr/bin/env python3
"""Build the normal F2 surface without the opt-in finite-validity research slice."""

from __future__ import annotations

import os
from pathlib import Path, PurePosixPath
import shlex
import shutil
import subprocess
import sys
import tempfile


REPOSITORY = Path(__file__).resolve().parents[1]

OMITTED_FILES = frozenset(
    {
        PurePosixPath("Whiel/Library/FiniteOrder.lean"),
        PurePosixPath("Whiel/Library/Tests/FiniteOrder.lean"),
        PurePosixPath("Whiel/Synthesis/Tests/FiniteValidityResearch.lean"),
        PurePosixPath("Whiel/Synthesis/Tests/FrameworkIIFiniteValidity.lean"),
        PurePosixPath(
            "Whiel/Synthesis/Tests/FrameworkIIFiniteValidityAxiomAudit.lean"
        ),
    }
)
OMITTED_DIRECTORY = PurePosixPath(
    "Whiel/Synthesis/FrameworkII/FiniteValidity"
)
RETIRED_FILES = (
    REPOSITORY
    / "Whiel/Synthesis/Tests/FrameworkIIFiniteValidityWorkerSmoke.lean",
)

FORBIDDEN_COPY_ROOTS = (
    PurePosixPath(".git"),
    PurePosixPath(".lake"),
    PurePosixPath(".venv"),
    PurePosixPath("artifacts"),
    PurePosixPath("results_summary"),
    PurePosixPath("whiel_runner/target"),
)
FORBIDDEN_COPY_SUFFIXES = frozenset(
    {
        ".ilean",
        ".olean",
        ".o",
        ".pyc",
        ".rmeta",
        ".rlib",
    }
)

LEAN_TARGETS = (
    "Whiel.Synthesis.Tests.All",
    "Whiel.Synthesis.Tests.AxiomAudit",
    "Whiel.Synthesis.Tests.FrameworkIIRefutation",
    "example0012_encoding_worker",
    "benchmark_encoding_worker",
    "fixed_ambient_encoding_worker",
)


class DeletionGateError(RuntimeError):
    """The source copy or deletion contract is incomplete."""


def _is_within(path: PurePosixPath, root: PurePosixPath) -> bool:
    return path == root or root in path.parents


def _is_omitted(path: PurePosixPath) -> bool:
    return path in OMITTED_FILES or _is_within(path, OMITTED_DIRECTORY)


def _is_forbidden_build_path(path: PurePosixPath) -> bool:
    if any(_is_within(path, root) for root in FORBIDDEN_COPY_ROOTS):
        return True
    if any(part.endswith(".nosync") for part in path.parts):
        return True
    return path.suffix in FORBIDDEN_COPY_SUFFIXES


def _listed_source_paths() -> tuple[PurePosixPath, ...]:
    completed = subprocess.run(
        [
            "git",
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
        ],
        cwd=REPOSITORY,
        check=True,
        capture_output=True,
    )
    decoded = completed.stdout.decode("utf-8").split("\0")
    return tuple(PurePosixPath(path) for path in decoded if path)


def _check_deletion_contract_sources() -> None:
    missing = [
        str(path)
        for path in sorted(OMITTED_FILES)
        if not (REPOSITORY / path).is_file()
    ]
    if not (REPOSITORY / OMITTED_DIRECTORY).is_dir():
        missing.append(str(OMITTED_DIRECTORY))
    if missing:
        raise DeletionGateError(
            "retained finite-validity research source is missing: "
            + ", ".join(missing)
        )
    present_retired = [
        str(path.relative_to(REPOSITORY)) for path in RETIRED_FILES if path.exists()
    ]
    if present_retired:
        raise DeletionGateError(
            "retired finite-validity worker smoke source still exists: "
            + ", ".join(present_retired)
        )


def _copy_clean_source(destination: Path) -> None:
    omitted = set()
    for relative in _listed_source_paths():
        if _is_omitted(relative):
            omitted.add(relative)
            continue
        if _is_forbidden_build_path(relative):
            raise DeletionGateError(
                f"Git source listing contains build output {relative}"
            )

        source = REPOSITORY / relative
        if not source.exists():
            # A tracked deletion in the current worktree is intentionally absent.
            continue
        if source.is_symlink():
            raise DeletionGateError(
                f"source symlink would break copy isolation: {relative}"
            )
        if not source.is_file():
            raise DeletionGateError(f"unexpected source entry: {relative}")

        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)

    unseen_files = sorted(OMITTED_FILES.difference(omitted))
    omitted_modules = [
        path for path in omitted if _is_within(path, OMITTED_DIRECTORY)
    ]
    if unseen_files or not omitted_modules:
        detail = ", ".join(str(path) for path in unseen_files)
        if not omitted_modules:
            detail = f"{detail}, {OMITTED_DIRECTORY}".strip(", ")
        raise DeletionGateError(
            "source listing did not exercise every deletion root: " + detail
        )


def _assert_initial_copy_is_clean(copy_root: Path) -> None:
    present_roots = [
        str(root) for root in FORBIDDEN_COPY_ROOTS if (copy_root / root).exists()
    ]
    if present_roots:
        raise DeletionGateError(
            "clean source copy contains generated roots: " + ", ".join(present_roots)
        )

    leaked_research = [
        str(path)
        for path in sorted(OMITTED_FILES)
        if (copy_root / path).exists()
    ]
    if (copy_root / OMITTED_DIRECTORY).exists():
        leaked_research.append(str(OMITTED_DIRECTORY))
    if leaked_research:
        raise DeletionGateError(
            "clean source copy contains omitted research source: "
            + ", ".join(leaked_research)
        )

    generated_files = [
        path.relative_to(copy_root)
        for path in copy_root.rglob("*")
        if path.is_file() and path.suffix in FORBIDDEN_COPY_SUFFIXES
    ]
    if generated_files:
        raise DeletionGateError(
            "clean source copy contains generated files: "
            + ", ".join(str(path) for path in generated_files[:10])
        )


def _build_environment(copy_root: Path) -> dict[str, str]:
    environment = os.environ.copy()
    for name in ("CARGO_TARGET_DIR", "LAKE_HOME", "LEAN_PATH", "LEAN_SRC_PATH"):
        environment.pop(name, None)
    environment["CARGO_TARGET_DIR"] = str(copy_root / "whiel_runner/target")
    return environment


def _check_tool_resolution() -> None:
    for name in ("cargo", "git", "lake"):
        executable = shutil.which(name)
        if executable is None:
            raise DeletionGateError(f"required executable is unavailable: {name}")
        resolved = Path(executable).resolve()
        if resolved == REPOSITORY or REPOSITORY in resolved.parents:
            raise DeletionGateError(
                f"{name} resolves inside the source worktree: {resolved}"
            )


def _run(command: tuple[str, ...], copy_root: Path, environment: dict[str, str]) -> None:
    rendered = shlex.join(command)
    print(f"deletion gate: {rendered}", flush=True)
    subprocess.run(command, cwd=copy_root, env=environment, check=True)


def main() -> int:
    try:
        _check_deletion_contract_sources()
        _check_tool_resolution()
        with tempfile.TemporaryDirectory(prefix="whiel-f2-without-fv-") as temporary:
            copy_root = Path(temporary) / "source"
            copy_root.mkdir()
            _copy_clean_source(copy_root)
            _assert_initial_copy_is_clean(copy_root)
            print(
                "deletion gate: clean source copy contains no .lake, target, "
                "artifacts, olean files, or retained finite-validity research slice",
                flush=True,
            )

            environment = _build_environment(copy_root)
            # Lake now resolves dependencies normally into the clean copy's new
            # .lake tree. No worktree package or build tree is on LEAN_PATH.
            _run(("lake", "build"), copy_root, environment)
            _run(("lake", "build", *LEAN_TARGETS), copy_root, environment)
            _run(
                (
                    "cargo",
                    "test",
                    "--manifest-path",
                    "whiel_runner/Cargo.toml",
                    "--lib",
                    "framework2::",
                ),
                copy_root,
                environment,
            )
            _run(
                (
                    "cargo",
                    "test",
                    "--manifest-path",
                    "whiel_runner/Cargo.toml",
                    "--test",
                    "framework2_fixed_ambient",
                    "--",
                    "--test-threads=1",
                ),
                copy_root,
                environment,
            )
    except (DeletionGateError, OSError, subprocess.CalledProcessError) as error:
        print(f"deletion gate failed: {error}", file=sys.stderr)
        return 1

    print("deletion gate passed", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
