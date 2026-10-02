#!/usr/bin/env python3
"""Fail closed if the V5 Lean product path regains V4 bridges."""

import hashlib
import re
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]

ACTIVE_FILES = (
    ROOT / "Whiel.lean",
    ROOT / "Benchmark/Example0001/Input.lean",
    ROOT / "Whiel/Synthesis/Runtime/FixedAmbientRegistry.lean",
    ROOT / "Whiel/Synthesis/Tests/FixedAmbientAll.lean",
    ROOT / "Whiel/Synthesis/Runtime/FixedAmbientWorker.lean",
    ROOT / "Whiel/Synthesis/Tests/FixedAmbientWorker.lean",
)

FIXED_AMBIENT_DIR = (
    ROOT / "Whiel/Synthesis/FrameworkII/FixedAmbient"
)

FORBIDDEN = (
    "FrameworkII.ProgramImage",
    "FrameworkII.Scope",
    "FrameworkII.SourceCollapse",
    "ProgramProphecyTaskSchema",
    "programImage",
    "onProgramImage",
    "sourceCollapse",
    "Instance.reduct",
    "RelationNameSupply WhielNames",
    "FiniteValidity",
)

REGISTRY_FORBIDDEN = (
    "BenchmarkEncoding",
    "BenchmarkEncodingWorker",
    "EncodingWorker",
    "Tests.All",
)

# The registry binds exactly the production input identity.
REGISTRY_REQUIRED_IDENTITY = (
    '"Example0001"',
    '"Benchmark.Example0001.Input"',
    '"Whiel.Benchmark.Example0001"',
)

# The retired bootstrap fixture must not resurface on the product path.
STALE_IDENTITY_TOKENS = (
    "FixedAmbient0001",
)

# Superseded V4 Lean modules deleted in Pass 7.3d; their return fails closed.
RETIRED_LEAN_FILES = (
    "Whiel/Hoare/BaseNameOnly.lean",
    "Whiel/Synthesis/FrameworkII/FixedAmbient/BaseNameSymbols.lean",
    "Whiel/RelationNames/ProgramProphecy.lean",
    "Whiel/RelationNames/ProgramProphecySchema.lean",
    "Whiel/Synthesis/FrameworkII/Admission.lean",
    "Whiel/Synthesis/FrameworkII/Assembly.lean",
    "Whiel/Synthesis/FrameworkII/Components.lean",
    "Whiel/Synthesis/FrameworkII/IdentityDecoder.lean",
    "Whiel/Synthesis/FrameworkII/Obligations.lean",
    "Whiel/Synthesis/FrameworkII/Precondition.lean",
    "Whiel/Synthesis/FrameworkII/ProgramImage.lean",
    "Whiel/Synthesis/FrameworkII/Scope.lean",
    "Whiel/Synthesis/FrameworkII/Semantics.lean",
    "Whiel/Synthesis/FrameworkII/SourceCollapse.lean",
    "Whiel/Synthesis/FrameworkII/SurfaceParser/ProgramProphecy.lean",
    "Whiel/Synthesis/FrameworkII/WorkerService.lean",
)

LEGACY_RUNTIME_FILES = (
    ROOT / "Whiel/Synthesis/Runtime/EncodingWorker.lean",
    ROOT / "Whiel/Synthesis/Runtime/BenchmarkEncoding.lean",
    ROOT / "Whiel/Synthesis/Runtime/Task.lean",
    ROOT / "Whiel/Synthesis/Tests/All.lean",
    ROOT / "Whiel/Synthesis/Tests/AxiomAudit.lean",
)

LEGACY_FORBIDDEN = (
    "ProgramProphecyName",
    "FrameworkII.WorkerService",
    "FrameworkII.AdmissionService",
    "framework_ii_",
)

RUST_SOURCE_DIRS = (
    ROOT / "whiel_runner/src",
    ROOT / "whiel_runner/tests",
)

# Rust may carry these strings only inside the explicit fail-closed
# deny list that proves retired V4 wire operations are rejected.
RUST_DENY_LIST_FILE = ROOT / "whiel_runner/src/encoding/protocol.rs"

RUST_FORBIDDEN = (
    "ProgramProphecyTaskSchema",
    "program_image",
    "programImage",
    "reduct",
    "AdmittedSourceInstance",
    "admit_source_instance",
    "prophecy_context",
    "collapse_framework_ii_core",
    "FRAMEWORK_II_WORKER_VERSION",
    "whiel_framework_ii_task_scope",
    "mentions_prophecy()",
)


def fail(message: str) -> None:
    print(message, file=sys.stderr)
    raise SystemExit(1)


def registry_closure() -> list[Path]:
    """Follow declared registry support/generated imports, fail on cycles/links."""
    prefix = "Whiel.Synthesis.Runtime.FixedAmbientRegistry"
    result = []
    visited = set()
    active = set()

    def visit(module: str) -> None:
        if module in active:
            fail(f"registry import cycle: {module}")
        if module in visited:
            return
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if any(p.is_symlink() for p in (path, *path.parents)) or not path.is_file():
            fail(f"missing or linked registry module: {module}")
        active.add(module)
        source = path.read_text(encoding="utf-8")
        for imported in re.findall(r"^import ([A-Za-z0-9_.]+)$", source, re.MULTILINE):
            if imported == prefix or imported.startswith(prefix + "."):
                visit(imported)
            elif imported.startswith("Benchmark."):
                if not re.fullmatch(r"Benchmark\.[A-Za-z][A-Za-z0-9_]*\.Input", imported):
                    fail(f"registry imports non-input Benchmark module: {imported}")
        active.remove(module)
        visited.add(module)
        result.append(path)

    visit(prefix)
    return result


def main() -> None:
    closure = registry_closure()
    files = list(ACTIVE_FILES) + closure
    files.extend(sorted(FIXED_AMBIENT_DIR.glob("*.lean")))
    for path in files:
        if not path.is_file():
            fail(f"missing active V5 file: {path.relative_to(ROOT)}")
        source = path.read_text(encoding="utf-8")
        for token in FORBIDDEN:
            if token in source:
                fail(
                    f"{path.relative_to(ROOT)} contains "
                    f"forbidden V4 token {token!r}"
                )

    for path in (*ACTIVE_FILES, *closure):
        source = path.read_text(encoding="utf-8")
        for token in STALE_IDENTITY_TOKENS:
            if token in source:
                fail(
                    f"{path.relative_to(ROOT)} still names the retired "
                    f"fixture identity {token!r}"
                )

    registry = "\n".join(path.read_text(encoding="utf-8") for path in closure)
    for token in REGISTRY_FORBIDDEN:
        if token in registry:
            fail(
                "fixed-ambient registry reaches legacy aggregate "
                f"token {token!r}"
            )
    for token in REGISTRY_REQUIRED_IDENTITY:
        if token not in registry:
            fail(
                "fixed-ambient registry does not bind the production "
                f"input identity {token}"
            )

    fixture_digest = hashlib.sha256(
        ACTIVE_FILES[1].read_bytes()
    ).hexdigest()
    if (
        fixture_digest[:32] not in registry
        or fixture_digest[32:] not in registry
    ):
        fail("fixed-ambient registry input digest is stale")

    root_source = ACTIVE_FILES[0].read_text(encoding="utf-8")
    required_imports = (
        "Whiel.Synthesis.FrameworkII.FixedAmbient.Worker",
        "Whiel.Synthesis.Runtime.FixedAmbientRegistry",
        "Whiel.Synthesis.Runtime.FixedAmbientWorker",
    )
    for module in required_imports:
        if f"import {module}" not in root_source:
            fail(f"Whiel.lean does not import {module}")

    # The registry consumes only the supply-free preprocessing path:
    # the preprocessed loop and the checked `Hoare.preprocess` result.
    for marker in ("Preproc.loop", "Hoare.preprocess"):
        if marker not in registry:
            fail(
                "fixed-ambient registry does not consume the "
                f"supply-free input marker {marker!r}"
            )

    for marker in ("productTask", "rawBaseNameOnly", "BaseNameOnly"):
        if marker in registry:
            fail(
                "fixed-ambient registry regained the retired "
                f"per-input raw check marker {marker!r}"
            )

    present = [path for path in RETIRED_LEAN_FILES if (ROOT / path).exists()]
    if present:
        fail("retired V4 Lean module present: " + ", ".join(present))
    for path in LEGACY_RUNTIME_FILES:
        source = path.read_text(encoding="utf-8")
        for token in LEGACY_FORBIDDEN:
            if token in source:
                fail(
                    f"{path.relative_to(ROOT)} still carries the retired "
                    f"V4 service token {token!r}"
                )

    for directory in RUST_SOURCE_DIRS:
        for path in sorted(directory.rglob("*.rs")):
            source = path.read_text(encoding="utf-8")
            for token in RUST_FORBIDDEN:
                if token in source and path != RUST_DENY_LIST_FILE:
                    fail(
                        f"{path.relative_to(ROOT)} contains "
                        f"retired V4 Rust token {token!r}"
                    )

    print("fixed-ambient Lean and Rust product-path audit passed")


if __name__ == "__main__":
    main()
