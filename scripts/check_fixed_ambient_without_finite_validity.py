#!/usr/bin/env python3
"""Build the V5 Lean product path without finite validity."""

from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import tempfile

from check_f2_without_finite_validity import (
    DeletionGateError,
    _assert_initial_copy_is_clean,
    _build_environment,
    _check_deletion_contract_sources,
    _check_tool_resolution,
    _copy_clean_source,
    _run,
)


LEAN_TARGETS = (
    "Whiel",
    "Whiel.Synthesis.Tests.FixedAmbientAll",
    "fixed_ambient_encoding_worker",
)


def main() -> int:
    try:
        _check_deletion_contract_sources()
        _check_tool_resolution()
        with tempfile.TemporaryDirectory(
            prefix="whiel-v5-without-fv-"
        ) as temporary:
            copy_root = Path(temporary) / "source"
            copy_root.mkdir()
            _copy_clean_source(copy_root)
            _assert_initial_copy_is_clean(copy_root)
            print(
                "fixed-ambient deletion gate: clean source "
                "contains no retained finite-validity research",
                flush=True,
            )
            environment = _build_environment(copy_root)
            _run(
                ("lake", "build", *LEAN_TARGETS),
                copy_root,
                environment,
            )
    except (
        DeletionGateError,
        OSError,
        subprocess.CalledProcessError,
    ) as error:
        print(
            f"fixed-ambient deletion gate failed: {error}",
            file=sys.stderr,
        )
        return 1

    print("fixed-ambient deletion gate passed", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
