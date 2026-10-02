#!/usr/bin/env python3
"""Check the repository-pinned Tier-1 toolchain."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys


REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))

from toolchain_lock import (  # noqa: E402
    ToolchainLockError,
    check_toolchain,
)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit machine-readable check results",
    )
    return parser


def main() -> int:
    arguments = _parser().parse_args()
    try:
        results = check_toolchain(REPO)
    except ToolchainLockError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    if arguments.json:
        print(json.dumps([result.to_json() for result in results], indent=2))
    else:
        for result in results:
            status = "ok" if result.ok else "FAIL"
            suffix = f" ({result.path})" if result.path else ""
            print(f"{status} {result.role}: {result.detail}{suffix}")
    return 0 if all(result.ok for result in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
