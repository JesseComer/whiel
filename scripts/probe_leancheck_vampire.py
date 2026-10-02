#!/usr/bin/env python3
"""Machine-readable identity probe of the pinned leancheck Vampire.

Reports the platform, resolved binary path, binary SHA-256, version
output, pinned source commit, patch digest, and applied patch commit, with
every identity check. Exits nonzero unless every check passes.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

from leancheck_toolchain import (  # noqa: E402
    REPO,
    LeancheckPinError,
    probe,
)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--binary",
        type=Path,
        default=None,
        help="probe this binary instead of the locked path",
    )
    parser.add_argument(
        "--platform-key",
        default=None,
        help="check against this platform's pinned digest (default: host)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit the identity as JSON",
    )
    return parser


def main() -> int:
    arguments = _parser().parse_args()
    try:
        identity = probe(
            REPO,
            binary=arguments.binary,
            platform_key=arguments.platform_key,
        )
    except LeancheckPinError as error:
        if arguments.json:
            print(json.dumps({"ok": False, "error": str(error)}, indent=2))
        else:
            print(f"error: {error}", file=sys.stderr)
        return 1
    if arguments.json:
        print(json.dumps(identity, indent=2, sort_keys=True))
    else:
        for check in identity["checks"]:
            status = "ok" if check["ok"] else "FAIL"
            print(f"{status} {check['name']}: {check['detail']}")
        print(f"binary: {identity['binary']}")
        print(f"sha256: {identity.get('sha256')}")
        print(f"version: {identity.get('version', '').replace(chr(10), ' | ')}")
    return 0 if identity["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
