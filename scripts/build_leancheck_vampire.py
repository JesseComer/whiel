#!/usr/bin/env python3
"""Build the pinned leancheck Vampire from repository-controlled sources.

Reads the ``leancheck_vampire`` role of ``toolchain.lock.json``, fetches the
pinned upstream commit into an ignored checkout under ``toolchain/build/``, applies
the checked-in emitter patch, commits it with a fixed identity so the
resulting commit hash is reproducible, runs the locked configure and compile
commands, and probes the built binary against the pinned identity. The
checkout is disposable; the lock, patch, and fixtures are the pin.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from typing import Mapping, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

from leancheck_toolchain import (  # noqa: E402
    REPO,
    LeancheckPinError,
    applied_commit,
    check_binary,
    check_patch,
    command_output,
    host_platform_key,
    leancheck_role,
    load_lock,
    locked_checkout_path,
    locked_patches,
    repository_path,
    sha256_file,
)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--destination",
        type=Path,
        default=None,
        help="checkout directory (default: the locked path's checkout)",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=os.cpu_count() or 1,
        help="parallel compile jobs",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="remove an existing destination before building",
    )
    parser.add_argument(
        "--bootstrap",
        action="store_true",
        help=(
            "report the applied commit and binary digest without requiring "
            "them to match the lock (used once when first recording a pin)"
        ),
    )
    parser.add_argument("--json", action="store_true", help="emit a JSON receipt")
    return parser


def _git(checkout: Path, *arguments: str, env: dict[str, str] | None = None) -> str:
    return command_output(
        ["git", "-C", str(checkout), *arguments],
        cwd=checkout,
        timeout=1800.0,
        env=env,
    )


def _fetch_commit(checkout: Path, url: str, commit: str, ref: str | None) -> None:
    _git(checkout, "init", "-q")
    _git(checkout, "remote", "add", "origin", url)
    try:
        _git(checkout, "fetch", "-q", "--no-tags", "origin", commit)
    except LeancheckPinError:
        if ref is None:
            raise
        _git(checkout, "fetch", "-q", "--no-tags", "origin", ref)
    _git(checkout, "checkout", "-q", "--detach", commit)
    head = _git(checkout, "rev-parse", "HEAD")
    if head != commit:
        raise LeancheckPinError(f"checked out {head}, expected {commit}")
    _git(checkout, "submodule", "update", "--init", "--recursive", "-q")


def _apply_patch(
    checkout: Path,
    repository: Path,
    patch: Mapping[str, object],
) -> str:
    patch_path = repository_path(repository, str(patch["path"]), label="patch")
    files = patch["files"]
    for relative, digests in files.items():
        actual = sha256_file(checkout / relative)
        if actual != digests["before_sha256"]:
            raise LeancheckPinError(
                f"{relative} differs from the pinned pre-patch source"
            )
    _git(checkout, "apply", "--index", str(patch_path))
    for relative, digests in files.items():
        actual = sha256_file(checkout / relative)
        if actual != digests["after_sha256"]:
            raise LeancheckPinError(
                f"{relative} differs from the pinned patched source"
            )
    applied = patch["commit"]
    _git(checkout, "config", "core.abbrev", str(applied["abbrev"]))
    env = dict(os.environ)
    for role in ("AUTHOR", "COMMITTER"):
        env[f"GIT_{role}_NAME"] = str(applied["author"])
        env[f"GIT_{role}_EMAIL"] = str(applied["email"])
        env[f"GIT_{role}_DATE"] = str(applied["date"])
    _git(
        checkout, "-c", "commit.gpgsign=false", "commit", "-q", "--no-verify",
        "-m", str(applied["message"]), env=env,
    )
    return _git(checkout, "rev-parse", "HEAD")


def _apply_patches(
    checkout: Path,
    repository: Path,
    patches: Sequence[Mapping[str, object]],
    *,
    bootstrap: bool,
) -> list[str]:
    """Apply the pinned series in order, one fixed-identity commit each.

    Each patch's pre-patch digests are checked against the tree the
    previous commit left behind, so a series whose members were recorded
    against a different order or a different base fails closed here rather
    than producing a binary nobody can reproduce.
    """
    applied: list[str] = []
    for patch in patches:
        head = _apply_patch(checkout, repository, patch)
        expected = str(patch["commit"]["sha"])
        if head != expected and not bootstrap:
            raise LeancheckPinError(
                f"applied patch commit {head} differs from pinned {expected}"
            )
        applied.append(head)
    return applied


def build(
    repository: Path,
    *,
    destination: Path | None,
    jobs: int,
    force: bool,
    bootstrap: bool,
) -> dict[str, object]:
    lock = load_lock(repository)
    role = leancheck_role(lock)
    patch_checks = check_patch(repository, role)
    if not all(check.ok for check in patch_checks):
        raise LeancheckPinError(patch_checks[0].detail)
    checkout = (destination or locked_checkout_path(repository, role)).resolve()
    if checkout.exists():
        if not force:
            raise LeancheckPinError(
                f"{checkout} exists; pass --force to rebuild from scratch"
            )
        shutil.rmtree(checkout)
    checkout.parent.mkdir(parents=True, exist_ok=True)
    checkout.mkdir()
    source = role["source"]
    _fetch_commit(
        checkout, str(source["url"]), str(source["commit"]),
        source.get("ref") if isinstance(source.get("ref"), str) else None,
    )
    patches = locked_patches(role)
    commits = _apply_patches(
        checkout, repository, patches, bootstrap=bootstrap
    )
    applied = commits[-1]
    expected_applied = str(applied_commit(role)["sha"])
    build_role = role["build"]
    configure = [
        argument.replace("${CHECKOUT}", str(checkout))
        for argument in build_role["configure"]
    ]
    build_env = dict(os.environ)
    environment = build_role.get("environment", {})
    if not isinstance(environment, dict) or not all(
        isinstance(key, str) and isinstance(value, str)
        for key, value in environment.items()
    ):
        raise LeancheckPinError("build environment must map strings to strings")
    build_env.update(environment)
    command_output(configure, cwd=checkout, timeout=1800.0, env=build_env)
    compile_command = [*build_role["compile"], "--parallel", str(jobs)]
    command_output(compile_command, cwd=checkout, timeout=7200.0, env=build_env)
    binary = checkout / "build" / "vampire"
    platform_key = host_platform_key()
    checks, identity = check_binary(
        repository, role, binary=binary, platform_key=platform_key
    )
    compiler = command_output(["cc", "--version"], cwd=checkout).splitlines()[0]
    receipt: dict[str, object] = {
        "checkout": str(checkout),
        "source_commit": source["commit"],
        "applied_commit": applied,
        "applied_commits": commits,
        "expected_applied_commit": expected_applied,
        "configure": configure,
        "compile": compile_command,
        "environment": dict(environment),
        "compiler": compiler,
        "platform": platform_key,
        "binary": str(binary),
        "sha256": identity.get("sha256"),
        "expected_sha256": identity.get("expected_sha256"),
        "version": identity.get("version"),
        "checks": [check.to_json() for check in patch_checks + checks],
    }
    receipt["ok"] = bootstrap or all(check.ok for check in patch_checks + checks)
    return receipt


def main() -> int:
    arguments = _parser().parse_args()
    try:
        receipt = build(
            REPO,
            destination=arguments.destination,
            jobs=arguments.jobs,
            force=arguments.force,
            bootstrap=arguments.bootstrap,
        )
    except (LeancheckPinError, OSError, subprocess.TimeoutExpired) as error:
        if arguments.json:
            print(json.dumps({"ok": False, "error": str(error)}, indent=2))
        else:
            print(f"error: {error}", file=sys.stderr)
        return 1
    if arguments.json:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        for check in receipt["checks"]:
            status = "ok" if check["ok"] else "FAIL"
            print(f"{status} {check['name']}: {check['detail']}")
        print(f"applied commit: {receipt['applied_commit']}")
        print(f"binary: {receipt['binary']}")
        print(f"sha256: {receipt['sha256']}")
        print(f"compiler: {receipt['compiler']}")
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
