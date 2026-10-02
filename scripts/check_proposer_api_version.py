#!/usr/bin/env python3
"""Require an API version and documentation update for API-directory changes.

Compare an explicit Git commit with the current working tree, including
untracked (also ignored) API files. Renames are treated as deletion/addition so
moving a file out of the API directory cannot bypass the gate. This is a
mechanical source convention, not a semantic compatibility assessment.
"""

import argparse
from pathlib import Path
import re
import subprocess
import sys


API_DIRECTORY = "whiel_runner/src/proposer_api"
VERSION_FILE = f"{API_DIRECTORY}/version.rs"
DOCUMENTATION = "docs/proposer-api.md"
SEMVER = r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)"
VERSION_DECLARATION = re.compile(
    r'\bpub\s+const\s+API_VERSION\s*:\s*&\s*str\s*=\s*"([^"\\]*)"\s*;'
)


class VersionGateError(ValueError):
    pass


def git(root: Path, *arguments: str) -> bytes:
    result = subprocess.run(
        ["git", "-C", str(root), *arguments],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode:
        raise VersionGateError(result.stderr.decode("utf-8", errors="replace").strip())
    return result.stdout


def strip_rust_comments(source: str) -> str:
    """Ignore comments, including nested block comments, around declarations."""
    output = []
    position = 0
    while position < len(source):
        if source.startswith("//", position):
            end = source.find("\n", position)
            position = len(source) if end < 0 else end
        elif source.startswith("/*", position):
            depth = 1
            position += 2
            while position < len(source) and depth:
                if source.startswith("/*", position):
                    depth += 1
                    position += 2
                elif source.startswith("*/", position):
                    depth -= 1
                    position += 2
                else:
                    position += 1
            if depth:
                raise VersionGateError("unterminated comment in API version file")
            output.append(" ")
        elif source[position] == '"':
            start = position
            position += 1
            while position < len(source) and source[position] != '"':
                position += 2 if source[position] == "\\" else 1
            position += 1
            output.append(source[start:position])
        else:
            output.append(source[position])
            position += 1
    return "".join(output)


def parse_version(source: str, label: str) -> tuple[int, int, int]:
    declarations = VERSION_DECLARATION.findall(strip_rust_comments(source))
    if len(declarations) != 1 or re.fullmatch(SEMVER, declarations[0]) is None:
        raise VersionGateError(
            f'{label} must declare exactly one pub const API_VERSION: &str = "X.Y.Z"; '
            "using a canonical three-component release version"
        )
    return tuple(map(int, declarations[0].split(".")))


def version_entry(document: str, version: str) -> str | None:
    """Read the version's level-three Markdown section, excluding code fences."""
    lines = document.splitlines()
    headings = []
    fence = None
    for index, line in enumerate(lines):
        marker = re.match(r"^ {0,3}(`{3,}|~{3,})", line)
        if marker:
            run = marker[1]
            if fence is None:
                fence = run
            elif run[0] == fence[0] and len(run) >= len(fence):
                fence = None
            continue
        if fence is None:
            heading = re.match(r"^(#{1,6})\s+(.+?)\s*$", line)
            if heading:
                headings.append((index, len(heading[1]), heading[2]))
    matches = [
        index for index, level, title in headings
        if level == 3 and re.match(rf"^{re.escape(version)}(?:\s|$)", title)
    ]
    if len(matches) > 1:
        raise VersionGateError(f"duplicate documentation entries for API {version}")
    if not matches:
        return None
    start = matches[0]
    end = next((index for index, level, _ in headings if index > start and level <= 3), len(lines))
    if not any(line.strip() for line in lines[start + 1:end]):
        raise VersionGateError(f"API {version} documentation entry needs explanatory text")
    return "\n".join(lines[start:end]).strip()


def current_text(root: Path, relative: str) -> str:
    path = root / relative
    for component in (path, *path.parents):
        if component == root:
            break
        if component.is_symlink():
            raise VersionGateError(f"{relative} must be a regular repository file, not a symlink")
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise VersionGateError(f"cannot read {relative}: {error}") from error


def base_text(root: Path, commit: str, relative: str) -> str | None:
    listing = git(root, "ls-tree", "-z", commit, "--", relative)
    if not listing:
        return None
    if not listing.startswith((b"100644 blob ", b"100755 blob ")):
        raise VersionGateError(f"base {relative} must be a regular repository file")
    try:
        return git(root, "show", f"{commit}:{relative}").decode("utf-8")
    except UnicodeError as error:
        raise VersionGateError(f"base {relative} must be UTF-8") from error


def check(root: Path, base: str) -> str:
    root = Path(git(root, "rev-parse", "--show-toplevel").decode().strip()).resolve()
    commit = git(root, "rev-parse", "--verify", "--end-of-options", f"{base}^{{commit}}").decode().strip()
    changed = git(
        root, "diff", "--no-ext-diff", "--no-textconv", "--no-renames",
        "--name-only", "-z", commit, "--", API_DIRECTORY,
    )
    untracked = git(root, "ls-files", "--others", "-z", "--", API_DIRECTORY)
    if not changed and not untracked:
        return "PASS: no API-directory changes"

    new = parse_version(current_text(root, VERSION_FILE), VERSION_FILE)
    previous = base_text(root, commit, VERSION_FILE)
    if previous is None:
        if git(root, "ls-tree", "-r", "--name-only", commit, "--", API_DIRECTORY):
            raise VersionGateError("base API directory exists but its version file is missing")
    elif new <= parse_version(previous, f"base {VERSION_FILE}"):
        raise VersionGateError("API-directory changes require a strictly newer API_VERSION")

    version = ".".join(map(str, new))
    document = current_text(root, DOCUMENTATION)
    old_document = base_text(root, commit, DOCUMENTATION) or ""
    if document == old_document:
        raise VersionGateError("API-directory changes require an update to docs/proposer-api.md")
    entry = version_entry(document, version)
    if entry is None:
        raise VersionGateError(f"documentation needs a ### {version} version entry")
    if entry == version_entry(old_document, version):
        raise VersionGateError(f"API {version} documentation entry must be new or updated")
    return f"PASS: API changes documented at version {version}"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True, help="explicit Git comparison commit/ref")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    arguments = parser.parse_args()
    try:
        print(check(arguments.root, arguments.base))
    except (VersionGateError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
