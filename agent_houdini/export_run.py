# Author: Fangzhu Shen
"""Copy a run directory for a collaborator, and refuse to leak this machine.

`python3 -m agent_houdini export-run RUN_DIR DEST` copies a run directory
(made by `experiment run`, or a bare `campaign run` destination) to `DEST`,
leaving out every `native-*` file -- the raw provider stdout/stderr/debug
streams `run_records.py` retains under `--agent-retention all` -- and any
other provider debug or session file. It then scans every copied file for
this machine's own layout: the account's user name, its home directory, the
process's temporary-directory prefixes, the two conventional absolute-path
roots and the machine's host name. A hit is printed in full, with the file
and a line number or byte offset, and the command exits non-zero having
deleted `DEST` again: an export either carries none of this, or it does not
exist.

`python3 -m agent_houdini export-run --check-only RUN_DIR` runs the same scan
in place, without copying anything, so a collaborator can see what would
block an export before making one.

Both modes derive the scan list from the running process (`getpass.getuser`,
`Path.home`, `tempfile.gettempdir`, `socket.gethostname`), never from a
hard-coded name, so the check is exactly this machine's own, whoever runs it.

This is diagnostic tooling around the run directory, not the campaign or the
proposer: it reads and copies files and never talks to the verifier or a
provider.
"""

from __future__ import annotations

import argparse
import getpass
from pathlib import Path
import shutil
import socket
import sys
import tempfile


TEXT_EXCERPT_BYTES = 300
BINARY_CONTEXT_BYTES = 24
# Every file name `run_records.py` writes for a native provider's own raw
# stream. `native_debug.txt`'s sibling prefix covers `native-stdout.jsonl` and
# `native-stderr.txt` too, so one prefix check is the whole rule. Retention
# writes no other provider debug or session file today; a later one belongs
# in this set, named exactly, the day it exists.
NATIVE_PREFIX = "native-"
OTHER_EXCLUDED_NAMES = frozenset()
# Deliberately empty: every hit this scan can produce is either fixed by
# excluding the file that carries it (above) or fixed at the source in the
# writer that produced it (`agent_houdini/safe_paths.py` and its callers).
# Nothing is allow-listed instead of fixed.
ALLOWED_HITS = ()


def is_excluded(path: Path) -> bool:
    """Whether `path` is a raw provider stream or other excluded file."""
    return path.name.startswith(NATIVE_PREFIX) or path.name in OTHER_EXCLUDED_NAMES


def unsafe_markers() -> list[str]:
    """The literal substrings this run must not carry, read from this process.

    Every value here comes from the environment the export command itself
    runs in -- never a name typed into the tool -- so the check is always
    this machine's own account, home directory, temp directories and host
    name, not a fixed list that could go stale or miss a collaborator's own
    machine.
    """
    home = str(Path.home())
    tmp = tempfile.gettempdir().rstrip("/")
    markers = {getpass.getuser(), home, "/tmp/", "/private/", "/var/folders/",
              tmp + "/", "/Users/", "/home/", socket.gethostname()}
    return sorted(marker for marker in markers if marker and marker not in ("/", ""))


def _text_hits(text: str, markers: list[str]):
    for number, line in enumerate(text.split("\n"), start=1):
        for marker in markers:
            if marker in line:
                yield marker, f"line {number}", line.strip()[:TEXT_EXCERPT_BYTES]


def _binary_hits(data: bytes, markers: list[str]):
    for marker in markers:
        needle = marker.encode("utf-8", errors="ignore")
        if not needle:
            continue
        offset = data.find(needle)
        while offset != -1:
            start = max(0, offset - BINARY_CONTEXT_BYTES)
            end = offset + len(needle) + BINARY_CONTEXT_BYTES
            yield marker, f"byte offset {offset}", data[start:end].decode("utf-8", errors="replace")
            offset = data.find(needle, offset + 1)


def scan_file(path: Path, markers: list[str]):
    """Every unsafe-marker hit in one file, as `(marker, location, excerpt)`.

    A file that decodes as UTF-8 text is scanned line by line, so a hit names
    its line number; anything else -- a binary certificate artifact, a solver
    witness -- is scanned as raw bytes, so a hit names a byte offset instead.
    Nothing here redacts the excerpt: a hit is reported in full, exactly what
    would otherwise have reached a collaborator.
    """
    try:
        data = path.read_bytes()
    except OSError as error:
        return [("(unreadable)", "?", str(error))]
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return list(_binary_hits(data, markers))
    return list(_text_hits(text, markers))


def find_hits(root: Path, *, skip_excluded: bool):
    """Every unsafe hit under `root`, as `(relative_path, marker, location, excerpt)`.

    `skip_excluded` is true for `--check-only`, which predicts an export
    without copying: a `native-*` file never reaches `DEST`, so it is not
    scanned for one either. A real export scans what it already copied, which
    never included an excluded file in the first place.
    """
    root = Path(root)
    markers = unsafe_markers()
    hits = []
    for path in sorted(root.rglob("*")):
        if path.is_dir() or path.is_symlink():
            continue
        if skip_excluded and is_excluded(path):
            continue
        relative = path.relative_to(root)
        for marker, location, excerpt in scan_file(path, markers):
            if (str(relative), marker) in ALLOWED_HITS:
                continue
            hits.append((relative, marker, location, excerpt))
    return hits


def _report(hits, *, out, prefix):
    for relative, marker, location, excerpt in hits:
        print(f"{prefix}: unsafe: {relative} {location}: {marker!r} in {excerpt!r}", file=out)


def copy_excluding_native(run_dir: Path, dest: Path) -> None:
    """Copy `run_dir` to the not-yet-existing `dest`, leaving out every
    excluded file; symlinks (the digest's `verifier`/`agent` shortcuts) are
    copied as the relative links they are, not followed.
    """
    def ignore(directory, names):
        base = Path(directory)
        return [name for name in names
               if not (base / name).is_dir() and is_excluded(base / name)]

    shutil.copytree(run_dir, dest, symlinks=True, ignore=ignore)


def export_run(run_dir, dest, *, out=None, err=None) -> int:
    out = sys.stdout if out is None else out
    err = sys.stderr if err is None else err
    run_dir, dest = Path(run_dir), Path(dest)
    if not run_dir.is_dir():
        print(f"export-run: {run_dir} is not a directory", file=err)
        return 2
    if dest.exists() or dest.is_symlink():
        print(f"export-run: {dest} already exists; choose a fresh destination", file=err)
        return 2
    try:
        copy_excluding_native(run_dir, dest)
    except OSError as error:
        print(f"export-run: cannot copy {run_dir} to {dest}: {error}", file=err)
        shutil.rmtree(dest, ignore_errors=True)
        return 2
    hits = find_hits(dest, skip_excluded=False)
    if hits:
        _report(hits, out=err, prefix="export-run")
        shutil.rmtree(dest, ignore_errors=True)
        print(f"export-run: refusing to leave {dest} in place: "
             f"{len(hits)} unsafe hit(s), see above", file=err)
        return 1
    print(f"export-run: {dest}", file=out)
    return 0


def check_only(run_dir, *, out=None) -> int:
    out = sys.stdout if out is None else out
    run_dir = Path(run_dir)
    if not run_dir.is_dir():
        print(f"export-run --check-only: {run_dir} is not a directory", file=out)
        return 2
    hits = find_hits(run_dir, skip_excluded=True)
    if not hits:
        print(f"export-run --check-only: {run_dir}: nothing would block an export", file=out)
        return 0
    _report(hits, out=out, prefix="export-run --check-only")
    print(f"export-run --check-only: {run_dir}: {len(hits)} unsafe hit(s) would block an export",
         file=out)
    return 1


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="python -m agent_houdini export-run", allow_abbrev=False, description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("run_dir", type=Path, nargs="?", metavar="RUN_DIR",
                        help="the run directory to export")
    parser.add_argument("dest", type=Path, nargs="?", metavar="DEST",
                        help="the not-yet-existing directory to export it to")
    parser.add_argument("--check-only", type=Path, default=None, metavar="RUN_DIR",
                        help="scan a run directory in place; report what would block an export")
    options = parser.parse_args(sys.argv[1:] if argv is None else argv)
    if options.check_only is not None:
        if options.run_dir is not None or options.dest is not None:
            parser.error("--check-only stands alone; it takes no RUN_DIR/DEST pair")
        return check_only(options.check_only)
    if options.run_dir is None or options.dest is None:
        parser.error("export-run needs RUN_DIR and DEST")
    return export_run(options.run_dir, options.dest)


if __name__ == "__main__":
    raise SystemExit(main())
