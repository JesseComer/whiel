#!/usr/bin/env python3
"""Verifier freeze tripwire.

The owner's boundary: the VERIFIER is everything that runs inside the search
clock, i.e. inside `search.run()` in `whiel_runner/src/campaign_run.rs`
(proposer exchange, the Houdini controller, entailment checks, Vampire
invocation, search-time counterexample validation, and the Lean worker calls
that prepare obligations and validate counterexamples). The CERTIFIER is
everything after it: certificate building, proof transformation, publication,
placement, `campaign certify`, `certificate build`. See `AGENTS.md`'s
"Verifier Freeze" section for the protocol a tripped check follows.

This script is a cheap tripwire, not a physical partition: some files mix
verifier and certifier code (for example `framework2/publication.rs`, whose
`RunConfiguration` the search itself holds, and whose `publish_valid`/
`publish_invalid` build certificates only after the search returns). Files
like that stay in the verifier set at file granularity rather than being
split, per the owner's decision not to refactor for a true partition.

Subcommands:
  list  - print the verifier file set, one repo-relative path per line,
          grouped as Rust / Lean / pins. `--lean` instead prints the
          declaration-level record (see below): one `name\\tmodule\\tkind\\t
          hash` line per declaration the search-time Lean worker surface
          depends on.
  check - recompute the digest and compare it with the recorded manifest;
          exit 0 if equal, otherwise exit 1, print exactly which files
          changed/were added/removed, and print the protocol. `--lean`
          instead runs the declaration-level tool
          (`scripts/verifier_freeze_decls.lean`) and compares its output
          with the manifest's `lean_declarations`, naming exactly which
          declarations changed, appeared or disappeared. The plain
          (file-level) `check` never runs the Lean tool: it stays the
          always-on, seconds-fast gate; `check --lean` is the slower,
          separately-invoked follow-up that resolves a file-level trip in
          the worker's own module (see the "Verifier Freeze" section of
          `AGENTS.md`).
  bless - rewrite the recorded manifest; refuses unless
          --approved-by-owner is passed. Recomputes the file-level record
          every time. `--lean` additionally (re)computes and writes the
          declaration-level record (`lean_declarations`); without `--lean`,
          any `lean_declarations` already in the manifest is carried over
          unchanged rather than dropped.

The recorded manifest stores a per-file normalised digest (comments and
whitespace formatting do not change it) plus one overall digest over the
sorted `path\\0digest\\n` lines, so `check` can name exactly what changed.
It also stores `rust_digest_version`/`lean_digest_version`: bump the
relevant one in this file whenever that side's normalisation, roots,
exclusion list, or (for Lean) root declarations/traversal rules change, so
digests produced under different rules are never compared as if they meant
the same thing. `check` refuses outright, without attempting a digest
comparison, when the manifest's recorded version differs from this script's
current one. The owner-approved five-file certifier correction is a one-time
exception: it preserves version 1 and every retained baseline hash. Both
file-set identities and removed entries are recorded in
implementation_manifests/certifier-freeze-scope-correction.json; AGENTS.md
documents the scope. Later changes still follow the normal version rule.
"""

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = Path(__file__).resolve().parent
DATA_FILE = SCRIPT_DIR / "verifier_freeze_data.json"
MANIFEST_FILE = SCRIPT_DIR / "verifier_freeze_manifest.json"
DECLS_TOOL = SCRIPT_DIR / "verifier_freeze_decls.lean"
FORMAT_VERSION = 1
# Bump whenever the Rust side's normalisation, roots (`rust_roots` in
# verifier_freeze_data.json), or exclusion list changes.
RUST_DIGEST_VERSION = 1
# Bump whenever the Lean side's normalisation, roots (`lean_source_roots`/
# `lean_root_module`/`lean_extra_files`), or the import-closure traversal
# rule changes.
LEAN_DIGEST_VERSION = 1
# Generous: the declaration tool imports the worker's full dependency
# closure (Mathlib included) from already-built `.olean`s before it does
# any work of its own.
LEAN_DECLS_TIMEOUT_SECONDS = 900

PROTOCOL_TEXT = """\
Verifier freeze protocol:
A tripped check means a file in the verifier set changed since the manifest
was last blessed (`python3 scripts/verifier_freeze.py list` is the record of
what counts as verifier; check it before editing a file you are unsure
about). An agent must not commit the tripping change and must not re-bless
the manifest. Raise it to the user by naming the file(s): the user decides
whether to review the diff or run the freeze replay
(`python3 -m agent_houdini experiment run
agent_houdini/experiments/replay.json`, about 20 minutes, expected 86 of 86
accepted, plus a transcript replay with `compare-runs` and its three replay
fidelity checks when a reference transcript exists). Nobody is required to
run the replay immediately or after every pass. Tripping is not a stop-work
order: continue other authorized work, or find a solution that leaves the
verifier untouched. Re-blessing the manifest needs the user's explicit
approval.\
"""


# ------------------------------------------------------------
# Normalisers
# ------------------------------------------------------------


def _collapse_whitespace(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


_RUST_RAW_STRING_RE = re.compile(r'(?:br|cr|r)(#*)"')
_RUST_STRING_RE = re.compile(r'(?:b|c)?"')
_RUST_CHAR_RE = re.compile(
    r"b?'(?:\\(?:u\{[0-9a-fA-F_]+\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'"
)


def strip_rust_comments(source: str) -> str:
    """Drop `//...` and nested `/* ... */` comments, keeping every string,
    raw string, byte string and char literal (including lifetime-looking
    `'a` sequences, which simply fail every literal pattern below and fall
    through as ordinary characters) untouched."""
    out = []
    i, n = 0, len(source)
    while i < n:
        if source.startswith("//", i):
            end = source.find("\n", i)
            i = n if end < 0 else end
            continue
        if source.startswith("/*", i):
            depth = 1
            i += 2
            while i < n and depth:
                if source.startswith("/*", i):
                    depth += 1
                    i += 2
                elif source.startswith("*/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        m = _RUST_RAW_STRING_RE.match(source, i)
        if m:
            hashes = m.group(1)
            body_start = m.end()
            closing = '"' + hashes
            end = source.find(closing, body_start)
            end_pos = n if end < 0 else end + len(closing)
            out.append(source[i:end_pos])
            i = end_pos
            continue
        m = _RUST_STRING_RE.match(source, i)
        if m:
            j = m.end()
            while j < n and source[j] != '"':
                j += 2 if source[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(source[i:j])
            i = j
            continue
        m = _RUST_CHAR_RE.match(source, i)
        if m:
            out.append(m.group(0))
            i = m.end()
            continue
        out.append(source[i])
        i += 1
    return "".join(out)


_LEAN_CHAR_RE = re.compile(r"'(?:\\.|[^'\\\n])'")


def strip_lean_comments(source: str) -> str:
    """Drop `--...` and nested `/- ... -/` comments (this also covers doc
    comments `/-- ... -/` and module doc comments `/-! ... -/`, which only
    add characters after the same two-character `/-` opener), keeping every
    string and char literal untouched."""
    out = []
    i, n = 0, len(source)
    while i < n:
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = n if end < 0 else end
            continue
        if source.startswith("/-", i):
            depth = 1
            i += 2
            while i < n and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        if source[i] == '"':
            j = i + 1
            while j < n and source[j] != '"':
                j += 2 if source[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(source[i:j])
            i = j
            continue
        m = _LEAN_CHAR_RE.match(source, i)
        if m:
            out.append(m.group(0))
            i = m.end()
            continue
        out.append(source[i])
        i += 1
    return "".join(out)


def normalized_digest(text: str) -> str:
    return hashlib.sha256(_collapse_whitespace(text).encode("utf-8")).hexdigest()


def raw_digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_digest(path: Path) -> str:
    data = path.read_bytes()
    if path.suffix == ".rs":
        return normalized_digest(strip_rust_comments(data.decode("utf-8")))
    if path.suffix == ".lean":
        return normalized_digest(strip_lean_comments(data.decode("utf-8")))
    return raw_digest(data)


# ------------------------------------------------------------
# File-set discovery
# ------------------------------------------------------------


def load_data(data_file: Path = DATA_FILE) -> dict:
    return json.loads(data_file.read_text())


def _is_test_or_fixture(relative_parts: tuple) -> bool:
    if any(part in ("fixtures", "tests") for part in relative_parts[:-1]):
        return True
    basename = relative_parts[-1]
    return basename == "tests.rs" or basename.endswith("_tests.rs")


def rust_files(repo_root: Path, data: dict) -> dict:
    """Every root in `rust_roots` is either a directory (walked
    recursively, subject to the test/fixture pattern and the exclusion
    list) or a single file (added directly if present and not excluded).
    Each root is independently editable, so extending or narrowing the
    Rust side never requires touching this function."""
    exclusions = {entry["path"] for entry in data["rust_exclusions"]}
    files = {}
    for root_entry in data["rust_roots"]:
        root_path = repo_root / root_entry
        if root_path.is_file():
            if root_entry not in exclusions:
                files[root_entry] = root_path
            continue
        for path in sorted(root_path.rglob("*")):
            if not path.is_file():
                continue
            relative = path.relative_to(repo_root).as_posix()
            if _is_test_or_fixture(path.relative_to(root_path).parts):
                continue
            if relative in exclusions:
                continue
            files[relative] = path
    return files


_LEAN_IMPORT_RE = re.compile(
    r"^\s*(?:public\s+|meta\s+)?import(?:\s+all)?\s+([A-Za-z0-9_.]+)", re.MULTILINE
)


def _lean_module_map(repo_root: Path, source_roots: list) -> dict:
    mapping = {}
    for root_name in source_roots:
        base = repo_root / root_name
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
            relative = path.relative_to(repo_root)
            module = ".".join(relative.with_suffix("").parts)
            mapping[module] = path
    return mapping


def lean_files(repo_root: Path, data: dict) -> dict:
    mapping = _lean_module_map(repo_root, data["lean_source_roots"])
    root_module = data["lean_root_module"]
    if root_module not in mapping:
        raise SystemExit(
            f"verifier_freeze: Lean worker root module not found: {root_module}"
        )
    seen = set()
    frontier = [root_module]
    while frontier:
        module = frontier.pop()
        if module in seen:
            continue
        seen.add(module)
        path = mapping.get(module)
        if path is None:
            continue  # external module (Mathlib/Init/Std/...), outside this repo
        for imported in _LEAN_IMPORT_RE.findall(path.read_text()):
            if imported not in seen:
                frontier.append(imported)
    files = {}
    for module in seen:
        path = mapping.get(module)
        if path is not None:
            files[path.relative_to(repo_root).as_posix()] = path
    for extra in data["lean_extra_files"]:
        path = repo_root / extra
        if path.is_file():
            files[extra] = path
    return files


def pin_files(repo_root: Path, data: dict) -> dict:
    files = {}
    for pin in data["pins"]:
        path = repo_root / pin
        if path.is_file():
            files[pin] = path
    return files


def collect_groups(repo_root: Path, data: dict) -> dict:
    return {
        "rust": rust_files(repo_root, data),
        "lean": lean_files(repo_root, data),
        "pins": pin_files(repo_root, data),
    }


def compute_manifest(repo_root: Path, data: dict) -> dict:
    groups = collect_groups(repo_root, data)
    all_files = {}
    for group in groups.values():
        all_files.update(group)
    digests = {relative: file_digest(path) for relative, path in all_files.items()}
    overall = hashlib.sha256()
    for relative in sorted(digests):
        overall.update(f"{relative}\0{digests[relative]}\n".encode("utf-8"))
    return {
        "format_version": FORMAT_VERSION,
        "rust_digest_version": RUST_DIGEST_VERSION,
        "lean_digest_version": LEAN_DIGEST_VERSION,
        "overall_digest": overall.hexdigest(),
        "counts": {name: len(group) for name, group in groups.items()},
        "exclusions": data["rust_exclusions"],
        "files": digests,
    }


# ------------------------------------------------------------
# Declaration-level Lean record (scripts/verifier_freeze_decls.lean)
# ------------------------------------------------------------


def run_lean_decls_tool() -> str:
    """Run the standalone declaration tool and return its raw stdout.
    Never part of the always-on file-level `check`; only `check --lean`,
    `list --lean`, and `bless --lean` invoke it."""
    if not DECLS_TOOL.is_file():
        raise SystemExit(
            f"verifier_freeze: declaration tool not found at "
            f"{DECLS_TOOL.relative_to(REPO_ROOT)}"
        )
    try:
        result = subprocess.run(
            ["lake", "env", "lean", "--run", str(DECLS_TOOL)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=LEAN_DECLS_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as exc:
        raise SystemExit(
            "verifier_freeze: scripts/verifier_freeze_decls.lean timed out "
            f"after {LEAN_DECLS_TIMEOUT_SECONDS}s"
        ) from exc
    if result.returncode != 0:
        raise SystemExit(
            "verifier_freeze: scripts/verifier_freeze_decls.lean failed "
            f"(exit {result.returncode}):\n{result.stderr}"
        )
    return result.stdout


def parse_lean_decls(stdout: str) -> dict:
    """Parse `name\\tmodule\\tkind\\thash` lines into
    `{name: {"module": ..., "kind": ..., "hash": ...}}`."""
    declarations = {}
    for line in stdout.splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) != 4:
            raise SystemExit(
                "verifier_freeze: malformed line from "
                f"verifier_freeze_decls.lean: {line!r}"
            )
        name, module, kind, digest = parts
        declarations[name] = {"module": module, "kind": kind, "hash": digest}
    return declarations


def compute_lean_declarations() -> dict:
    """Run the declaration tool and assemble the recorded-manifest shape:
    the per-declaration map, a count, an overall digest over it, and the
    tool script's own sha256 (so a change to the tool's roots or edge
    rules — not just to a declaration it reports on — is itself
    detectable by `check --lean`)."""
    declarations = parse_lean_decls(run_lean_decls_tool())
    overall = hashlib.sha256()
    for name in sorted(declarations):
        entry = declarations[name]
        overall.update(
            f"{name}\0{entry['module']}\0{entry['kind']}\0{entry['hash']}\n".encode(
                "utf-8"
            )
        )
    return {
        "tool_sha256": raw_digest(DECLS_TOOL.read_bytes()),
        "count": len(declarations),
        "overall_digest": overall.hexdigest(),
        "declarations": declarations,
    }


# ------------------------------------------------------------
# Subcommands
# ------------------------------------------------------------


def cmd_list(args: argparse.Namespace) -> int:
    if args.lean:
        declarations = parse_lean_decls(run_lean_decls_tool())
        print(f"# lean declarations ({len(declarations)})")
        for name in sorted(declarations):
            entry = declarations[name]
            print(f"{name}\t{entry['module']}\t{entry['kind']}\t{entry['hash']}")
        return 0
    data = load_data()
    groups = collect_groups(REPO_ROOT, data)
    for name in ("rust", "lean", "pins"):
        print(f"# {name} ({len(groups[name])})")
        for relative in sorted(groups[name]):
            print(relative)
        print()
    return 0


def cmd_check_lean() -> int:
    if not MANIFEST_FILE.is_file():
        print(
            "verifier_freeze check --lean: no recorded manifest at "
            f"{MANIFEST_FILE.relative_to(REPO_ROOT)}; run "
            "`bless --approved-by-owner --lean` first",
            file=sys.stderr,
        )
        return 1
    recorded = json.loads(MANIFEST_FILE.read_text())
    recorded_lean = recorded.get("lean_declarations")
    if recorded_lean is None:
        print(
            "verifier_freeze check --lean: manifest has no recorded "
            "`lean_declarations`; run `bless --approved-by-owner --lean` "
            "first",
            file=sys.stderr,
        )
        return 1
    current = compute_lean_declarations()
    if current["tool_sha256"] != recorded_lean.get("tool_sha256"):
        print(
            "verifier_freeze check --lean: FAILED "
            "(scripts/verifier_freeze_decls.lean itself changed since the "
            "manifest was blessed — its roots or edge rules may have "
            "changed, so the declaration set below is not comparable to "
            "the recorded one on the same terms; review the tool change "
            "itself, not only the declarations it now reports)"
        )
        return 1
    if current["overall_digest"] == recorded_lean.get("overall_digest"):
        return 0
    current_decls = current["declarations"]
    recorded_decls = recorded_lean.get("declarations", {})
    added = sorted(set(current_decls) - set(recorded_decls))
    removed = sorted(set(recorded_decls) - set(current_decls))
    changed = sorted(
        name
        for name in set(current_decls) & set(recorded_decls)
        if current_decls[name] != recorded_decls[name]
    )
    print("verifier_freeze check --lean: FAILED (declaration digest no longer matches)")
    if changed:
        print("changed:")
        for name in changed:
            print(f"  {name}")
    if added:
        print("appeared:")
        for name in added:
            print(f"  {name}")
    if removed:
        print("disappeared:")
        for name in removed:
            print(f"  {name}")
    print()
    print(PROTOCOL_TEXT)
    return 1


def cmd_check(args: argparse.Namespace) -> int:
    if args.lean:
        return cmd_check_lean()
    data = load_data()
    current = compute_manifest(REPO_ROOT, data)
    if not MANIFEST_FILE.is_file():
        print(
            "verifier_freeze check: no recorded manifest at "
            f"{MANIFEST_FILE.relative_to(REPO_ROOT)}; run "
            "`bless --approved-by-owner` first",
            file=sys.stderr,
        )
        return 1
    recorded = json.loads(MANIFEST_FILE.read_text())
    for key, expected in (
        ("rust_digest_version", RUST_DIGEST_VERSION),
        ("lean_digest_version", LEAN_DIGEST_VERSION),
    ):
        recorded_version = recorded.get(key)
        if recorded_version != expected:
            print(
                f"verifier_freeze check: REFUSED ({key} mismatch: manifest "
                f"has {recorded_version!r}, script has {expected!r}) — the "
                "file set, normalisation, or traversal rules changed since "
                "the manifest was blessed, so a digest comparison would not "
                "mean what it used to; review the change and re-bless with "
                "--approved-by-owner",
                file=sys.stderr,
            )
            return 1
    if current["overall_digest"] == recorded.get("overall_digest"):
        return 0

    current_files = current["files"]
    recorded_files = recorded.get("files", {})
    added = sorted(set(current_files) - set(recorded_files))
    removed = sorted(set(recorded_files) - set(current_files))
    changed = sorted(
        relative
        for relative in set(current_files) & set(recorded_files)
        if current_files[relative] != recorded_files[relative]
    )

    print("verifier_freeze check: FAILED (verifier digest no longer matches)")
    if changed:
        print("changed:")
        for relative in changed:
            print(f"  {relative}")
    if added:
        print("added:")
        for relative in added:
            print(f"  {relative}")
    if removed:
        print("removed:")
        for relative in removed:
            print(f"  {relative}")
    print()
    print(PROTOCOL_TEXT)
    return 1


def cmd_bless(args: argparse.Namespace) -> int:
    if not args.approved_by_owner:
        print(
            "verifier_freeze bless: refused; pass --approved-by-owner to "
            "record the owner's explicit approval before rewriting the "
            "manifest",
            file=sys.stderr,
        )
        return 1
    data = load_data()
    manifest = compute_manifest(REPO_ROOT, data)
    prior = {}
    if MANIFEST_FILE.is_file():
        prior = json.loads(MANIFEST_FILE.read_text())
    if args.lean:
        manifest["lean_declarations"] = compute_lean_declarations()
    elif "lean_declarations" in prior:
        # A plain (file-level-only) re-bless must not silently drop a
        # previously blessed declaration-level record.
        manifest["lean_declarations"] = prior["lean_declarations"]
    MANIFEST_FILE.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    lean_note = ""
    if "lean_declarations" in manifest:
        lean_note = (
            f", {manifest['lean_declarations']['count']} Lean declarations"
        )
    print(
        "verifier_freeze bless: wrote "
        f"{MANIFEST_FILE.relative_to(REPO_ROOT)} "
        f"({len(manifest['files'])} files, digest "
        f"{manifest['overall_digest'][:16]}...{lean_note})"
    )
    return 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description="Verifier freeze tripwire")
    subparsers = parser.add_subparsers(dest="command", required=True)

    list_parser = subparsers.add_parser("list", help="print the verifier file set")
    list_parser.add_argument(
        "--lean",
        action="store_true",
        help="print the declaration-level record instead of the file set",
    )
    list_parser.set_defaults(func=cmd_list)

    check_parser = subparsers.add_parser(
        "check", help="compare the current digest with the recorded manifest"
    )
    check_parser.add_argument(
        "--lean",
        action="store_true",
        help=(
            "run the declaration-level tool and compare it with the "
            "manifest instead of the always-on file-level check"
        ),
    )
    check_parser.set_defaults(func=cmd_check)

    bless_parser = subparsers.add_parser(
        "bless", help="rewrite the recorded manifest"
    )
    bless_parser.add_argument(
        "--approved-by-owner",
        action="store_true",
        help="required: records that the owner approved this manifest",
    )
    bless_parser.add_argument(
        "--lean",
        action="store_true",
        help=(
            "also (re)compute and write the declaration-level record; "
            "without this, any existing one is carried over unchanged"
        ),
    )
    bless_parser.set_defaults(func=cmd_bless)

    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
