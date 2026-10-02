#!/usr/bin/env python3
"""Measure every emitter-written certificate and record where its kernel check runs.

A certificate whose kernel check does not fit the watched build's memory limit cannot sit in
the library root: the whole library build dies with it. Which certificates those are is
machine state, not curation, so it is measured here and written to one generated, tracked
ledger, `Benchmark/CertificatePlacement.json`:

    {"version": 2, "limitKb": 4194304,
     "certificates": {"Example0013": {"treeSha256": "…", "fits": true, "peakKb": 1802240},
                      "Example5013": {"treeSha256": "…", "fits": false, "peakKb": 6942000,
                                      "note": "peak resident memory 6942000 KB while …"}}}

`treeSha256` digests the sorted relative paths and bytes of every regular, non-hidden file
under the case's `Certificate/` directory, so a re-emitted certificate no longer matches its
entry and is measured again, and a case that used to be too heavy returns to the library by
itself as soon as a new measurement fits. Nothing here is hand-maintained: no metadata key
decides placement, and no edit is needed to move a case either way.

The registry generator reads the ledger to decide whether a case's certificates are listed
in `Benchmark/Certificates.lean` or in `Benchmark/OutsideLibrary.lean`; the benchmark report
reads it to say which cases are checked outside the library build. Both can ask
`ledger_problems(root)` whether the ledger still matches the tree without building anything.

How a case is measured, one certificate root at a time:

  1. The modules the root imports are built with `scripts/lake_build_watched.sh` under the
     library build's own limit. Any non-zero result there is a hard error, never a placement:
     the imports are shared library modules, so their failure is repository breakage.
  2. The root itself is then elaborated once from source, `lake env lean <file>` with a single
     thread, inside a generous hard safety cap so that a runaway check cannot take the machine
     down. Its peak resident memory is read from the operating system's own accounting rather
     than sampled, so a result near the limit does not depend on when a poll happened to land.
  3. The certificate fits when that check succeeded and its peak is at or under the limit. A
     peak above the limit places the case outside the library build. Any non-zero status is a
     broken certificate (or a check too heavy even for the safety cap): it is reported, no
     entry is written, and the entry the case had is dropped, because a certificate that does
     not check must never be recorded as merely too heavy.

Usage:
  python3 scripts/place_certificates.py                    # measure what changed, write the ledger
  python3 scripts/place_certificates.py --ids Example5013  # only the named cases
  python3 scripts/place_certificates.py --check            # is the ledger current? builds nothing
  python3 scripts/place_certificates.py --force            # re-measure unchanged certificates too
  python3 scripts/place_certificates.py --limit-kb 10485760
  python3 scripts/place_certificates.py --hard-limit-kb 16777216
  python3 scripts/place_certificates.py --jobs 1           # one certificate module at a time

Every certificate root imports a handful of independent leaf modules (a case's own proof-job
reconstructions) before it can be elaborated itself. `--jobs` bounds how many of those leaves
`scripts/lake_build_watched.sh` may compile at once, by raising the `LEAN_NUM_THREADS` it hands
to `lake build`: Lake already knows which of the imports it is given are independent and which
depend on which, so nothing here re-derives that graph. `--jobs 1` reproduces the old
one-at-a-time behaviour exactly. Left unset, `--jobs` is sized from the detected CPU count and
memory so that the worst case of every concurrent `lean` worker reaching `--limit-kb` at once
still fits in RAM; see `default_jobs`. It never changes a placement decision, only how quickly
the script reaches it: the certificate root itself is always elaborated on one thread, exactly
as before, so its measured peak does not depend on how many other things happened to be building
alongside it.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import resource
import subprocess
import shutil
import sys
from pathlib import Path
from typing import Callable, NamedTuple

ROOT = Path(__file__).resolve().parents[1]
CASES = "Benchmark"
LEDGER_NAME = "CertificatePlacement.json"
LEDGER_PATH = f"{CASES}/{LEDGER_NAME}"
LEDGER_VERSION = 2
DEFAULT_LIMIT_KB = 4194304
# The safety cap is not the measurement: it exists only so that a certificate whose check
# never stops cannot exhaust the machine. It is deliberately far above the library limit, and
# a check that reaches it is an error rather than a placement, because a killed check has no
# peak to record.
DEFAULT_HARD_LIMIT_KB = 12582912
KB_PER_GIB = 1024 * 1024
# The ceiling on the default `--jobs`: a handful of concurrent `lean` workers already keeps the
# machine busy, and this is also the largest value this build has actually been exercised at.
DEFAULT_JOBS_CAP = 4
# A certificate counts only when the Lean-owned emitter wrote it; a hand-written file does not.
EMITTER_MARK = "-- Generated by the Lean-owned fixed-ambient certificate emitter."
EMITTER_MARKS = (EMITTER_MARK, "-- Generated by the Lean-owned fixed-ambient certificate-emitter-v2.")
CERTIFICATE_MODULES = ("Valid", "ProposalBinding", "Invalid")
DIGEST_DOMAIN = b"whiel-certificate-tree-v1"
BUILD_SCRIPT = "scripts/lake_build_watched.sh"
WATCHDOG_SCRIPT = "scripts/watchdog.sh"
IMPORT_LINE = re.compile(r"^import[ \t]+([A-Za-z_][A-Za-z0-9_.']*)", re.M)
# The status `scripts/watchdog.sh` exits with when it kills what it is watching.
HARD_CAP_STATUS = 137
MEASURE_FLAG = "--measure-one"
TAIL_CHARS = 2000


class PlacementError(RuntimeError):
    """A certificate could not be measured; the ledger keeps no entry for it."""


class Run(NamedTuple):
    """What one build or elaboration reported.

    `peak_kb` is the largest resident set any single process of the command reached, in KB.
    """

    status: int
    output: str
    peak_kb: int


Builder = Callable[[list[str], "dict[str, str]"], Run]


def maxrss_kb(maxrss: int, platform: str | None = None) -> int:
    """`ru_maxrss` in KB: the field is bytes on macOS and kilobytes on Linux."""
    return maxrss // 1024 if (platform or sys.platform) == "darwin" else maxrss


def default_jobs(cores: int, memory_kb: int) -> int:
    """`min(DEFAULT_JOBS_CAP, max(1, cores // 2), memory_kb // 4 GiB)`, never below 1.

    Pure arithmetic on an already-known core count and memory size, so it is exercised directly
    by tests without touching the real machine. `cores // 2` leaves room for the rest of the
    machine (the shell driving this script, the watchdog's own polling, anything else running);
    `memory_kb // 4 GiB` assumes the worst case, every concurrent `lean` worker reaching
    `DEFAULT_LIMIT_KB` at once, so raising `--limit-kb` well past 4 GiB calls for a smaller
    explicit `--jobs` too, since this default does not know about that override.
    """
    by_cores = max(1, cores // 2)
    by_memory = max(1, memory_kb // (4 * KB_PER_GIB))
    return max(1, min(DEFAULT_JOBS_CAP, by_cores, by_memory))


def detected_memory_kb() -> int | None:
    """Total physical memory in KB, or None when this platform cannot report it.

    Best-effort and used only to size the default `--jobs`; an explicit `--jobs` never calls it.
    """
    try:
        return (os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE")) // 1024
    except (ValueError, OSError, AttributeError):
        pass
    if sys.platform == "darwin":
        try:
            done = subprocess.run(["sysctl", "-n", "hw.memsize"], capture_output=True, text=True,
                                  timeout=5)
            if done.returncode == 0:
                return int(done.stdout.strip()) // 1024
        except (OSError, ValueError, subprocess.SubprocessError):
            pass
    return None


def resolved_default_jobs() -> int:
    """The default `--jobs` for this machine, or 1 when memory cannot be determined.

    A concurrency budget this script cannot verify against real memory is not a default worth
    guessing at: it falls back to today's one-at-a-time behaviour instead.
    """
    memory_kb = detected_memory_kb()
    if memory_kb is None:
        return 1
    return default_jobs(os.cpu_count() or 1, memory_kb)


def measure_one(request: str) -> int:
    """Run one command to completion and print its status, output and peak resident memory.

    This is the body of the `--measure-one` subcommand, and it exists so that every
    measurement gets a process of its own. `resource.getrusage(RUSAGE_CHILDREN).ru_maxrss` is
    a running maximum over every descendant the calling process has waited for, so it is only
    this command's peak in a process that has waited for nothing else. The figure is a maximum
    over processes, not a sum over the tree: it reports the largest single descendant, which is
    exactly the per-`lean` metric the library build's watchdog applies.
    """
    spec = json.loads(request)
    done = subprocess.run(list(spec["command"]),
                          env={**os.environ, **dict(spec.get("env") or {})},
                          capture_output=True, text=True)
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    sys.stdout.write(json.dumps({"status": done.returncode,
                                 "output": (done.stdout or "") + (done.stderr or ""),
                                 "peakKb": maxrss_kb(usage.ru_maxrss)}) + "\n")
    return 0


def shell_builder(root: Path) -> Builder:
    """The real builder: run the command in the checkout and report what it peaked at.

    Every command is run by a fresh `--measure-one` helper process, which waits for it and
    reports the operating system's own peak for it. Nothing is sampled, so a certificate that
    sits just under or just over the limit is placed the same way every time.
    """
    script = str(Path(__file__).resolve())

    def run(command: list[str], env: dict[str, str]) -> Run:
        request = json.dumps({"command": list(command), "env": dict(env)})
        done = subprocess.run([sys.executable, script, MEASURE_FLAG, request],
                              cwd=root, capture_output=True, text=True)
        lines = [line for line in (done.stdout or "").splitlines() if line.strip()]
        try:
            reported = json.loads(lines[-1]) if lines else None
            if not isinstance(reported, dict):
                raise ValueError("not an object")
            return Run(int(reported["status"]), str(reported["output"]),
                       int(reported["peakKb"]))
        except (IndexError, KeyError, TypeError, ValueError) as error:
            raise PlacementError(
                f"the measuring helper reported nothing usable ({error}) for "
                f"{' '.join(command)}; it exited with status {done.returncode}\n"
                f"{tail((done.stdout or '') + (done.stderr or ''))}") from error

    return run


def tail(text: str) -> str:
    return text[-TAIL_CHARS:] if len(text) > TAIL_CHARS else text


# --------------------------------------------------------------------------------------
# The corpus: which cases carry an emitter-written certificate, and what it hashes to
# --------------------------------------------------------------------------------------

def emitter_wrote(path: Path) -> bool:
    """True when the file exists and its first line is the certificate emitter's marker."""
    if path.is_symlink() or not path.is_file():
        return False
    with path.open(encoding="utf-8") as handle:
        return handle.readline().rstrip("\n") in EMITTER_MARKS


def certificate_roots(case_dir: Path) -> list[str]:
    """The emitter-written certificate roots of a case, in the order they are measured."""
    return [name for name in CERTIFICATE_MODULES
            if emitter_wrote(case_dir / "Certificate" / f"{name}.lean")]


def certified_cases(root: Path) -> dict[str, list[str]]:
    """Every case folder with an emitter-written certificate, mapped to its certificate roots."""
    out: dict[str, list[str]] = {}
    base = root / CASES
    if not base.is_dir():
        raise PlacementError(f"no {CASES}/ directory to measure")
    for directory in sorted(base.iterdir(), key=lambda p: p.name):
        if not directory.is_dir():
            continue
        if not (directory / "Input.lean").is_file() or not (directory / "Metadata.json").is_file():
            continue
        roots = certificate_roots(directory)
        if roots:
            out[directory.name] = roots
    return out


def tree_digest(case_dir: Path) -> str:
    """A digest of the emitted files under the case's Certificate/ directory, paths included.

    Any re-emission — a changed proof, a new clause file, a removed one — changes the digest,
    which is what makes a stale measurement impossible to mistake for a current one. Only
    regular files whose every path component is visible are hashed: a hidden file is never
    something the emitter wrote, it is the operating system's or a tool's own litter (a folder
    view's state file, an editor's swap file, a lock file), and litter appearing beside a
    certificate must not invalidate a measurement of that certificate.
    """
    base = case_dir / "Certificate"
    entries: list[tuple[str, Path]] = []
    if base.is_dir():
        for path in base.rglob("*"):
            rel = path.relative_to(base).as_posix()
            if any(part.startswith(".") for part in rel.split("/")):
                continue
            if path.is_symlink():
                raise PlacementError(f"symlink refused under {case_dir.name}/Certificate: {rel}")
            if path.is_file():
                entries.append((rel, path))
    digest = hashlib.sha256()
    digest.update(DIGEST_DOMAIN + b"\0")
    for rel, path in sorted(entries):
        data = path.read_bytes()
        digest.update(rel.encode("utf-8") + b"\0")
        digest.update(str(len(data)).encode("ascii") + b"\0")
        digest.update(data + b"\0")
    return digest.hexdigest()


# --------------------------------------------------------------------------------------
# Measurement
# --------------------------------------------------------------------------------------

def imports_of(path: Path) -> list[str]:
    """The modules a certificate root imports, in order and without repetition."""
    seen: set[str] = set()
    out: list[str] = []
    for match in IMPORT_LINE.finditer(path.read_text(encoding="utf-8")):
        name = match.group(1)
        if name not in seen:
            seen.add(name)
            out.append(name)
    return out


def too_heavy_note(peak_kb: int, name: str, limit_kb: int) -> str:
    """How the ledger says that a certificate's own check is over the library build's limit."""
    return (f"peak resident memory {peak_kb} KB while checking Certificate/{name}.lean "
            f"exceeds the library build's {limit_kb} KB limit")


def measure(root: Path, case: str, roots: list[str], limit_kb: int, hard_limit_kb: int,
            jobs: int, builder: Builder) -> tuple[bool, str, int]:
    """Check every certificate root of the case and report what the heaviest one peaked at.

    Returns (fits, note, peak_kb): `peak_kb` is the maximum over the case's roots, the note is
    empty when the certificate fits and otherwise names that peak, the root that reached it and
    the limit. A case is also outside the library when a proof module it imports builds only
    under the hard safety cap. Raises PlacementError when anything failed to build or check
    under that cap, so that a broken certificate can never be written down as merely too heavy.

    `jobs` bounds how many of a root's independent leaf imports `lake build` may compile at
    once (see the module docstring); it is applied only to that build, at the ordinary
    `limit_kb`. The hard-limit retry below stays single-threaded on purpose: it exists only to
    tell a genuinely broken module apart from one that is merely too heavy, so it runs rarely,
    and `jobs` concurrent workers each allowed up to `hard_limit_kb` could together ask for far
    more memory than the machine has. The root's own elaboration is likewise always
    single-threaded, exactly as before `--jobs` existed, so a certificate's measured peak never
    depends on how many other things happened to be building alongside it.
    """
    peaks: list[tuple[int, str]] = []
    heavy_import = ""
    # Lake replays a cached build product without elaborating anything, which would measure
    # nothing: drop this certificate's own build products so its proof modules are rebuilt.
    for kind in ("lib/lean", "ir"):
        shutil.rmtree(root / ".lake" / "build" / kind / CASES / case / "Certificate",
                      ignore_errors=True)
    for name in roots:
        relative = f"{CASES}/{case}/Certificate/{name}.lean"
        source = root / relative
        imports = imports_of(source)
        if imports:
            run = builder([BUILD_SCRIPT, *imports],
                          {"LIMIT_KB": str(limit_kb), "LEAN_NUM_THREADS": str(jobs)})
            if run.status != 0:
                # A proof module the certificate imports may itself be over the limit. Whatever
                # the first failure was, the modules must build cleanly under the hard cap:
                # success there proves them valid, and only then is the case merely heavy.
                retry = builder([BUILD_SCRIPT, *imports],
                                {"LIMIT_KB": str(hard_limit_kb), "LEAN_NUM_THREADS": "1"})
                if retry.status != 0:
                    raise PlacementError(
                        f"{case}: building the modules imported by {relative} failed with "
                        f"status {retry.status} even under the hard safety cap of "
                        f"{hard_limit_kb} KB\n  modules: {' '.join(imports)}\n"
                        f"{tail(retry.output)}")
                heavy_import = name
        run = builder([WATCHDOG_SCRIPT, str(hard_limit_kb), "lake", "env", "lean", relative],
                      {"LEAN_NUM_THREADS": "1"})
        if run.status == HARD_CAP_STATUS:
            raise PlacementError(
                f"{case}: checking {relative} exceeded the hard safety cap of {hard_limit_kb} "
                f"KB; raise --hard-limit-kb to measure it\n{tail(run.output)}")
        if run.status != 0:
            raise PlacementError(f"{case}: checking {relative} failed with status "
                                 f"{run.status}\n{tail(run.output)}")
        peaks.append((int(run.peak_kb), name))
    peak_kb, heaviest = max(peaks, default=(0, ""))
    if peak_kb > limit_kb:
        return False, too_heavy_note(peak_kb, heaviest, limit_kb), peak_kb
    if heavy_import:
        return False, (f"a proof module imported by Certificate/{heavy_import}.lean does not "
                       f"build under the library build's {limit_kb} KB limit; it builds under "
                       f"{hard_limit_kb} KB"), peak_kb
    return True, "", peak_kb


# --------------------------------------------------------------------------------------
# The ledger
# --------------------------------------------------------------------------------------

def ledger_file(root: Path) -> Path:
    return root / CASES / LEDGER_NAME


def is_size(value: object) -> bool:
    """True for a plain non-negative integer; a boolean is not one, however Python counts it."""
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def entry_problems(case: str, entry: object) -> list[str]:
    """Everything wrong with the shape of one ledger entry."""
    if not isinstance(entry, dict):
        return [f"{case}: the ledger entry is not an object"]
    problems: list[str] = []
    if not isinstance(entry.get("treeSha256"), str):
        problems.append(f"{case}: treeSha256 is not a string")
    if not isinstance(entry.get("fits"), bool):
        problems.append(f"{case}: fits is not a boolean")
    if not is_size(entry.get("peakKb")):
        problems.append(f"{case}: peakKb is not a non-negative integer")
    return problems


def read_ledger(root: Path) -> tuple[int | None, dict[str, dict]]:
    """(limitKb, entries) of the ledger; (None, {}) when there is none or it is an older version.

    A ledger written before this version recorded a different measurement, so none of its
    entries is reused: everything it names is measured again.
    """
    path = ledger_file(root)
    if not path.is_file():
        return None, {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except ValueError as error:
        raise PlacementError(f"malformed {LEDGER_PATH}: {error}") from error
    if not isinstance(data, dict):
        raise PlacementError(f"{LEDGER_PATH} is not a JSON object")
    if data.get("version") != LEDGER_VERSION:
        return None, {}
    entries = data.get("certificates")
    if not isinstance(entries, dict):
        raise PlacementError(f"{LEDGER_PATH} has no certificates object")
    for case in sorted(entries):
        problems = entry_problems(case, entries[case])
        if problems:
            raise PlacementError(f"{LEDGER_PATH}: {problems[0]}")
    limit = data.get("limitKb")
    return (limit if is_size(limit) else None), entries


def ledger_text(limit_kb: int, entries: dict[str, dict]) -> str:
    """The ledger as bytes-on-disk: keys sorted, 2-space indent, one trailing newline."""
    body: dict[str, dict] = {}
    for case in sorted(entries):
        entry = entries[case]
        fits = bool(entry["fits"])
        written = {"treeSha256": entry["treeSha256"], "fits": fits,
                   "peakKb": int(entry.get("peakKb") or 0)}
        if not fits:
            written["note"] = str(entry.get("note") or "")
        body[case] = written
    return json.dumps({"version": LEDGER_VERSION, "limitKb": limit_kb, "certificates": body},
                      indent=2, ensure_ascii=False) + "\n"


def write_ledger(root: Path, limit_kb: int, entries: dict[str, dict]) -> bool:
    """Write the ledger unless the bytes are already there; True when the file changed."""
    path = ledger_file(root)
    text = ledger_text(limit_kb, entries)
    if path.is_file() and path.read_text(encoding="utf-8") == text:
        return False
    path.write_text(text, encoding="utf-8")
    return True


def ledger_problems(root: Path | str) -> list[str]:
    """Every reason the ledger does not match the tree, in the words `--check` prints.

    Pure: it reads the corpus and the ledger and builds nothing, so any generator that must
    refuse to run from a stale placement can call it. An empty list means every case with an
    emitter-written certificate has a well-formed entry of the current version whose digest
    still matches the certificate tree, and that the ledger names no case that has none.
    """
    return ledger_findings(Path(root), None, None)


def ledger_findings(root: Path, ids: list[str] | None, limit_kb: int | None) -> list[str]:
    """`ledger_problems`, restricted to `ids` and optionally told which limit was asked for."""
    path = ledger_file(root)
    try:
        cases = certified_cases(root)
    except PlacementError as error:
        return [str(error)]
    if not path.is_file():
        # A corpus with no certificate has nothing to place and needs no ledger.
        return [f"{LEDGER_PATH} is missing; run scripts/place_certificates.py"] if cases else []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except ValueError as error:
        return [f"malformed {LEDGER_PATH}: {error}"]
    if not isinstance(data, dict):
        return [f"{LEDGER_PATH} is not a JSON object"]
    if data.get("version") != LEDGER_VERSION:
        return [f"{LEDGER_PATH} is version {data.get('version')!r}, not version "
                f"{LEDGER_VERSION}; re-run placement"]
    entries = data.get("certificates")
    if not isinstance(entries, dict):
        return [f"{LEDGER_PATH} has no certificates object"]

    problems: list[str] = []
    limit = data.get("limitKb")
    if limit_kb is not None and is_size(limit) and limit != limit_kb:
        problems.append(f"the ledger was measured at {limit} KB, not at {limit_kb} KB")
    malformed: set[str] = set()
    for case in sorted(entries):
        shape = entry_problems(case, entries[case])
        if shape:
            malformed.add(case)
            problems.extend(shape)
    selected = list(ids) if ids else sorted(cases)
    for case in selected:
        if case not in cases:
            problems.append(f"{case}: no emitter-written certificate to place")
        elif case not in entries:
            problems.append(f"{case}: no entry in the ledger")
        elif case not in malformed \
                and entries[case]["treeSha256"] != tree_digest(root / CASES / case):
            problems.append(f"{case}: the certificate changed since it was measured")
    if not ids:
        for case in sorted(entries):
            if case not in cases:
                problems.append(f"{case}: stale entry, the case has no emitter-written certificate")
    return problems


# --------------------------------------------------------------------------------------
# The two modes
# --------------------------------------------------------------------------------------

def check(root: Path, ids: list[str] | None, limit_kb: int) -> int:
    """Report whether the ledger is current. Builds nothing and writes nothing."""
    problems = ledger_findings(root, ids, limit_kb)
    if problems:
        print(f"ERROR: {LEDGER_PATH} is not current:", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        print("  run scripts/place_certificates.py to measure what changed", file=sys.stderr)
        return 1
    counted = len(ids) if ids else len(certified_cases(root))
    print(f"{LEDGER_PATH} is current: {counted} certificate(s) checked against the tree")
    return 0


def place(root: Path, ids: list[str] | None, limit_kb: int, hard_limit_kb: int, jobs: int,
          force: bool, builder: Builder) -> int:
    """Measure what changed and write the ledger. Returns the process exit status."""
    cases = certified_cases(root)
    if ids:
        for case in ids:
            if case not in cases:
                raise PlacementError(f"{case}: no emitter-written certificate to place")
        selection = {case: cases[case] for case in ids}
    else:
        selection = cases

    limit, previous = read_ledger(root)
    entries = {case: dict(entry) for case, entry in previous.items()}
    # A ledger measured at another limit says nothing about this one.
    remeasure_all = force or (limit is not None and limit != limit_kb)
    dropped: list[str] = []
    if not ids:
        for case in sorted(entries):
            if case not in cases:
                del entries[case]
                dropped.append(case)

    measured: list[str] = []
    unchanged: list[str] = []
    errors: list[str] = []
    for case in sorted(selection):
        digest = tree_digest(root / CASES / case)
        entry = entries.get(case)
        if entry is not None and not remeasure_all and entry["treeSha256"] == digest:
            unchanged.append(case)
            continue
        print(f"measuring {case} ({', '.join(selection[case])})...", flush=True)
        try:
            fits, note, peak_kb = measure(root, case, selection[case], limit_kb, hard_limit_kb,
                                          jobs, builder)
        except PlacementError as error:
            errors.append(str(error))
            entries.pop(case, None)
            continue
        entries[case] = {"treeSha256": digest, "fits": fits, "note": note, "peakKb": peak_kb}
        measured.append(case)
        print(f"  {case}: {'inside' if fits else 'outside'} the library build, "
              f"peak {peak_kb} KB", flush=True)

    changed = write_ledger(root, limit_kb, entries)
    inside = sorted(case for case, entry in entries.items() if entry["fits"])
    outside = sorted(case for case, entry in entries.items() if not entry["fits"])
    print(f"measured {len(measured)}, unchanged {len(unchanged)}, "
          f"dropped {len(dropped)}, errors {len(errors)}")
    print(f"inside the library build: {len(inside)}")
    print(f"outside the library build: {len(outside)}"
          + (": " + ", ".join(outside) if outside else ""))
    for case in outside:
        print(f"  {case}: {entries[case].get('note', '')}")
    for case in dropped:
        print(f"  dropped the stale entry for {case}")
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    if errors:
        print("ERROR: no ledger entry was written for the case(s) above; a certificate that "
              "does not check is broken, not merely too heavy", file=sys.stderr)
    print(f"{'wrote' if changed else 'already current:'} {LEDGER_PATH}")
    print("next: python3 scripts/generate_fixed_ambient_registry.py, "
          "then python3 Benchmark/report/build_report.py")
    return 1 if errors else 0


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--ids", nargs="+", metavar="CASE",
                        help="measure (or check) only these case directories")
    parser.add_argument("--check", action="store_true",
                        help="verify that the ledger matches the tree; build and write nothing")
    parser.add_argument("--limit-kb", type=int, default=DEFAULT_LIMIT_KB,
                        help=f"the library build's memory limit in KB (default {DEFAULT_LIMIT_KB})")
    parser.add_argument("--hard-limit-kb", type=int, default=DEFAULT_HARD_LIMIT_KB,
                        help="the safety cap that stops a runaway check, in KB "
                             f"(default {DEFAULT_HARD_LIMIT_KB})")
    parser.add_argument("--force", action="store_true",
                        help="re-measure even a certificate whose digest still matches")
    parser.add_argument("--jobs", type=int, default=None,
                        help="concurrent lean workers per certificate root's import build "
                             "(default: sized from detected cores and memory; 1 reproduces the "
                             "old one-at-a-time behaviour)")
    parser.add_argument(MEASURE_FLAG, metavar="JSON",
                        help="internal: run one command and report its peak resident memory")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None, builder: Builder | None = None,
         root: Path | str | None = None) -> int:
    base = Path(root) if root is not None else ROOT
    args = parse_args(argv)
    if args.measure_one is not None:
        return measure_one(args.measure_one)
    if args.limit_kb <= 0 or args.hard_limit_kb <= 0:
        print("ERROR: --limit-kb and --hard-limit-kb must be positive", file=sys.stderr)
        return 2
    if args.hard_limit_kb < args.limit_kb:
        print("ERROR: --hard-limit-kb is below --limit-kb, so no certificate could be measured",
              file=sys.stderr)
        return 2
    if args.jobs is not None and args.jobs <= 0:
        print("ERROR: --jobs must be positive", file=sys.stderr)
        return 2
    jobs = args.jobs if args.jobs is not None else resolved_default_jobs()
    try:
        if args.check:
            if args.force:
                print("ERROR: --check measures nothing, so --force means nothing with it",
                      file=sys.stderr)
                return 2
            return check(base, args.ids, args.limit_kb)
        return place(base, args.ids, args.limit_kb, args.hard_limit_kb, jobs, args.force,
                     builder or shell_builder(base))
    except PlacementError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
