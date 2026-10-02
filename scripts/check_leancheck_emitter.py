#!/usr/bin/env python3
"""Regression check for the corrected leancheck emitter.

The locked fixture root holds one directory per emitter defect the pinned
patch series corrects, and each of those holds one case directory per
preserved leancheck job. For every case the check runs the pinned binary on
the preserved problem with the preserved arguments and requires the raw
output to equal the preserved corrected output, modulo the run-volatile
timing, memory, and temporary-path lines and modulo the allocation-dependent
order of the `variable` telescope. The preserved uncorrected output must
exhibit that family's defect, the corrected output must not, the corrected
output must elaborate with the pinned VampLean runtime, and the uncorrected
output must fail to elaborate with that family's stated error.

Elaboration adds import packaging only: the emitted `import VampLean`
line becomes the upstream dependency import plus the Mathlib module that
defines the emitted linter option, and the runtime namespace is opened.
No proof text is rewritten.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))

from leancheck_toolchain import (  # noqa: E402
    REPO,
    Check,
    LeancheckPinError,
    leancheck_role,
    load_lock,
    locked_binary_path,
    locked_patches,
    probe,
    repository_path,
)


VOLATILE_PREFIXES = (
    "-- Time elapsed:",
    "-- Peak memory usage:",
    "-- Success in time",
    "--  found proof, printing to",
)
STEP_HEADER = re.compile(r"^-- step (\d+) (.+)$")
IMPORT_LINE = "import VampLean"
PACKAGING_HEADER = (
    "import VampLean\n"
    "import Mathlib.Tactic.Linter.UnusedTactic\n"
    "open VampLean\n"
)
DEFECT_TOKEN = re.compile(r"(?<![A-Za-z0-9_.])default(?![A-Za-z0-9_])")

FAMILY_FILENAME = "family.json"

TELESCOPE_GROUP = re.compile(
    r"^\s*(?:variable )?\{(?P<names>[^:{}]+?)\s*:\s*(?P<type>[^{}]+?)\}$"
)
TELESCOPE_LINE = re.compile(r"^variable \{(?P<name>\S+) : (?P<type>.+)\}$")
VERSION_PREFIX = "-- Version:"

# The emitter writes every introduced definition symbol as `«_sFn»`, and
# every application of one as that name followed by its arguments, which at
# the sites this check inspects are always variables: the `let` that defines
# the symbol, the `have` that states its defining equation, and the
# statements of the steps that use it.
INTRODUCED_SYMBOL = re.compile(r"(?P<name>«_sF\d+»)(?P<arguments>(?: v\d+)*)")
# The `let` the emitter writes for one function-definition step. The step's
# own comment line carries no space after `step`, and it sits inside the
# `fullProof` body rather than at the top level, so it is not one of
# `split_steps`'s blocks.
DEFINITION_LET = re.compile(
    r"^\s*let (?P<name>«_sF\d+»)(?P<arguments>(?: v\d+)*)\s*:="
)


def normalize(text: str) -> list[str]:
    """Drop run-volatile lines and canonicalize the `variable` telescope.

    The emitter orders the section-variable telescope by an allocation-
    dependent traversal, so identical runs can group and order the same
    declarations differently. Every declaration is kept, one per line,
    sorted by name, so the telescope compares as a set.
    """
    lines = [
        line for line in text.splitlines()
        if not line.startswith(VOLATILE_PREFIXES)
    ]
    result: list[str] = []
    telescope: list[str] = []
    index = 0
    while index < len(lines):
        match = TELESCOPE_GROUP.match(lines[index])
        if match is None:
            if telescope:
                result.extend(sorted(telescope))
                telescope = []
            result.append(lines[index])
        else:
            kind = match.group("type").strip()
            for name in match.group("names").split():
                telescope.append(f"variable {{{name} : {kind}}}")
        index += 1
    result.extend(sorted(telescope))
    return result


def split_steps(lines: list[str]) -> list[tuple[str, list[str]]]:
    """Group output lines into the preamble and one block per proof step."""
    blocks: list[tuple[str, list[str]]] = [("preamble", [])]
    for line in lines:
        match = STEP_HEADER.match(line)
        if match is not None:
            blocks.append((f"step {match.group(1)} {match.group(2)}", []))
        blocks[-1][1].append(line)
    return blocks


# ------------------------------------------------------------
# Defect signatures
# ------------------------------------------------------------


def rectify_defect_present(lines: list[str]) -> bool:
    """A `rectify` helper binds a variable that has no name in scope."""
    return any(
        name.endswith(" rectify") and any(DEFECT_TOKEN.search(l) for l in body)
        for name, body in split_steps(lines)
    )


def declared_symbol_arities(lines: list[str]) -> dict[str, int]:
    """Arity of every introduced definition symbol, read off the telescope."""
    arities: dict[str, int] = {}
    for line in lines:
        match = TELESCOPE_LINE.match(line)
        if match is None:
            continue
        name = match.group("name")
        if INTRODUCED_SYMBOL.fullmatch(name) is None:
            continue
        arities[name] = match.group("type").count("→")
    return arities


def symbol_arity_disagreements(lines: list[str]) -> list[str]:
    """Sites that use an introduced symbol at other than its declared arity.

    The emitter declares each `_sF` symbol in the section-variable telescope
    with the arity Vampire's signature gives it, then writes the `let` that
    defines it, the equation that states the definition, and every later
    use. A site applying the symbol to a different number of arguments than
    the declaration states cannot elaborate; that disagreement is the defect
    this signature detects.
    """
    declared = declared_symbol_arities(lines)
    if not declared:
        return []
    disagreements: list[str] = []
    for line in lines:
        if TELESCOPE_LINE.match(line) is not None:
            continue
        for match in INTRODUCED_SYMBOL.finditer(line):
            name = match.group("name")
            if name not in declared:
                continue
            used = len(match.group("arguments").split())
            if used != declared[name]:
                disagreements.append(
                    f"{name} is declared with arity {declared[name]} "
                    f"and used with {used}"
                )
    return disagreements


def introduced_symbol_arity_defect_present(lines: list[str]) -> bool:
    return bool(symbol_arity_disagreements(lines))


DEFECTS = {
    "rectify_default_binder": rectify_defect_present,
    "introduced_symbol_arity": introduced_symbol_arity_defect_present,
}


def parameterised_definition_sites(lines: list[str]) -> list[str]:
    """`let` sites that define an introduced symbol taking parameters.

    A ground twee definition introduces a constant and exercises none of
    the binder handling; only a site with at least one parameter pins the
    agreement between the declared arity, the `let` binders, and the uses.
    """
    declared = declared_symbol_arities(lines)
    sites: list[str] = []
    for line in lines:
        match = DEFINITION_LET.match(line)
        if match is None:
            continue
        name = match.group("name")
        if declared.get(name, 0) > 0:
            sites.append(name)
    return sites


def only_named_steps_differ(
    unpatched: list[str], patched: list[str], suffix: str
) -> tuple[bool, str]:
    before = split_steps(unpatched)
    after = split_steps(patched)
    before_names = [name for name, _ in before]
    after_names = [name for name, _ in after]
    if before_names != after_names:
        return False, "step headers differ between uncorrected and corrected output"

    def without_version(body: list[str]) -> list[str]:
        return [line for line in body if not line.startswith(VERSION_PREFIX)]

    differing = [
        name for (name, body_before), (_, body_after) in zip(before, after)
        if without_version(body_before) != without_version(body_after)
    ]
    if not differing:
        return False, "uncorrected and corrected outputs are identical"
    offenders = [name for name in differing if not name.endswith(suffix)]
    if offenders:
        return False, "unexpected differing steps: " + ", ".join(offenders)
    return True, f"only{suffix} steps differ: " + ", ".join(differing)


# ------------------------------------------------------------
# Fixture families
# ------------------------------------------------------------


def load_family(
    directory: Path, locked_patch_paths: set[str]
) -> dict[str, object]:
    """Read and validate one fixture family's descriptor."""
    path = directory / FAMILY_FILENAME
    try:
        family = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise LeancheckPinError(
            f"{directory.name}: bad {FAMILY_FILENAME}: {error}"
        )
    if not isinstance(family, dict):
        raise LeancheckPinError(
            f"{directory.name}: {FAMILY_FILENAME} is not an object"
        )
    defect = family.get("defect")
    if defect not in DEFECTS:
        raise LeancheckPinError(f"{directory.name}: unknown defect {defect!r}")
    patch = family.get("patch")
    if not isinstance(patch, str) or patch not in locked_patch_paths:
        raise LeancheckPinError(
            f"{directory.name}: patch {patch!r} is not in the locked series"
        )
    fragment = family.get("uncorrected_error_contains")
    if not isinstance(fragment, str) or not fragment:
        raise LeancheckPinError(
            f"{directory.name}: uncorrected_error_contains must be a "
            "nonempty string"
        )
    suffix = family.get("differing_steps_suffix")
    if suffix is not None and (not isinstance(suffix, str) or not suffix):
        raise LeancheckPinError(
            f"{directory.name}: differing_steps_suffix must be a nonempty string"
        )
    minimum = family.get("minimum_parameterised_definitions", 0)
    if not isinstance(minimum, int) or isinstance(minimum, bool) or minimum < 0:
        raise LeancheckPinError(
            f"{directory.name}: minimum_parameterised_definitions must be a count"
        )
    return {
        "name": directory.name,
        "defect": defect,
        "patch": patch,
        "uncorrected_error_contains": fragment,
        "differing_steps_suffix": suffix,
        "minimum_parameterised_definitions": minimum,
    }


def package_for_elaboration(raw: str) -> str:
    lines = raw.splitlines(keepends=True)
    for index, line in enumerate(lines):
        if line.rstrip("\n") == IMPORT_LINE:
            lines[index] = PACKAGING_HEADER
            return "".join(lines)
    raise LeancheckPinError("raw leancheck output has no `import VampLean` line")


def elaborate(repository: Path, module: Path) -> tuple[int, str]:
    completed = subprocess.run(
        ["lake", "env", "lean", str(module)],
        cwd=repository,
        text=True,
        capture_output=True,
        timeout=1800.0,
        check=False,
    )
    return completed.returncode, completed.stdout + completed.stderr


def run_case(
    repository: Path,
    binary: Path,
    case: Path,
    family: dict[str, object],
    *,
    elaborate_outputs: bool,
    workdir: Path,
) -> tuple[list[Check], dict[str, object]]:
    checks: list[Check] = []
    label = f"{family['name']}/{case.name}"
    receipt: dict[str, object] = {"family": family["name"], "case": case.name}
    defect_present = DEFECTS[str(family["defect"])]
    try:
        arguments = json.loads(
            (case / "arguments.json").read_text(encoding="utf-8")
        )["arguments"]
    except (OSError, KeyError, ValueError) as error:
        raise LeancheckPinError(f"{label}: bad arguments.json: {error}")
    if not isinstance(arguments, list) or not all(
        isinstance(item, str) for item in arguments
    ):
        raise LeancheckPinError(f"{label}: arguments must be strings")
    unpatched = (case / "unpatched.lean").read_text(encoding="utf-8")
    patched = (case / "patched.lean").read_text(encoding="utf-8")
    receipt["arguments"] = arguments
    completed = subprocess.run(
        [str(binary), *arguments],
        cwd=case,
        text=True,
        capture_output=True,
        timeout=600.0,
        check=False,
    )
    receipt["exit_status"] = completed.returncode
    checks.append(Check(
        f"{label}:solver_exit",
        completed.returncode == 0,
        f"pinned Vampire exited with status {completed.returncode}",
    ))
    fresh = normalize(completed.stdout)
    expected = normalize(patched)
    same = fresh == expected
    checks.append(Check(
        f"{label}:corrected_output",
        same,
        "fresh output equals the preserved corrected output"
        if same else "fresh output differs from the preserved corrected output",
    ))
    if not same:
        (workdir / f"{family['name']}.{case.name}.fresh.lean").write_text(
            completed.stdout, encoding="utf-8"
        )
    unpatched_lines = normalize(unpatched)
    checks.append(Check(
        f"{label}:uncorrected_defect",
        defect_present(unpatched_lines),
        f"uncorrected output carries the {family['defect']} defect",
    ))
    checks.append(Check(
        f"{label}:corrected_clean",
        not defect_present(expected),
        f"corrected output is free of the {family['defect']} defect",
    ))
    suffix = family["differing_steps_suffix"]
    if isinstance(suffix, str):
        ok, detail = only_named_steps_differ(unpatched_lines, expected, suffix)
        checks.append(Check(f"{label}:step_scope", ok, detail))
    receipt["parameterised_definitions"] = len(
        parameterised_definition_sites(expected)
    )
    if elaborate_outputs:
        for kind, raw, expect_success in (
            ("corrected", patched, True),
            ("uncorrected", unpatched, False),
        ):
            stem = f"{family['name']}_{case.name}_{kind}".replace("-", "_")
            module = workdir / f"Leancheck_{stem}.lean"
            module.write_text(package_for_elaboration(raw), encoding="utf-8")
            status, output = elaborate(repository, module)
            errors = [line for line in output.splitlines() if ": error" in line]
            succeeded = status == 0 and not errors
            if expect_success:
                checks.append(Check(
                    f"{label}:{kind}_elaborates",
                    succeeded,
                    "corrected output elaborates with the pinned VampLean"
                    if succeeded else
                    "corrected output failed to elaborate: "
                    + "; ".join(errors[:3]),
                ))
            else:
                fragment = str(family["uncorrected_error_contains"])
                stated = any(fragment in line for line in errors)
                checks.append(Check(
                    f"{label}:{kind}_fails",
                    not succeeded and stated,
                    f"uncorrected output fails with {fragment!r}"
                    if not succeeded and stated else
                    f"uncorrected output did not fail with {fragment!r}",
                ))
            receipt[f"{kind}_elaboration_status"] = status
            receipt[f"{kind}_elaboration_errors"] = errors[:8]
    return checks, receipt


def run(
    repository: Path,
    *,
    binary: Path | None,
    elaborate_outputs: bool,
) -> dict[str, object]:
    lock = load_lock(repository)
    role = leancheck_role(lock)
    identity = probe(repository, binary=binary)
    checks = [Check(**check) for check in identity["checks"]]
    fixtures = repository_path(
        repository, str(role["regression"]["fixtures"]), label="fixtures"
    )
    families = sorted(
        path for path in fixtures.iterdir()
        if path.is_dir() and (path / FAMILY_FILENAME).is_file()
    )
    if not families:
        raise LeancheckPinError(f"no fixture families under {fixtures}")
    locked_patch_paths = {str(patch["path"]) for patch in locked_patches(role)}
    descriptors = [
        load_family(directory, locked_patch_paths) for directory in families
    ]
    covered = {str(descriptor["patch"]) for descriptor in descriptors}
    missing = sorted(locked_patch_paths - covered)
    checks.append(Check(
        "patch_coverage",
        not missing,
        "every locked patch has a fixture family" if not missing
        else "no fixture family covers " + ", ".join(missing),
    ))
    receipts: list[dict[str, object]] = []
    resolved = binary if binary is not None else locked_binary_path(repository, role)
    if identity["ok"]:
        with tempfile.TemporaryDirectory(prefix="leancheck-check-") as tmp:
            for directory, descriptor in zip(families, descriptors):
                cases = sorted(
                    path for path in directory.iterdir() if path.is_dir()
                )
                if not cases:
                    raise LeancheckPinError(f"no fixture cases under {directory}")
                parameterised = 0
                for case in cases:
                    case_checks, receipt = run_case(
                        repository, resolved, case, descriptor,
                        elaborate_outputs=elaborate_outputs,
                        workdir=Path(tmp),
                    )
                    checks.extend(case_checks)
                    receipts.append(receipt)
                    parameterised += int(receipt["parameterised_definitions"])
                minimum = int(descriptor["minimum_parameterised_definitions"])
                if minimum:
                    checks.append(Check(
                        f"{descriptor['name']}:parameterised_definitions",
                        parameterised >= minimum,
                        f"the family's corrected outputs define {parameterised} "
                        "introduced symbol(s) with parameters "
                        f"(at least {minimum} required)",
                    ))
    return {
        "identity": {
            key: value for key, value in identity.items() if key != "checks"
        },
        "cases": receipts,
        "checks": [check.to_json() for check in checks],
        "ok": all(check.ok for check in checks) and identity["ok"],
    }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--binary", type=Path, default=None,
        help="check this binary instead of the locked path",
    )
    parser.add_argument(
        "--no-elaborate", action="store_true",
        help="skip Lean elaboration of the preserved outputs",
    )
    parser.add_argument("--json", action="store_true", help="emit JSON")
    return parser


def main() -> int:
    arguments = _parser().parse_args()
    try:
        report = run(
            REPO,
            binary=arguments.binary,
            elaborate_outputs=not arguments.no_elaborate,
        )
    except (LeancheckPinError, OSError, subprocess.TimeoutExpired) as error:
        if arguments.json:
            print(json.dumps({"ok": False, "error": str(error)}, indent=2))
        else:
            print(f"error: {error}", file=sys.stderr)
        return 1
    if arguments.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        for check in report["checks"]:
            status = "ok" if check["ok"] else "FAIL"
            print(f"{status} {check['name']}: {check['detail']}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
