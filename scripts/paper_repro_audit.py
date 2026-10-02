#!/usr/bin/env python3
"""Paper-specific reproduction audit of saved Direct Lean checker receipts.

This reads records only: it never runs Lean, rechecks a proof, authenticates a
receipt, or changes the shipped verifier's acceptance policy. ``std3`` means a
subset of propext, Classical.choice and Quot.sound. The shipped checker audits
the answer AND every native assertion declared in the candidate, including
unused helpers; a native entry need not be a dependency of the answer itself.
``native_kernel_rechecked`` is a subset checked by kernel-reduction fallback,
not removal of those original axioms or a std3-only audit of the submission.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.paper_repro_common import ROOT, STD3, ReproError, output_directory

CLASSIFICATIONS = (
    "accepted_std3_only",
    "accepted_native_assertions",
    "unexpected_accepted_axioms",
    "rejected",
    "missing_or_inconsistent_evidence",
)
PROBLEMS = {"unexpected_accepted_axioms", "missing_or_inconsistent_evidence"}


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result = {}
    for name, value in pairs:
        _require(name not in result, "duplicate JSON fields")
        result[name] = value
    return result


def _invalid_number(_value: str) -> None:
    raise ValueError("nonfinite JSON number")


def _read_object(path: Path) -> dict[str, Any]:
    # Do not echo file contents, exception text or credentials from raw records.
    try:
        value = json.loads(path.read_text(encoding="utf-8"),
                           object_pairs_hook=_object_pairs,
                           parse_constant=_invalid_number)
    except (OSError, ValueError, UnicodeError) as error:
        raise ValueError("required file is missing, unreadable, or invalid JSON") from error
    _require(isinstance(value, dict), "JSON object required")
    return value


def _names(receipt: dict[str, Any], field: str) -> set[str]:
    value = receipt.get(field)
    _require(isinstance(value, list) and
             all(isinstance(name, str) and name for name in value),
             "missing or malformed " + field)
    _require(len(value) == len(set(value)), "duplicate names in " + field)
    return set(value)


def _case_row(root: Path, case: str) -> dict[str, Any]:
    axioms: set[str] = set()
    native: set[str] = set()
    kernel: set[str] = set()
    classification, detail = "missing_or_inconsistent_evidence", ""
    try:
        directory = root / "cases" / case
        outer = _read_object(directory / "result.json")
        receipt = _read_object(directory / "check" / "result.json")
        # JSON serialization distinguishes true from 1, unlike Python equality.
        _require(json.dumps(outer.get("check"), sort_keys=True) ==
                 json.dumps(receipt, sort_keys=True), "checker receipt copies disagree")
        _require(type(receipt.get("schema_version")) is int and
                 receipt["schema_version"] == 1 and receipt.get("case") == case,
                 "unsupported schema or wrong case")
        accepted = receipt.get("proof_checked")
        _require(type(accepted) is bool and type(outer.get("proof_checked")) is bool and
                 outer["proof_checked"] == accepted and
                 outer.get("status") == receipt.get("status"),
                 "acceptance flags or statuses disagree")
        try:
            response_hash = hashlib.sha256((directory / "response.json").read_bytes()).hexdigest()
        except OSError as error:
            raise ValueError("saved response is missing or unreadable") from error
        _require(receipt.get("response_sha256") == response_hash,
                 "saved response hash mismatch")
        if not accepted:
            _require(receipt.get("status") in
                     {"check_failed", "check_timeout", "task_setup_failed"} and
                     receipt.get("failure_stage") in {"task", "compile", "audit"},
                     "malformed rejection status")
            classification = "rejected"
            detail = receipt["status"] + ":" + receipt["failure_stage"]
        else:
            _require(receipt.get("verdict") in {"valid", "invalid"} and
                     receipt.get("status") == receipt["verdict"] + "_proof_checked" and
                     receipt.get("failure_stage", "missing") is None,
                     "malformed acceptance status")
            axioms = _names(receipt, "axioms")
            native = _names(receipt, "native_rechecked")
            kernel = _names(receipt, "native_kernel_rechecked")
            if axioms - STD3 != native or not kernel <= native or any(
                    "_native" not in name.split(".") for name in native):
                classification = "unexpected_accepted_axioms"
                detail = "axiom/native fields violate the shipped audit policy"
            else:
                classification = ("accepted_native_assertions" if native
                                  else "accepted_std3_only")
    except ValueError as error:
        detail = str(error)
    except TypeError:
        detail = "receipt fields have incorrect types"
    return {"case": case, "classification": classification,
            "axioms": sorted(axioms), "native_assertions": sorted(native),
            "kernel_fallback": sorted(kernel), "detail": detail}


def audit_run(path: Path) -> dict[str, Any]:
    """Classify every case declared by a saved Direct Lean campaign's run.json.

    ``complete`` means no missing/inconsistent evidence or unexpected accepted
    axiom fields were found. Rejected checker receipts are ordinary outcomes,
    not issues. An invalid case list produces a run-level issue and no inferred
    case inventory. The result contains only IDs, axiom names and fixed messages;
    raw records, model output, authentication information and paths are omitted.
    """
    result: dict[str, Any] = {
        "schema_version": 1, "complete": False,
        "counts": {name: 0 for name in CLASSIFICATIONS}, "cases": [], "issues": [],
    }
    try:
        cases = _read_object(Path(path) / "run.json").get("cases")
        _require(isinstance(cases, list) and bool(cases) and
                 all(isinstance(case, str) and re.fullmatch(r"Example[0-9]{4}", case)
                     for case in cases), "missing or malformed case list")
        _require(len(cases) == len(set(cases)), "duplicate case IDs")
    except ValueError as error:
        result["issues"].append({"case": None, "detail": str(error)})
        return result
    for case in cases:
        row = _case_row(Path(path), case)
        result["cases"].append(row)
        result["counts"][row["classification"]] += 1
        if row["classification"] in PROBLEMS:
            result["issues"].append({"case": case, "detail": row["detail"]})
    result["complete"] = not result["issues"]
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run", type=Path, help="saved Direct Lean campaign directory")
    parser.add_argument("--output", help="new repository-relative JSON file under artifacts/")
    args = parser.parse_args(argv)
    result = audit_run(args.run)
    if args.output:
        try:
            destination = output_directory(ROOT, args.output)
            destination.parent.mkdir(parents=True, exist_ok=True)
            # Never overwrite a receipt, run manifest or previous audit report.
            with destination.open("x", encoding="utf-8") as stream:
                json.dump(result, stream, indent=2, sort_keys=True, allow_nan=False)
                stream.write("\n")
        except (OSError, ReproError):
            print("Cannot create audit JSON: use a new file under artifacts/.", file=sys.stderr)
            return 2
    print("Saved-receipt audit only; proofs were not independently rechecked.")
    for name, count in result["counts"].items():
        print(f"{name}: {count}")
    for issue in result["issues"]:
        print(f"{issue['case'] or 'run.json'}: {issue['detail']}", file=sys.stderr)
    return 0 if result["complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
