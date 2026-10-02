"""Fail-closed identity checks for the pinned leancheck Vampire."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

import pytest

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))

import build_leancheck_vampire  # noqa: E402
import check_leancheck_emitter  # noqa: E402
from leancheck_toolchain import (  # noqa: E402
    LeancheckPinError,
    check_patch,
    leancheck_role,
    load_lock,
    probe,
)


FIXTURES = REPO / "toolchain/leancheck-vampire/fixtures"
RECTIFY = FIXTURES / "rectify-retained-binders"
ARITY = FIXTURES / "definition-symbol-arity"


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _fake_binary(path: Path, version: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "#!/bin/sh\n"
        "if [ \"$1\" = \"--version\" ]; then "
        f"printf '%s\\n' '{version}' 'CaDiCaL: cadical-2.1.3'; "
        "else exit 2; fi\n",
        encoding="utf-8",
    )
    path.chmod(0o755)
    return path


def _fake_repository(tmp_path: Path, *, patch_bytes: bytes | None = None):
    """Copy the real lock and the whole patch series into a scratch repository.

    ``patch_bytes`` replaces the last patch of the series, which is the one
    whose commit the built binary's version names.
    """
    lock = json.loads((REPO / "toolchain.lock.json").read_text("utf-8"))
    role = lock["roles"]["leancheck_vampire"]
    for position, patch in enumerate(role["patches"]):
        patch_relative = patch["path"]
        source = (REPO / patch_relative).read_bytes()
        target = tmp_path / patch_relative
        target.parent.mkdir(parents=True, exist_ok=True)
        last = position == len(role["patches"]) - 1
        target.write_bytes(
            patch_bytes if patch_bytes is not None and last else source
        )
    return lock, role


def _write_lock(tmp_path: Path, lock: dict) -> None:
    (tmp_path / "toolchain.lock.json").write_text(
        json.dumps(lock, indent=2) + "\n", encoding="utf-8"
    )


def test_real_lock_and_patch_series_are_self_consistent() -> None:
    lock = load_lock(REPO)
    role = leancheck_role(lock)
    assert all(check.ok for check in check_patch(REPO, role))
    patches = role["patches"]
    assert [Path(patch["path"]).name for patch in patches] == [
        "0001-leancheck-rectify-retained-binders.patch",
        "0002-leancheck-definition-symbol-arity.patch",
    ]
    for patch in patches:
        patch_text = (REPO / patch["path"]).read_text("utf-8")
        for relative in patch["files"]:
            assert relative in patch_text
        assert patch["commit"]["sha"].startswith(patch["commit"]["version_commit"])
    # Each patch of the series states the tree the previous one leaves, so
    # the series is only applicable in the order the lock records it.
    first, second = patches
    shared = set(first["files"]) & set(second["files"])
    assert shared == {"Shell/LeanChecker/LeanChecker.cpp"}
    for relative in shared:
        assert (
            first["files"][relative]["after_sha256"]
            == second["files"][relative]["before_sha256"]
        )
    # The built binary's version names the last commit of the series.
    assert f"commit {patches[-1]['commit']['version_commit']}" in role[
        "version_contains"
    ]


def test_a_series_recorded_out_of_order_is_refused(tmp_path: Path) -> None:
    lock, role = _fake_repository(tmp_path)
    role["patches"] = list(reversed(role["patches"]))
    _write_lock(tmp_path, lock)
    with pytest.raises(LeancheckPinError, match="does not leave behind"):
        leancheck_role(load_lock(tmp_path))


def test_a_role_with_no_patch_series_is_refused(tmp_path: Path) -> None:
    lock, role = _fake_repository(tmp_path)
    role.pop("patches")
    _write_lock(tmp_path, lock)
    with pytest.raises(LeancheckPinError):
        leancheck_role(load_lock(tmp_path))


def test_probe_accepts_a_consistent_fake_binary(tmp_path: Path) -> None:
    lock, role = _fake_repository(tmp_path)
    binary = _fake_binary(
        tmp_path / "vampire",
        f"Vampire 5.0.1 (Release build, commit "
        f"{role['patches'][-1]['commit']['version_commit']} on date)",
    )
    role["sha256"] = {"Test-arch": _sha256(binary.read_bytes())}
    _write_lock(tmp_path, lock)
    identity = probe(tmp_path, binary=binary, platform_key="Test-arch")
    assert identity["ok"], identity["checks"]


@pytest.mark.parametrize(
    "tamper",
    ["binary_digest", "applied_commit", "patch_bytes", "platform"],
)
def test_probe_fails_closed(tmp_path: Path, tamper: str) -> None:
    patch_bytes = None
    if tamper == "patch_bytes":
        patch_bytes = (REPO / "toolchain/leancheck-vampire/patches"
                       / "0002-leancheck-definition-symbol-arity.patch"
                       ).read_bytes() + b"\n"
    lock, role = _fake_repository(tmp_path, patch_bytes=patch_bytes)
    version_commit = role["patches"][-1]["commit"]["version_commit"]
    binary = _fake_binary(
        tmp_path / "vampire",
        f"Vampire 5.0.1 (Release build, commit {version_commit} on date)",
    )
    digest = _sha256(binary.read_bytes())
    platform_key = "Test-arch"
    role["sha256"] = {platform_key: digest}
    if tamper == "binary_digest":
        role["sha256"] = {platform_key: "0" * 64}
    elif tamper == "applied_commit":
        role["patches"][-1]["commit"]["sha"] = "f" * 40
    elif tamper == "platform":
        platform_key = "Other-arch"
    _write_lock(tmp_path, lock)
    identity = probe(tmp_path, binary=binary, platform_key=platform_key)
    assert not identity["ok"]
    failed = {check["name"] for check in identity["checks"] if not check["ok"]}
    expected = {
        "binary_digest": "binary_sha256",
        "applied_commit": "version_commit",
        "patch_bytes": "patch_file_1",
        "platform": "platform",
    }[tamper]
    assert expected in failed


def test_unsupported_lock_format_fails_closed(tmp_path: Path) -> None:
    lock, _ = _fake_repository(tmp_path)
    lock["format_version"] = 1
    _write_lock(tmp_path, lock)
    with pytest.raises(LeancheckPinError):
        load_lock(tmp_path)


def test_build_rejects_a_tampered_patch_before_fetching(tmp_path: Path) -> None:
    lock, _ = _fake_repository(tmp_path, patch_bytes=b"not the patch\n")
    _write_lock(tmp_path, lock)
    destination = tmp_path / "checkout"
    with pytest.raises(LeancheckPinError, match="patch SHA-256"):
        build_leancheck_vampire.build(
            tmp_path, destination=destination, jobs=1, force=False,
            bootstrap=False,
        )
    assert not destination.exists()


def test_build_refuses_to_overwrite_without_force(tmp_path: Path) -> None:
    lock, _ = _fake_repository(tmp_path)
    _write_lock(tmp_path, lock)
    destination = tmp_path / "checkout"
    destination.mkdir()
    with pytest.raises(LeancheckPinError, match="--force"):
        build_leancheck_vampire.build(
            tmp_path, destination=destination, jobs=1, force=False,
            bootstrap=False,
        )


def _cases(family: Path) -> list[str]:
    return sorted(path.name for path in family.iterdir() if path.is_dir())


@pytest.mark.parametrize("case", _cases(RECTIFY))
def test_preserved_rectify_outputs_differ_only_in_rectify_steps(case: str) -> None:
    unpatched = check_leancheck_emitter.normalize(
        (RECTIFY / case / "unpatched.lean").read_text("utf-8")
    )
    patched = check_leancheck_emitter.normalize(
        (RECTIFY / case / "patched.lean").read_text("utf-8")
    )
    assert check_leancheck_emitter.rectify_defect_present(unpatched)
    assert not check_leancheck_emitter.rectify_defect_present(patched)
    ok, detail = check_leancheck_emitter.only_named_steps_differ(
        unpatched, patched, " rectify"
    )
    assert ok, detail


@pytest.mark.parametrize("case", _cases(ARITY))
def test_preserved_arity_outputs_agree_on_every_introduced_symbol(case: str) -> None:
    unpatched = check_leancheck_emitter.normalize(
        (ARITY / case / "unpatched.lean").read_text("utf-8")
    )
    patched = check_leancheck_emitter.normalize(
        (ARITY / case / "patched.lean").read_text("utf-8")
    )
    assert check_leancheck_emitter.symbol_arity_disagreements(unpatched)
    assert check_leancheck_emitter.symbol_arity_disagreements(patched) == []


def test_the_arity_family_exercises_a_parameterised_definition() -> None:
    sites = [
        site
        for case in _cases(ARITY)
        for site in check_leancheck_emitter.parameterised_definition_sites(
            check_leancheck_emitter.normalize(
                (ARITY / case / "patched.lean").read_text("utf-8")
            )
        )
    ]
    assert sites, "no corrected output defines an introduced symbol with parameters"


def test_the_arity_family_exercises_an_unsorted_binder_list() -> None:
    """Some corrected `let` binds its parameters in non-ascending index order.

    The emitter reads a definition's binders off the introduced symbol's
    own application, and must emit them in that order. `outputVariables`
    sorts by variable index unless told not to, and a family whose every
    definition happens to be already ascending cannot tell the two apart.
    `probe-two-parameter-order` is the case that can.
    """
    unsorted: list[list[str]] = []
    for case in _cases(ARITY):
        lines = check_leancheck_emitter.normalize(
            (ARITY / case / "patched.lean").read_text("utf-8")
        )
        for line in lines:
            match = check_leancheck_emitter.DEFINITION_LET.match(line)
            if match is None:
                continue
            binders = match.group("arguments").split()
            if binders != sorted(binders):
                unsorted.append(binders)
    assert unsorted, (
        "no corrected output binds a definition's parameters in an order "
        "that sorting by variable index would change"
    )


@pytest.mark.parametrize(
    "family,case",
    [(RECTIFY, case) for case in _cases(RECTIFY)]
    + [(ARITY, case) for case in _cases(ARITY)],
)
def test_every_fixture_case_pins_its_own_arguments(family: Path, case: str) -> None:
    arguments = json.loads(
        (family / case / "arguments.json").read_text("utf-8")
    )["arguments"]
    assert arguments[:2] == ["--proof", "leancheck"]
    assert arguments[-1] == "problem.p"
    # Every case pins the preprocessing whose emitted proof it is about,
    # either by running the whole `casc_2025` schedule that turns it on or
    # by naming the option directly on a single strategy.
    assert "casc_2025" in arguments or "--twee_goal_transformation" in arguments


@pytest.mark.parametrize("family", [RECTIFY, ARITY])
def test_every_family_names_a_locked_patch(family: Path) -> None:
    role = leancheck_role(load_lock(REPO))
    locked = {str(patch["path"]) for patch in role["patches"]}
    descriptor = check_leancheck_emitter.load_family(family, locked)
    assert descriptor["defect"] in check_leancheck_emitter.DEFECTS
    assert descriptor["patch"] in locked


def test_packaging_replaces_only_the_import_line() -> None:
    raw = "-- header\nimport VampLean\nsection vamproof\ntheorem t : True := trivial\n"
    packaged = check_leancheck_emitter.package_for_elaboration(raw)
    assert packaged.startswith(
        "-- header\nimport VampLean\n"
        "import Mathlib.Tactic.Linter.UnusedTactic\nopen VampLean\n"
    )
    assert packaged.endswith("section vamproof\ntheorem t : True := trivial\n")
    with pytest.raises(LeancheckPinError):
        check_leancheck_emitter.package_for_elaboration("theorem t : True := trivial\n")
