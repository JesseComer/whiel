#!/usr/bin/env python3
"""Emit and kernel-check a test-only flagged certificate in a fresh overlay.

Build the ordinary Lean test imports first. This driver never registers its
scratch adapter or writes into Benchmark. Every artifact and proof job comes
from the production bound worker; Vampire supplies the actual raw proofs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = "Whiel.Synthesis.Tests.FixedAmbientFlaggedFixture"
ID = "FlaggedEmissions"
AUDIT = Path("Whiel/Synthesis/Tests/FixedAmbientFlaggedCertificateAxiomAudit.lean")
STD3 = {"propext", "Classical.choice", "Quot.sound"}
# The repository's existing deterministic Direct profile, unchanged.
DIRECT = ["--proof", "leancheck", "--proof_extra", "lean",
          "--skolemization", "syntactic", "--output_mode", "lean",
          "--time_limit", "30", "--avatar", "on", "--random_seed", "1"]

ADAPTER = f'''import {FIXTURE}

namespace Whiel.Benchmark.{ID}

abbrev inputSchema := Synthesis.Tests.FixedAmbientFlaggedFixture.inputSchema
abbrev inputPre := Synthesis.Tests.FixedAmbientFlaggedFixture.inputPre
abbrev inputCmd := Synthesis.Tests.FixedAmbientFlaggedFixture.inputCmd
abbrev inputPost := Synthesis.Tests.FixedAmbientFlaggedFixture.inputPost
abbrev inputPreproc := Synthesis.Tests.FixedAmbientFlaggedFixture.inputPreproc

end Whiel.Benchmark.{ID}
'''


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def checked_path(root: Path, relative: str) -> Path:
    path = PurePosixPath(relative)
    if path.is_absolute() or not path.parts or any(p in (".", "..") for p in path.parts):
        raise ValueError(f"unsafe emitted path: {relative}")
    if path.parts[:2] != ("Benchmark", ID):
        raise ValueError(f"artifact escapes scratch adapter: {relative}")
    target = root.joinpath(*path.parts)
    target.parent.mkdir(parents=True, exist_ok=True)
    return target


def audit_source(output: str) -> str:
    theorem = f"Whiel.Benchmark.{ID}.Certificate.input_hoare_triple_valid"
    match = re.fullmatch(
        r"'" + re.escape(theorem) + r"' depends on axioms:\s*\[([^]]*)\]\s*", output
    )
    if match is None or {a.strip() for a in match[1].split(",")} != STD3:
        raise ValueError(f"emitted theorem does not have exact std3 axioms: {output}")
    return f'''-- Author: Jesse Comer
import Benchmark.{ID}.Certificate.Valid

/-
  Explicit scratch-overlay gate. The driver emits and builds
  its imported certificate before checking this file. It is
  intentionally outside the ordinary test aggregate.
-/

namespace Whiel.Synthesis.Tests.FixedAmbientFlaggedAudit

open FixedAmbientFlaggedFixture

/- The actual emitted theorem at the original fixture type. -/
example : HoareValid inputPre inputCmd inputPost :=
  Benchmark.{ID}.Certificate.input_hoare_triple_valid

end Whiel.Synthesis.Tests.FixedAmbientFlaggedAudit

/-- info: {output.strip()} -/
#guard_msgs (whitespace := lax) in
#print axioms
  {theorem}
'''


class Driver:
    def __init__(self, output: Path):
        self.output = output.resolve()
        if self.output == ROOT or ROOT in self.output.parents:
            raise ValueError("use a fresh output directory outside the source worktree")
        self.output.mkdir(parents=True, exist_ok=False)
        self.src = self.output / "src"
        self.olean = self.output / "olean"
        self.src.mkdir(); self.olean.mkdir()
        self.commands: list[dict] = []
        self.env = os.environ.copy()
        self.env["LEAN_NUM_THREADS"] = "2"
        self.lean = self.run("resolve-lean", ["lake", "env", "which", "lean"]).strip()
        lean_path = self.run("resolve-path", ["lake", "env", "printenv", "LEAN_PATH"]).strip()
        self.env["LEAN_PATH"] = str(self.olean) + os.pathsep + lean_path
        self.identity = {"canonical_id": ID, "module": f"Benchmark.{ID}.Input",
                         "namespace": f"Whiel.Benchmark.{ID}",
                         "source_sha256": digest(ADAPTER.encode())}
        self.scope = None
        self.calls = 0

    def run(self, name: str, command: list[str], *, timeout: int = 180) -> str:
        start = time.monotonic()
        process = subprocess.Popen(command, cwd=ROOT, env=self.env,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   start_new_session=True)
        timed_out = False
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
        result = subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
        (self.output / f"{name}.stdout").write_bytes(result.stdout)
        (self.output / f"{name}.stderr").write_bytes(result.stderr)
        self.commands.append({"name": name, "command": command, "cwd": str(ROOT),
                              "exit_code": result.returncode, "timed_out": timed_out,
                              "elapsed_seconds": round(time.monotonic() - start, 3),
                              "stdout_sha256": digest(result.stdout), "stderr_sha256": digest(result.stderr)})
        (self.output / "commands.json").write_text(json.dumps(self.commands, indent=2) + "\n")
        if result.returncode:
            raise RuntimeError(f"{name} failed ({result.returncode}); see {self.output}")
        return result.stdout.decode()

    def lean_file(self, name: str, path: Path, *, compile: bool = False) -> str:
        command = [str(ROOT / "scripts/watchdog.sh"), "4194304", self.lean,
                   f"--root={self.src}"]
        if compile:
            target = self.olean / path.relative_to(self.src).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            command += ["-o", str(target)]
        return self.run(name, command + [str(path)])

    def prepare(self) -> None:
        # Lean selects a package root before resolving its submodules. The
        # scratch Benchmark root therefore also exposes existing dependencies,
        # read-only, while only the new adapter directory receives output.
        benchmark = self.olean / "Benchmark"
        benchmark.mkdir()
        for path in (ROOT / ".lake/build/lib/lean/Benchmark").iterdir():
            if path.name == ID:
                raise ValueError("scratch adapter collides with a compiled benchmark")
            (benchmark / path.name).symlink_to(path, target_is_directory=path.is_dir())
        adapter = checked_path(self.src, f"Benchmark/{ID}/Input.lean")
        adapter.write_text(ADAPTER)
        self.lean_file("adapter", adapter, compile=True)
        bridge = self.src / "FlaggedBridge.lean"
        bridge.write_text(f'''import Benchmark.{ID}.Input
import Whiel.Synthesis.Runtime.FixedAmbientWorker

set_option linter.hashCommand false

namespace FlaggedBridge

open Whiel Whiel.Concrete Whiel.Synthesis
open Runtime Runtime.FixedAmbientRegistry

#guard !(supportedTaskIds.contains "{ID}")

private def identity : TaskIdentity where
  canonicalId := "{ID}"
  moduleName := "Benchmark.{ID}.Input"
  namespaceName := "Whiel.Benchmark.{ID}"
  sourceSha256 := "{self.identity['source_sha256']}"
  semanticVersion := 1
  encodingVersion := 1

private def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.{ID}.inputPre,
    Whiel.Benchmark.{ID}.inputCmd,
    Whiel.Benchmark.{ID}.inputPost,
    Whiel.Benchmark.{ID}.inputPreproc

instance : FixedAmbientWorker.Bound :=
  ⟨Entry.ofInput identity manifest
    Whiel.Benchmark.{ID}.inputPreproc⟩

/- Use the real bound worker, never the registry router. -/
def invoke (request : Lean.Json) : Lean.Json :=
  let operation :=
    (request.getObjValAs? String "operation").toOption.getD ""
  let payload := request.getObjValD "payload"
  (FixedAmbientWorker.dispatchBound {{}}
    (FixedAmbientWorker.Request.forOperation 1 0
      operation payload)).response

end FlaggedBridge
''')
        self.lean_file("bridge", bridge, compile=True)

    def request(self, operation: str, payload: dict) -> dict:
        self.calls += 1
        name = f"request-{self.calls}-{operation}"
        request = self.output / f"{name}.json"
        request.write_text(json.dumps({"operation": operation, "payload": payload}))
        source = self.src / "Invoke.lean"
        source.write_text(f'''import FlaggedBridge

#eval do
  let text ← IO.FS.readFile {json.dumps(str(request))}
  let request ← IO.ofExcept (Lean.Json.parse text)
  IO.println (FlaggedBridge.invoke request).compress
''')
        response = json.loads(self.lean_file(name, source))
        if response.get("status") != "ok":
            raise ValueError(f"worker {operation} failed: {response}")
        if response["task_identity"] != self.identity:
            raise ValueError("worker input identity drift")
        if self.scope is not None and response["scope_identity"] != self.scope:
            raise ValueError("worker scope drift")
        return response["payload"]

    def describe(self) -> dict:
        description = self.request("describe", {})
        self.scope = description["scope_identity"]
        assert description["task_identity"] == self.identity
        assert description["manifest"]["identity"] == self.identity
        for field, value in self.identity.items():
            key = {"canonical_id": "task_canonical_id", "module": "task_module",
                   "namespace": "task_namespace", "source_sha256": "task_source_sha256"}[field]
            assert self.scope[key] == value, key
        relations = description["relation_table"]
        keys = [r["key"] for r in relations]
        assert len(keys) == len(set(keys))
        # Both actual control flags and their body-assigned prophecy copies.
        flag_keys = {f"{copy}:f::{flag}" for copy in ("o", "y") for flag in (0, 1)}
        assert flag_keys <= set(keys), keys
        assert all(r["arity"] == 0 for r in relations if r["key"] in flag_keys)
        assert self.scope["ambient_scope"][1] == [[r["key"], r["arity"]] for r in relations]
        bindings = description["prophecy_bindings"]
        assert self.scope["ambient_scope"][2] == [
            [b["program_key"], b["prophecy_key"], b["arity"]] for b in bindings]
        for flag in (0, 1):
            assert {"program_key": f"o:f::{flag}", "prophecy_key": f"y:f::{flag}", "arity": 0} in bindings
        (self.output / "description.json").write_text(json.dumps(description, indent=2) + "\n")
        return description

    def emit(self) -> dict:
        admission = self.request("admit_clauses", {"clause_text_bytes": None, "clauses": ["true"]})
        assert admission["outcome"] == "accepted"
        clause = admission["clauses"][0]["clause"]
        assert clause["source"] == "true" and clause["minimum_level"] == 0
        snapshot = {"rows": [{"clause_id": 1, "level": 0,
                               "canonical_source": clause["source"], "identity": clause["identity"]}]}
        bundle = self.request("emit_certificate", {"snapshot": snapshot})
        assert bundle == self.request("emit_certificate", {"snapshot": snapshot})
        assert bundle["input_source_sha256"] == self.identity["source_sha256"]
        assert bundle["scope_identity"] == self.scope
        assert [j["id"] for j in bundle["jobs"]] == ["init_clause_0", "maint_clause_0", "term_check"]
        assert [j["role"] for j in bundle["jobs"]] == ["initialization", "maintenance", "termination"]
        paths = set()
        for artifact in bundle["artifacts"]:
            relative = artifact["relative_path"]
            assert relative not in paths; paths.add(relative)
            assert digest(artifact["contents"].encode()) == artifact["contents_sha256"]
            checked_path(self.src, relative).write_text(artifact["contents"])
        proposal = (self.src / f"Benchmark/{ID}/Certificate/Proposal.lean").read_text()
        assert "Hoare.LoopTriple Data inputPreproc.outSchema" in proposal
        assert "Hoare.LoopTriple Data inputSchema" not in proposal
        (self.output / "bundle.json").write_text(json.dumps(bundle, indent=2) + "\n")
        return bundle

    def proofs(self, bundle: dict) -> None:
        lock = json.loads((ROOT / "toolchain.lock.json").read_text())
        assert lock["format_version"] == 3
        role = lock["roles"]["leancheck_vampire"]
        binary = ROOT / role["path"]
        platform_key = platform.system() + "-" + platform.machine()
        assert digest(binary.read_bytes()) == role["sha256"][platform_key]
        for job in bundle["jobs"]:
            problem = checked_path(self.src, job["problem_relative_path"])
            assert digest(problem.read_bytes()) == job["problem_sha256"]
            raw = self.run(job["id"] + "-vampire", [str(binary), *DIRECT, str(problem)], timeout=45)
            lines = raw.splitlines()
            theorem_line = next(i for i, line in enumerate(lines)
                                if line.lstrip().startswith("theorem fullProof"))
            assert "end vamproof" in lines[theorem_line + 1:]
            checked_path(self.src, job["leancheck_output_relative_path"]).write_text(raw)
            packaged = self.request("package_proof", {"extra_imports": [], "job_id": job["id"],
                                     "proof_namespace": job["proof_namespace"], "raw_output": raw})
            assert digest(packaged["packaged"].encode()) == packaged["packaged_sha256"]
            checked_path(self.src, job["proof_module_relative_path"]).write_text(packaged["packaged"])

    def compile_emitted(self) -> None:
        pending = {p.relative_to(self.src).with_suffix("").as_posix().replace("/", "."): p
                   for p in (self.src / f"Benchmark/{ID}/Certificate").rglob("*.lean")
                   if "VampireArtifacts" not in p.parts}
        while pending:
            ready = []
            for module, path in sorted(pending.items()):
                imports = re.findall(r"(?m)^import\s+([A-Za-z0-9_.]+)", path.read_text())
                if not any(name in pending for name in imports):
                    ready.append((module, path))
            if not ready:
                raise ValueError(f"cyclic emitted module imports: {sorted(pending)}")
            for module, path in ready:
                self.lean_file("compile-" + module, path, compile=True)
                del pending[module]

    def audit_proofs(self, bundle: dict) -> dict:
        results = {}
        source = self.src / "ProofAxioms.lean"
        for job in bundle["jobs"]:
            theorem = job["proof_namespace"] + "." + job["proof_theorem"]
            source.write_text(f"import {job['proof_module']}\n#print axioms {theorem}\n")
            actual = self.lean_file("axioms-" + job["id"], source)
            match = re.fullmatch(r"'" + re.escape(theorem) + r"' depends on axioms:\s*\[([^]]*)\]\s*", actual)
            if actual.strip() == f"'{theorem}' does not depend on any axioms":
                axioms = set()
            elif match is not None:
                axioms = {name.strip() for name in match[1].split(",") if name.strip()}
            else:
                raise ValueError(f"unrecognized proof audit: {actual}")
            if not axioms <= STD3:
                raise ValueError(f"non-std3 proof axioms for {job['id']}: {actual}")
            results[job["id"]] = sorted(axioms)
        return results

    def audit(self, refresh: bool) -> str:
        source = self.src / "PrintAxioms.lean"
        source.write_text(f"import Benchmark.{ID}.Certificate.Valid\n#print axioms Whiel.Benchmark.{ID}.Certificate.input_hoare_triple_valid\n")
        actual = self.lean_file("actual-axioms", source)
        expected = audit_source(actual)
        if refresh:
            (ROOT / AUDIT).write_text(expected)
        if not (ROOT / AUDIT).exists() or (ROOT / AUDIT).read_text() != expected:
            raise ValueError("axiom audit is stale; review actual output and run --refresh-axiom-guard")
        target = self.src / AUDIT
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(expected)
        result = self.lean_file("silent-axiom-audit", target)
        assert not result and not (self.output / "silent-axiom-audit.stderr").read_bytes(), "axiom audit must pass silently"
        return actual


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path, help="new scratch directory outside the worktree")
    parser.add_argument("--refresh-axiom-guard", action="store_true", help="regenerate only the test guard from actual kernel output")
    args = parser.parse_args()
    if (ROOT / "Benchmark" / ID).exists():
        raise ValueError("scratch fixture id collides with a corpus directory")
    driver = Driver(args.output)
    before_inputs = {str(p.relative_to(ROOT)): digest(p.read_bytes()) for p in sorted((ROOT / "Benchmark").glob("*/Input.lean"))}
    driver.prepare()
    description = driver.describe()
    bundle = driver.emit()
    driver.proofs(bundle)
    driver.compile_emitted()
    proof_axioms = driver.audit_proofs(bundle)
    axioms = driver.audit(args.refresh_axiom_guard)
    after_inputs = {str(p.relative_to(ROOT)): digest(p.read_bytes()) for p in sorted((ROOT / "Benchmark").glob("*/Input.lean"))}
    assert after_inputs == before_inputs, "corpus inputs or membership changed"
    receipt = {"status": "passed", "fixture": FIXTURE, "adapter_identity": driver.identity,
               "registered": False, "input_hashes": before_inputs, "scope_identity": driver.scope,
               "relation_table": description["relation_table"], "prophecy_bindings": description["prophecy_bindings"],
               "jobs": [j["id"] for j in bundle["jobs"]], "proof_axioms": proof_axioms, "actual_axioms": axioms,
               "artifact_hashes": {str(p.relative_to(driver.src)): digest(p.read_bytes())
                                   for p in sorted(driver.src.rglob("*.lean"))},
               "commands": driver.commands, "lean_num_threads": 2, "watchdog_limit_kib": 4194304}
    (driver.output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"flagged emitted certificate passed: {driver.output / 'receipt.json'}")


if __name__ == "__main__":
    main()
