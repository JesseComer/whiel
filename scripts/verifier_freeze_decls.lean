import Lean

/-!
# Verifier-freeze declaration-level dependency tool

Part 2 of the verifier freeze (see the repo-root `AGENTS.md`'s "Verifier
Freeze" section and `scripts/verifier_freeze.py`). This file is a
standalone script, not a library module: nothing imports it, and it is not
registered as a `lean_lib`/`lean_exe` target in `lakefile.toml`. Run it from
the repo root with

  lake env lean --run scripts/verifier_freeze_decls.lean

Only `Lean` is imported statically. The fixed-ambient worker's own root
module is imported *dynamically*, by name, at run time (`Lean.importModules`)
rather than with a static `import` at the top of this file. This keeps the
file out of the library import graph (consistent with "not part of any lake
target") and mirrors the standard pattern Lean's own `leanchecker` tool uses
for one-shot environment inspection
(`$LEAN_SYSROOT/src/lean/LeanChecker.lean`, `unsafe def main` calling
`Lean.importModules`/`Lean.withImportModules`).

## Target and roots

`targetModule` is `Whiel.Synthesis.Runtime.FixedAmbientWorker`: the
`lakefile.toml` `[[lean_exe]] name = "fixed_ambient_encoding_worker"`
target's `root`, and the one module the search-time worker executable is
built from (confirmed: no other `lean_exe` in `lakefile.toml` names it, and
it is already `verifier_freeze_data.json`'s `lean_root_module` for the
file-level check). Importing it pulls in everything below transitively,
including `FixedAmbientRegistry`.

`roots` is the search-time command handlers of that module's dispatch table
(`runOperation`, around line 1636) plus the one registry lookup they need.
It deliberately does *not* root at `runOperation`, `dispatchBound`,
`dispatch`, `run`/`runOn`, or `main`: each of those is a single declaration
whose *value* is one big pattern match (or a call chain ending in one) over
every wire operation, so rooting at any of them would drag in the
certificate handlers (`emit_certificate`, `emit_invalid_certificate`,
`package_proof`, backed by `whiel_runner/src/framework2/certificate_ops.rs`,
already excluded from the Rust verifier set in
`scripts/verifier_freeze_data.json`) through that same declaration — a
"constants used in this value" analysis cannot tell which match arm a
reference came from. Rooting at the individual per-operation `private def`
handlers avoids that: each is its own declaration, reachable only from its
own operation.

Two operations Lean still serves are left out because production Rust never
issues them from the search path:
* `build_exact_obligation`: `whiel_runner/src/framework2/solver.rs`'s
  `build_selected_obligation`, its only caller, is `#[cfg(test)]`-gated (and
  `encoding/protocol.rs` says so directly: "since Pass 7.5d the production
  path never issues it ... the only Rust callers left are this crate's own
  tests"). Its own decode path (`decodeExactJob`/`decodeExactJobData`) is a
  strict subset of `prepare_exact_obligation`'s
  (`decodeBoundExactJobFields`), so nothing is lost by leaving it out.
* `prepare_component`: `docs/lean-runtime-api.md`'s operation table records
  "no current production Rust wrapper found" for it, and no
  `FixedAmbientWorkerOperation::PrepareComponent` construction exists
  outside `encoding/protocol.rs`'s own enum/display code.

`ping` and `shutdown` are handled inline in `runOperation` with no separate
declaration and trivial bodies (`{"ready": true}` / `{"stopped": true}`,
referencing nothing) — there is no declaration to root there.

The registry lookup (`FixedAmbientRegistry.lookup?`) is a necessary root
beyond the protocol handlers: every handler above is generic over an
abstract `[Bound]` instance (`entry := Bound.boundEntry`), so a "constants
used" traversal starting only from the handlers stops at the *type*
`FixedAmbientRegistry.Entry` and never reaches the concrete per-task
implementations `Entry.ofInput` assigns to each field — the real clause
admission, obligation-building, refutation- and counterexample-validation
logic in `Whiel/Synthesis/FrameworkII/FixedAmbient/*`, and the registered
`Benchmark/ExampleNNNN/Input.lean` data. `lookup?` is where the abstract
`Bound` instance is actually resolved to one of those concrete entries
(`dispatch`'s `letI : Bound := ⟨bound⟩`), so it is the edge that reaches
them.

Rooting at `lookup?` is deliberately imprecise in the certificate direction.
`Entry.ofInput` (`Whiel/Synthesis/Runtime/FixedAmbientRegistry/Support.lean`)
builds *every* field of one `Entry` — search-time and certificate-only
alike — in a single structure literal, from one shared per-task
constructor. A "constants used in this value" analysis cannot tell that a
downstream declaration only ever reads the `admitClause` field and not the
`emitCertificate` field; both are just sub-terms of the same literal.
Separating them precisely would need bespoke projection-reduction logic
specific to this one declaration, which this tool deliberately avoids in
favour of staying a general, auditable traversal usable on any declaration.
Per this lane's brief's own fallback for exactly this situation, the output
below therefore also includes, unavoidably, the certificate-only
declarations reached only through `Entry.ofInput`:
`FrameworkII.FixedAmbient.CertificateEmitter.emit`,
`FrameworkII.FixedAmbient.CertificateEmitter.InputBinding.ofTaskIdentity`,
and their own further dependencies. `emit_invalid_certificate`'s
`Entry.admitFrozenCounterexample`/`Entry.emitInvalidCertificate` and
`package_proof`'s `CertificateEmitter.packageProof` are *not* pulled in:
each is a separate top-level/`Entry`-namespace declaration outside
`Entry`/`Entry.ofInput` itself, and none of this tool's roots reaches them.

## Edges followed

For each reached declaration, using its `ConstantInfo`:
* every constant in its type, and in its value when accessible without
  forcing a theorem's proof or an opaque body open
  (`Lean.ConstantInfo.getUsedConstantsAsSet`, built on
  `Lean.Expr.getUsedConstants`/`Expr.foldConsts`); this function already
  supplies the fallback for constants with no ordinary value — an
  inductive's constructors, a constructor's own name, a recursor's mutual
  block — so those never panic;
* for an inductive, additionally its recursor, found as `Lean.mkRecName`
  if that name exists in the environment (the fallback above adds the
  constructors but not the recursor);
* for a structure, additionally its projection functions
  (`Lean.getStructureFields`/`Lean.getProjFnForField?`);
* an `@[implemented_by]` replacement (`Lean.Compiler.getImplementedBy?`);
* an `@[csimp]` replacement (`Lean.Compiler.CSimp.ext`'s scoped state).

Not followed, and why:
* `@[extern]` names a *native* symbol (a C function name, a `String`), not
  a Lean declaration, so there is no further Lean constant to add as a
  graph edge. Presence is checked (`Lean.isExtern`) but produces no edge.
* Instances used in an elaborated term are ordinary `Expr.const`
  applications already inside that term's type/value, so they need no
  special-casing beyond the first bullet.
* `_sunfold`/`match_`/well-founded-recursion auxiliary definitions are
  likewise ordinary named constants referenced from the main declaration's
  elaborated value where used, so the first bullet already follows them;
  `_cstage1`/`_cstage2` compiled-IR entries are compiler artifacts with no
  corresponding `Expr`-level reference and are not part of this graph.
* Free/local/meta variables, literals, sorts, and other non-`const` `Expr`
  nodes carry no global name, so `Expr.getUsedConstants` has nothing to
  add for them.

## Scope restriction

Only declarations whose defining module is under `Whiel.`, `Databases.`,
`Benchmark.`, or `VampLean.` are printed (`Environment.getModuleIdxFor?`
plus the environment header's module name table): everything else is Lean
core, Std, Mathlib, or another `lake-manifest.json`-pinned dependency,
already covered by the toolchain/manifest pins rather than this tool. The
traversal does not expand a non-repository constant's own dependencies
either: a dependency's constant cannot itself depend on a constant of the
*importing* project (Mathlib cannot reference `Whiel`), so pruning there is
exact, not an approximation that could miss a repository declaration.

## Hashing

Each printed declaration's hash covers `kind ++ "\n" ++ type ++ value?`,
where `type`/`value?` are `toString` of the `Expr`s. `Lean.Expr`'s only
`ToString` instance is `Expr.dbgToString`, a plain structural dump of the
term (binder names, de Bruijn indices, constant/literal/universe nodes) with
no delaborator, notation, or open-namespace dependence, so it is
"pretty-printer-independent" in the sense this lane's brief asks for: two
`Expr`s that print the same are structurally the same term. This is
deterministic across repeated runs on the same toolchain: declarations
loaded from `.olean`s are closed terms (a bound variable is already an
`Expr.bvar` de Bruijn index, not an `Expr.fvar`/`Expr.mvar` — the only parts
of an `Expr` whose identity is per-elaboration-run and not reproducible),
and the hash function below (FNV-1a, 64-bit, hand-rolled in this file
rather than relying on an undocumented stability guarantee for Lean's own
built-in `Hashable` instances, which are not documented as seed-free) is a
pure function of the UTF-8 bytes of that string.

Per this lane's brief, `value?` is included for an ordinary definition but
omitted for a theorem: `ConstantInfo.value? (allowOpaque := false)` already
returns `none` for `thmInfo`/`opaqueInfo`, giving exactly that split for
free, matching the brief's rationale directly — a theorem's proof term
cannot affect runtime behaviour, so only its statement (`type`) is worth
freezing, and proof terms are typically far more expensive to print/hash
than the statement. Axioms, inductives/structures, constructors and
recursors have no `value?` either, so they hash on `type` alone, which is
all they have; this is also why nothing here ever forces an opaque or axiom
body open, and nothing panics on them.
-/

open Lean

namespace VerifierFreezeDecls

/-- The `lean_exe fixed_ambient_encoding_worker` root; importing it reaches
every declaration below, including `FixedAmbientRegistry`. -/
def targetModule : Name := `Whiel.Synthesis.Runtime.FixedAmbientWorker

/-- Original (pre-mangling) names of the search-time per-operation
`private def` handlers this tool roots at, all declared in `targetModule`.
See the module docstring for why each is included and why two operations
and two trivial inline cases are not. -/
def privateRootUserNames : List Name := [
  -- Envelope validation, run before every operation.
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.validateRequest,
  -- `describe`
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.describePayload,
  -- `extend_name_env`
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.extendNameEnv,
  -- `admit_clauses`
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.admitClausesPayload,
  -- `evaluate_clauses` (also backs the proposer's `validate_clauses`)
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.evaluateClausesPayload,
  -- `prepare_task_pieces`
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.prepareTaskPiecesPayload,
  -- `prepare_clause_pieces`
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.prepareClausePiecesPayload,
  -- `prepare_support_block`
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.prepareSupportBlockPayload,
  -- `prepare_exact_obligation`
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.boundExactJobPayload,
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.prepareEntailmentJson,
  -- `check_empty_counterexample`
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.emptyResultJson,
  -- `validate_refutation`
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.validateRefutationPayload,
  -- `extract_precondition_clauses`
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.preconditionBasisJson,
  -- `confirm_precondition_row`
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.confirmPreconditionRowPayload,
  -- `validate_counterexample`
  `Whiel.Synthesis.Runtime.FixedAmbientWorker.validateCounterexamplePayload
]

/-- The one public root: the registry lookup `dispatch` resolves every
request's canonical task ID against, and the only route from the generic
protocol handlers above to the concrete per-task implementations. -/
def publicRootNames : List Name := [
  `Whiel.Synthesis.Runtime.FixedAmbientRegistry.lookup?
]

/-- Every `private def` above is declared directly in `targetModule`, so
its actual environment name is the traditional Lean 4 private mangling of
its user-facing name (`Lean.PrivateName`'s `_private.<module>.0 ++ name`),
computed here rather than hard-coded so this file states the mathematical
relationship instead of an opaque literal. -/
def roots : List Name :=
  (privateRootUserNames.map (Lean.mkPrivateNameCore targetModule)) ++
    publicRootNames

/-- A constant belongs to this repository's own source, rather than Lean
core/Std/Mathlib/another pinned dependency, exactly when its defining
module is under one of these roots (the `lean_lib`s in `lakefile.toml`
besides `EngineFixtures`, which the search-time worker does not use). -/
def repoPrefixes : List Name := [`Whiel, `Databases, `Benchmark, `VampLean]

def isRepoModule (m : Name) : Bool :=
  repoPrefixes.any (·.isPrefixOf m)

/-- Human-readable declaration kind, matching `ConstantInfo`'s own
constructors one for one. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

/-! ### FNV-1a, 64-bit

A small, self-contained, deterministic string hash (see the module
docstring's "Hashing" section for why determinism matters and why this is
hand-rolled rather than reusing a built-in `Hashable` instance). -/

private def fnvOffset : UInt64 := 0xcbf29ce484222325
private def fnvPrime : UInt64 := 0x100000001b3

private def fnv1a (s : String) : UInt64 := Id.run do
  let mut h := fnvOffset
  for b in s.toUTF8 do
    h := (h ^^^ UInt64.ofNat b.toNat) * fnvPrime
  return h

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n + 87)

/-- Fixed-width (16 hex digit), most-significant-digit-first rendering. -/
private def toHex64 (n : UInt64) : String := Id.run do
  let mut x := n.toNat
  let mut chars : List Char := []
  for _ in [0:16] do
    chars := hexDigit (x % 16) :: chars
    x := x / 16
  return String.ofList chars

/-- The declaration's hash input and hash. `value?` is Lean's own default
(`allowOpaque := false`), which already omits a theorem's proof and an
opaque's body — see the module docstring. -/
def declHash (info : ConstantInfo) : String :=
  let header := kindOf info ++ "\n" ++ toString info.type
  let full := match info.value? with
    | some v => header ++ "\n" ++ toString v
    | none => header
  toHex64 (fnv1a full)

/-- Edges this tool follows beyond `ConstantInfo.getUsedConstantsAsSet`:
an inductive's recursor, a structure's projections, an `@[implemented_by]`
replacement, and an `@[csimp]` replacement. See the module docstring for
the edges *not* followed and why. -/
def extraEdges (env : Environment) (name : Name) (info : ConstantInfo) :
    List Name := Id.run do
  let mut extra : List Name := []
  if info.isInductive then
    let recName := Lean.mkRecName name
    if (env.find? recName).isSome then
      extra := recName :: extra
  if Lean.isStructure env name then
    for field in Lean.getStructureFields env name do
      if let some projFn := Lean.getProjFnForField? env name field then
        extra := projFn :: extra
  if let some impl := Lean.Compiler.getImplementedBy? env name then
    extra := impl :: extra
  if let some entry := (Lean.Compiler.CSimp.ext.getState env).map.find? name then
    extra := entry.toDeclName :: extra
  return extra

/-- One row of the printed table: declaration name, defining module, kind,
hash. -/
abbrev Row := Name × Name × String × String

/-- Breadth-first (order does not matter; output is sorted afterwards)
traversal of the constant-dependency graph from `roots`, restricted to
repository declarations. `visited` guards against revisiting a name
reachable by more than one path; it is seeded with every name ever placed
on the worklist (not only every name popped), so a name cannot be queued
twice either. Declarations outside the repository are neither added to the
output nor expanded further (see the module docstring's "Scope
restriction"). A referenced name absent from the environment (should not
happen for a well-formed closed environment, but this must not panic) is
simply skipped. -/
partial def collect (env : Environment) :
    List Name → NameSet → Array Row → Array Row
  | [], _, acc => acc
  | name :: rest, visited, acc =>
      match env.find? name with
      | none => collect env rest visited acc
      | some info =>
          match env.getModuleIdxFor? name with
          | none => collect env rest visited acc
          | some idx =>
              match env.header.moduleNames[idx]? with
              | none => collect env rest visited acc
              | some moduleName =>
                  if !isRepoModule moduleName then
                    collect env rest visited acc
                  else
                    let row : Row := (name, moduleName, kindOf info, declHash info)
                    let edges := info.getUsedConstantsAsSet.toList ++
                      extraEdges env name info
                    let toQueue := edges.filter (!visited.contains ·)
                    let visited := toQueue.foldl (·.insert ·) visited
                    collect env (toQueue ++ rest) visited (acc.push row)

def rowLt (a b : Row) : Bool :=
  a.1.toString < b.1.toString

end VerifierFreezeDecls

open VerifierFreezeDecls in
unsafe def main : IO UInt32 := do
  -- Required before `importModules` below when `loadExts := true`: the
  -- persistent environment extensions this tool queries (structure info,
  -- `@[implemented_by]`, `@[csimp]`) are only populated from imported
  -- module data when extensions are loaded, and loading them may run
  -- interpreted `initialize` code.
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules
    (imports := #[{ module := targetModule }])
    (opts := {})
    (loadExts := true)
  let missing := roots.filter fun r => (env.find? r).isNone
  if !missing.isEmpty then
    IO.eprintln s!"verifier_freeze_decls: root(s) not found in the \
      environment (private-name mangling mismatch, or the handler was \
      renamed/removed): {missing}"
    return 1
  let visited : NameSet := roots.foldl (·.insert ·) {}
  let rows := collect env roots visited #[]
  let sorted := rows.qsort rowLt
  for (name, moduleName, kind, hash) in sorted do
    IO.println s!"{name}\t{moduleName}\t{kind}\t{hash}"
  return 0
