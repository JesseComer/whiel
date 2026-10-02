-- Author: Jesse Comer
import Whiel.Synthesis.Runtime.CanonicalDigest
import Whiel.Synthesis.Runtime.FixedAmbientRegistry

set_option linter.style.nativeDecide false
set_option linter.hashCommand false

/-
  Product-path checks for the isolated Step-7 registry.

  The checks pin each registered task identity, the one
  computed prophecy relation table, body-only prophecy
  bindings, canonical clause admission over the prophecy
  schema, and typed `2N+1` worker jobs of the lifted loop.
  They also pin the production task's published wire values,
  so registering a second task cannot move them.
-/

------------------------------------------------------------
-- Registry Lookup
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace FixedAmbientRegistryTest

open Concrete
open Benchmark.Example0001
open Runtime
open Runtime.FixedAmbientRegistry
open Runtime.FixedAmbientRegistry.Example0001

/-
  The published ID list is exactly the entry list's own
  canonical IDs, in registry order. The checks below are
  stated over `supportedTaskIds` rather than one example
  per task, so they cover whatever `entries` holds.
-/
/- Canonical directory order, without a fixed inventory list. -/
#guard supportedTaskIds.Pairwise (· < ·)

/- Every published ID resolves. -/
example :
    supportedTaskIds.all
      (fun id => (lookup? id).isSome) = true := by
  decide

/- And resolves to the entry that carries it. -/
example :
    (supportedTaskIds.filterMap fun id =>
      (lookup? id).map fun e => e.identity.canonicalId) =
      supportedTaskIds := by
  decide

/- Nothing else resolves, by the general lemma. -/
example : lookup? "FixedAmbient0001" = none :=
  lookup?_eq_none_of_not_mem (by decide)

example : lookup? "Not-Registered" = none :=
  lookup?_eq_none_of_not_mem (by decide)

------------------------------------------------------------
-- Raw Input Bindings
------------------------------------------------------------

/- A raw input carries the input triple and nothing else:
   the task and scope identities belong to the entry. -/
example :
    Example0013.entry.identity.canonicalId =
      "Example0013" := by
  rfl

example :
    Example0013.entry.identity.moduleName =
      "Benchmark.Example0013.Input" := by
  rfl

/- The refutable fixture consumes the production path. -/
theorem refutable_supply_free_preprocessing :
    Whiel.Benchmark.Example0013.inputPreproc =
      Hoare.preprocess Whiel.Benchmark.Example0013.inputPre
        Whiel.Benchmark.Example0013.inputCmd
        Whiel.Benchmark.Example0013.inputPost :=
  Example0013.inputPreproc_eq_preprocess

/- Both fixtures are stated over the same input schema. -/
example :
    Example0013.rawInput.schema =
      Example0001.rawInput.schema := by
  rfl

example :
    entry.identity.canonicalId =
      "Example0001" := by
  rfl

example :
    entry.manifest.toJson = manifest.toJson := by
  rfl

------------------------------------------------------------
-- Pinned Production Wire Values
------------------------------------------------------------

/-
  The production entry is assembled by the shared
  `Entry.ofInput` route. These digests pin its published
  wire values, so a further registered task cannot silently
  move the production envelope. The scope identity and the
  bound manifest both carry `task_source_sha256`, the
  digest of the five canonical declarations of
  `Example0001/Input.lean`, so both move exactly when one
  of those declarations changes; comments and headers are
  outside the digest. The relation table and the prophecy
  bindings are built from solver keys alone and do not move
  with the source.
-/
example :
    (CanonicalDigest.jsonSha256 entry.scopeIdentity ==
      "9718bdae419490c34072c3c401fb02f9" ++
        "a2efb58a0612438e00c875072926cf72") = true := by
  native_decide

example :
    (CanonicalDigest.jsonSha256 entry.manifest.toJson ==
      "7647387f2a9480f13c0c668dc2257764" ++
        "c9063cdbbb97dede852d06e52e8dfcdd") = true := by
  native_decide

example :
    (CanonicalDigest.jsonSha256 relationTableJson ==
      "e1883b3324daf668ee4e98a7f85b7267" ++
        "f5ff2efb1a2f570550a47b113d7ab239") = true := by
  native_decide

example :
    (CanonicalDigest.jsonSha256 prophecyBindingsJson ==
      "88f4b049a88e8d7b03f488cb33264332" ++
        "059ce991c74925469e2e6c59f4da46b7") = true := by
  native_decide

/- The refutable entry has its own distinct scope. -/
example :
    (Example0013.entry.scopeIdentity ==
      entry.scopeIdentity) = false := by
  native_decide

/- The registry consumes only the production path. -/
theorem registry_supply_free_preprocessing :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost :=
  inputPreproc_eq_preprocess

/- The registry task is the generic lifted task. -/
example : entry.task = inputLoop.task := by
  rfl

------------------------------------------------------------
-- One Prophecy Relation Table
------------------------------------------------------------

/- Three ordinary copies plus two prophecy copies. -/
example : relationTable.length = 5 := by
  native_decide

example :
    relationTable.map
        (fun row => row.relation.1) =
      prophecySchema.syms.attach.sort.map Subtype.val := by
  native_decide

private def ordinaryProgram (base : String)
    (h : base.toList.all Char.isAlpha = true := by decide) :
    WhielNames :=
  .ordinary (.programSymbol ⟨base, h⟩ 0)

private def prophecyProgram (base : String)
    (h : base.toList.all Char.isAlpha = true := by decide) :
    WhielNames :=
  .prophecy (.programSymbol ⟨base, h⟩ 0)

private def relationNames : List WhielNames :=
  relationTable.map fun row => row.relation.1

/- The relation table is in structural order, all binary. -/
example :
    (relationTable.map fun row =>
      (row.key, row.display, row.arity)) =
      [ ("o:p::E", "E", 2),
        ("o:p::S", "S", 2),
        ("o:p::T", "T", 2),
        ("y:p::S", "S∞", 2),
        ("y:p::T", "T∞", 2) ] := by
  native_decide

/- The edge relation `E` has no prophecy copy. -/
example : ordinaryProgram "E" ∈ relationNames := by
  native_decide

example : prophecyProgram "E" ∉ relationNames := by
  native_decide

/- Only the two loop-body targets have prophecy copies. -/
example : prophecyProgram "T" ∈ relationNames := by
  native_decide

example : prophecyProgram "S" ∈ relationNames := by
  native_decide

example :
    (relationNames.filter fun name =>
      !name.IsOrdinary).length = 2 := by
  native_decide

private def bindingSources : List WhielNames :=
  prophecyBindings.map fun binding =>
    binding.source.1

private def bindingTargets : List WhielNames :=
  prophecyBindings.map fun binding =>
    binding.prophecy.1

example : prophecyBindings.length = 2 := by
  native_decide

example : ordinaryProgram "E" ∉ bindingSources := by
  native_decide

example : ordinaryProgram "T" ∈ bindingSources := by
  native_decide

example : ordinaryProgram "S" ∈ bindingSources := by
  native_decide

example : prophecyProgram "E" ∉ bindingTargets := by
  native_decide

theorem binding_source_assigned_by_body
    (binding : ProphecyBinding) :
    binding.source.1 ∈ loop.body.assignedSymbols :=
  binding.sourceAssigned

------------------------------------------------------------
-- Computed Lifted Loop
------------------------------------------------------------

/-
  The preprocessed loop precondition is the strongest
  postcondition of the prefix over the raw `true`; both of
  its conjuncts mention body-assigned relations.
-/
example :
    FrameworkII.FixedAmbient.SurfaceSyntax.source loop.pre =
      "((true ∧ (op_zT = ∅[2])) ∧ (op_zS = (op_zE ∪ " ++
        "π[0,3] (σ[#1 = #2] ((op_zE × op_zT))))))" := by
  native_decide

example :
    FrameworkII.FixedAmbient.SurfaceSyntax.source
        loop.guard =
      "(¬((op_zS = op_zT)))" := by
  native_decide

example :
    FrameworkII.FixedAmbient.SurfaceSyntax.source
        loop.post =
      "(π[0,3] (σ[#1 = #2] ((op_zT × op_zT))) ⊆ op_zT)" := by
  native_decide

------------------------------------------------------------
-- Admission and Typed Worker Operations
------------------------------------------------------------

private abbrev AdmittedClause :=
  Runtime.FixedAmbientRegistry.Example0001.Clause

/- Admit one canonical clause over the prophecy schema. -/
private def admitted (source : String) : AdmittedClause :=
  match admitClause source with
  | .ok clause => clause
  | .error _ =>
      FrameworkII.FixedAmbient.Clause.ofFormula .true

/- Level-zero Core clause: `S` is the one-step image. -/
private def ordinarySource : String :=
  "(op_zS = (op_zE ∪ π[0,3] (σ[#1 = #2] ((op_zE × op_zT)))))"

/- Level-one Core clause: the prophecy `T∞` is closed. -/
private def prophecySource : String :=
  "(π[0,3] (σ[#1 = #2] ((op_zT × yp_zT))) ⊆ yp_zT)"

example :
    (admitted ordinarySource).canonicalSource =
      ordinarySource := by
  native_decide

example :
    (admitted prophecySource).canonicalSource =
      prophecySource := by
  native_decide

/- Agent-surface spacing collapses to the canonical source. -/
example :
    (admitted ("(op_zS = (op_zE ∪ (π[0, 3] " ++
      "(σ[#1 = #2] (op_zE × op_zT)))))")).canonicalSource =
      ordinarySource := by
  native_decide

example :
    (admitted ("((π[0, 3] (σ[#1 = #2] (op_zT × yp_zT))) " ++
      "⊆ yp_zT)")).canonicalSource =
      prophecySource := by
  native_decide

example : (admitted ordinarySource).minimumLevel = 0 := by
  native_decide

example : (admitted prophecySource).minimumLevel = 1 := by
  native_decide

/- Prophecy copies of loop-body targets are admissible. -/
example :
    (admitted "(yp_zT = ∅[2])").canonicalSource =
      "(yp_zT = ∅[2])" := by
  native_decide

/- The edge relation has no prophecy copy to name. -/
example :
    (match admitClause "(yp_zE = ∅[2])" with
      | .ok _ => true
      | .error _ => false) = false := by
  native_decide

/- Arities are checked against the computed schema. -/
example :
    (match admitClause "(op_zE = ∅[1])" with
      | .ok _ => true
      | .error _ => false) = false := by
  native_decide

private def ordinaryClause : AdmittedClause :=
  admitted ordinarySource

private def prophecyClause : AdmittedClause :=
  admitted prophecySource

private def snapshot : Snapshot where
  rows :=
    [ { clauseId := 11
        level := 0
        clause := ordinaryClause },
      { clauseId := 12
        level := 1
        clause := prophecyClause } ]

/- Every job has the computed prophecy schema. -/
def exactJobs :
    List (QFEntailment (D := Data) prophecySchema) :=
  (buildAllObligations snapshot).map fun built =>
    built.entailment

example : exactJobs.length = 5 := by
  native_decide

/-
  No top-level conjunct of the computed precondition is
  EDB-only: `T` and `S` are both assigned by the body.
-/
example : preconditionRows.length = 0 := by
  native_decide

example :
    (preconditionRows.map fun row =>
      (row.ordinal, row.clause.canonicalSource)) = [] := by
  native_decide

example :
    taskComponents.length = 5 := by
  native_decide

example :
    (clauseComponents ordinaryClause).length = 4 := by
  native_decide

example :
    (match buildObligation snapshot
        (.initialization 11) with
      | .ok built => some built.selector
      | .error _ => none) =
      some (.initialization 11) := by
  native_decide

example :
    (match buildObligation snapshot
        (.maintenance 12) with
      | .ok built => some built.selector
      | .error _ => none) =
      some (.maintenance 12) := by
  native_decide

example :
    (match buildObligation snapshot .termination with
      | .ok built => some built.selector
      | .error _ => none) = some .termination := by
  native_decide

private def family :
    FrameworkII.FixedAmbient.LeveledFamily
      Data prophecySchema :=
  FrameworkII.FixedAmbient.Snapshot.family snapshot

/-
  The exact worker VCs of the lifted loop assemble the
  authoritative raw input triple over its own schema.
-/
theorem exact_input_of_worker_vcs
    (hInit : ∀ clause ∈ family.clauses,
      (family.initVC task loop.guard loop.pre
        clause).Valid)
    (hStep : ∀ clause ∈ family.clauses,
      (family.maintenanceVC task loop.guard
        loop.body_loopFree clause).Valid)
    (hTerm :
      (family.terminationVC task loop.guard
        loop.post).Valid) :
    HoareValid inputPre inputCmd inputPost :=
  FrameworkII.FixedAmbient.Preproc.certifyProgramInput
    inputPreproc family hInit hStep hTerm

------------------------------------------------------------
-- The Refutable Twin
------------------------------------------------------------

namespace Refutable

private abbrev entry :=
  Runtime.FixedAmbientRegistry.Example0013.entry

private abbrev loop :=
  Runtime.FixedAmbientRegistry.Example0013.loop

/- The refutable fixture is a full Framework-II entry. -/
example : entry.identity.canonicalId = "Example0013" := by
  rfl

/-
  It shares Example0001's program schema and command, so its
  computed prophecy schema and relation table coincide with
  the production one; only its postcondition differs.
-/
example :
    (entry.relationTable.map fun row =>
      (row.key, row.display, row.arity)) =
      [ ("o:p::E", "E", 2),
        ("o:p::S", "S", 2),
        ("o:p::T", "T", 2),
        ("y:p::S", "S∞", 2),
        ("y:p::T", "T∞", 2) ] := by
  native_decide

example : entry.prophecyBindings.length = 2 := by
  native_decide

/- The lifted loop postcondition is the false claim. -/
example :
    FrameworkII.FixedAmbient.SurfaceSyntax.source loop.post =
      "(op_zT ⊆ op_zE)" := by
  native_decide

/- Its precondition is Example0001's, so it too has no
  EDB-only conjunct to protect. -/
example : entry.preconditionRows.length = 0 := by
  native_decide

example : entry.taskComponents.length = 5 := by
  native_decide

/- Clause admission works over the refutable entry too. -/
example :
    (match entry.admitClause "(op_zT = ∅[2])" {} with
      | .ok clause => clause.canonicalSource
      | .error _ => "") = "(op_zT = ∅[2])" := by
  native_decide

/- A registered task needs no Core: `2N+1` jobs are built
  from an empty snapshot alone. -/
example :
    (entry.buildAllObligations { rows := [] }).length = 1 := by
  native_decide

end Refutable

/- Controls retain distinct source-bound identities. -/
example : Example0001.entry.identity.canonicalId =
    "Example0001" := rfl

example : Example0106.entry.identity.canonicalId =
    "Example0106" := rfl

/- Measured after typed preprocessing, not inferred from text. -/
#guard Example0001.entry.preconditionRows.length == 0

#guard
  (Example0106.entry.preconditionRows.map fun row =>
    (row.ordinal, row.clause.canonicalSource)) ==
    [(0, "((op_zBase ∪ π[0,3] (σ[#1 = #2] " ++
      "((op_zRBound × op_zRBound)))) ⊆ op_zRBound)")]

/- Registration alone needs no candidate invariant. -/
#guard (Example0106.entry.buildAllObligations
  { rows := [] }).length == 1

end FixedAmbientRegistryTest
end Tests
end Synthesis
end Whiel
