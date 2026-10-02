-- Author: Jesse Comer
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Generated

/- Stable compatibility aliases and generic lookup proofs. -/

------------------------------------------------------------
-- Example0001 Compatibility
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0001

open Concrete
open Benchmark.Example0001

/- The preprocessed input loop over the flag extension. -/
abbrev inputLoop :
    Hoare.LoopTriple Data inputPreproc.outSchema :=
  FrameworkII.FixedAmbient.Preproc.loop inputPreproc

/- The computed prophecy schema of the input loop. -/
abbrev prophecySchema : UnnamedSchema WhielNames :=
  entry.prophecySchema

/- The input loop lifted to the prophecy schema. -/
abbrev loop : Hoare.LoopTriple Data prophecySchema :=
  entry.loop

/- The generic task of the lifted loop body. -/
abbrev task : FrameworkII.FixedAmbient.Task loop.body :=
  entry.task

/- One typed row in the sole prophecy relation table. -/
abbrev RelationRow := FixedAmbientRegistry.RelationRow prophecySchema

/- The complete relation table, in structural order. -/
abbrev relationTable : List RelationRow :=
  entry.relationTable

/- The one prophecy relation table for wire publication. -/
abbrev relationTableJson : Lean.Json :=
  entry.relationTableJson

/- One body-derived ordinary/prophecy correspondence. -/
abbrev ProphecyBinding :=
  FrameworkII.FixedAmbient.Task.Binding task

/-
  Exactly the prophecy partners required by the loop body.
-/
abbrev prophecyBindings : List ProphecyBinding :=
  entry.prophecyBindings

/-
  Body-only prophecy correspondence for wire publication.
-/
abbrev prophecyBindingsJson : Lean.Json :=
  entry.prophecyBindingsJson

/- Complete task-bound identity of the same-schema scope. -/
abbrev scopeIdentity : Lean.Json :=
  entry.scopeIdentity

/-
  Admitted clauses use the computed prophecy schema.
-/
abbrev Clause :=
  FrameworkII.FixedAmbient.Clause prophecySchema

/- Catalog rows are indexed by the prophecy schema. -/
abbrev CatalogRow :=
  FrameworkII.FixedAmbient.CatalogRow prophecySchema

/- Core snapshots use the prophecy schema. -/
abbrev Snapshot :=
  FrameworkII.FixedAmbient.Snapshot prophecySchema

/- Built jobs are indexed by the prophecy schema. -/
abbrev BuiltObligation :=
  FrameworkII.FixedAmbient.BuiltObligation prophecySchema

/- Prepared jobs retain the prophecy schema. -/
abbrev PreparedEntailment :=
  FrameworkII.FixedAmbient.PreparedEntailment prophecySchema

/- Prepared components retain the prophecy schema. -/
abbrev PreparedComponent :=
  FrameworkII.FixedAmbient.PreparedComponent prophecySchema

/- Empty checks retain the prophecy schema. -/
abbrev EmptyCheckResult :=
  FrameworkII.FixedAmbient.EmptyCheckResult prophecySchema

/- Protected precondition rows use the prophecy schema. -/
abbrev PreconditionRow :=
  FrameworkII.FixedAmbient.PreconditionRow prophecySchema

/- Admit one canonical clause through the Lean parser. -/
abbrev admitClause
    (source : String)
    (limits : FrameworkII.SurfaceParser.Limits := {}) :
    Except FrameworkII.FixedAmbient.ClauseAdmissionFailure
      Clause :=
  entry.admitClause source limits

/- Atomically admit one canonical clause batch. -/
abbrev admitClauses
    (sources : List String)
    (limits : FrameworkII.SurfaceParser.Limits := {}) :
    Except FrameworkII.FixedAmbient.ClauseAdmissionFailure
      (List Clause) :=
  entry.admitClauses sources limits

/- Build every exact job in stable `2N+1` order. -/
abbrev buildAllObligations
    (snapshot : Snapshot) : List BuiltObligation :=
  entry.buildAllObligations snapshot

/- Build one exact initialization, maintenance, or exit job. -/
abbrev buildObligation
    (snapshot : Snapshot)
    (selector :
      FrameworkII.FixedAmbient.ObligationSelector) :
    Except String BuiltObligation :=
  entry.buildObligation snapshot selector

/- Immutable components derived from the lifted loop. -/
abbrev taskComponents :
    List (FrameworkII.FixedAmbient.Component.Metadata
      prophecySchema) :=
  entry.taskComponents

/- Immutable components derived from one admitted clause. -/
abbrev clauseComponents
    (clause : Clause) :
    List (FrameworkII.FixedAmbient.Component.Metadata
      prophecySchema) :=
  entry.clauseComponents clause

/- Every EDB-only top-level precondition conjunct. -/
abbrev preconditionRows : List PreconditionRow :=
  entry.preconditionRows

/- Certificate binding of the immutable compiled Input. -/
abbrev certificateBinding :
    FrameworkII.FixedAmbient.CertificateEmitter.InputBinding :=
  entry.certificateBinding

/- The raw input triple of the production task. -/
abbrev rawInput : FrameworkII.FixedAmbient.RawInput :=
  entry.rawInput

end Example0001
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Example0013 Compatibility
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0013

open Concrete
open Benchmark.Example0013

/- The preprocessed input loop over the flag extension. -/
abbrev inputLoop :
    Hoare.LoopTriple Data inputPreproc.outSchema :=
  FrameworkII.FixedAmbient.Preproc.loop inputPreproc

/- The computed prophecy schema of the input loop. -/
abbrev prophecySchema : UnnamedSchema WhielNames :=
  entry.prophecySchema

/- The input loop lifted to the prophecy schema. -/
abbrev loop : Hoare.LoopTriple Data prophecySchema :=
  entry.loop

/- Complete task-bound identity of the same-schema scope. -/
abbrev scopeIdentity : Lean.Json :=
  entry.scopeIdentity

/- The raw input triple of the refutable fixture. -/
abbrev rawInput : FrameworkII.FixedAmbient.RawInput :=
  entry.rawInput

end Example0013
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Example4001 Compatibility
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4001

open Concrete
open Benchmark.Example4001

/- The preprocessed input loop over the flag extension. -/
abbrev inputLoop :
    Hoare.LoopTriple Data inputPreproc.outSchema :=
  FrameworkII.FixedAmbient.Preproc.loop inputPreproc

/- The computed prophecy schema of the input loop. -/
abbrev prophecySchema : UnnamedSchema WhielNames :=
  entry.prophecySchema

/- The input loop lifted to the prophecy schema. -/
abbrev loop : Hoare.LoopTriple Data prophecySchema :=
  entry.loop

/- Complete task-bound identity of the same-schema scope. -/
abbrev scopeIdentity : Lean.Json :=
  entry.scopeIdentity

/- The raw input triple of the Task 1 preamble input. -/
abbrev rawInput : FrameworkII.FixedAmbient.RawInput :=
  entry.rawInput

end Example4001
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Example4002 Compatibility
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4002

open Concrete
open Benchmark.Example4002

/- The preprocessed input loop over the flag extension. -/
abbrev inputLoop :
    Hoare.LoopTriple Data inputPreproc.outSchema :=
  FrameworkII.FixedAmbient.Preproc.loop inputPreproc

/- The computed prophecy schema of the input loop. -/
abbrev prophecySchema : UnnamedSchema WhielNames :=
  entry.prophecySchema

/- The input loop lifted to the prophecy schema. -/
abbrev loop : Hoare.LoopTriple Data prophecySchema :=
  entry.loop

/- Complete task-bound identity of the same-schema scope. -/
abbrev scopeIdentity : Lean.Json :=
  entry.scopeIdentity

/- The raw input triple of the Task 1 input. -/
abbrev rawInput : FrameworkII.FixedAmbient.RawInput :=
  entry.rawInput

end Example4002
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Example4037 Compatibility
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4037

open Concrete
open Benchmark.Example4037

/- The preprocessed input loop over the flag extension. -/
abbrev inputLoop :
    Hoare.LoopTriple Data inputPreproc.outSchema :=
  FrameworkII.FixedAmbient.Preproc.loop inputPreproc

/- The computed prophecy schema of the input loop. -/
abbrev prophecySchema : UnnamedSchema WhielNames :=
  entry.prophecySchema

/- The input loop lifted to the prophecy schema. -/
abbrev loop : Hoare.LoopTriple Data prophecySchema :=
  entry.loop

/- Complete task-bound identity of the same-schema scope. -/
abbrev scopeIdentity : Lean.Json :=
  entry.scopeIdentity

/- The raw input triple of the Task 8 input. -/
abbrev rawInput : FrameworkII.FixedAmbient.RawInput :=
  entry.rawInput

end Example4037
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Example4041 Compatibility
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4041

open Concrete
open Benchmark.Example4041

/- The preprocessed input loop over the flag extension. -/
abbrev inputLoop :
    Hoare.LoopTriple Data inputPreproc.outSchema :=
  FrameworkII.FixedAmbient.Preproc.loop inputPreproc

/- The computed prophecy schema of the input loop. -/
abbrev prophecySchema : UnnamedSchema WhielNames :=
  entry.prophecySchema

/- The input loop lifted to the prophecy schema. -/
abbrev loop : Hoare.LoopTriple Data prophecySchema :=
  entry.loop

/- Complete task-bound identity of the same-schema scope. -/
abbrev scopeIdentity : Lean.Json :=
  entry.scopeIdentity

/- The raw input triple of the Task 4 flagged input. -/
abbrev rawInput : FrameworkII.FixedAmbient.RawInput :=
  entry.rawInput

end Example4041
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Registry Lookup
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry

/- Exact supported-ID list; no legacy task is reachable. -/
def supportedTaskIds : List String :=
  entries.map fun e => e.identity.canonicalId

/-
  No two entries publish the same canonical ID, so
  `lookup?` cannot shadow one registration with another and
  the published ID list has one line per entry.
-/
theorem supportedTaskIds_nodup : supportedTaskIds.Nodup := by
  decide

/- Resolve only a dedicated fixed-ambient input. -/
def lookup?
    (canonicalId : String) : Option Entry :=
  entries.find? fun e =>
    e.identity.canonicalId == canonicalId

/-
  What `lookup?` answers with is a registered entry, never
  a fresh one. Stated over the entry list, so it holds of
  every entry the list will ever hold.
-/
theorem mem_entries_of_lookup?
    {canonicalId : String} {e : Entry}
    (h : lookup? canonicalId = some e) :
    e ∈ entries :=
  List.mem_of_find?_eq_some h

/-
  And it answers under the requested ID, never under a
  neighbouring entry's.
-/
theorem canonicalId_of_lookup?
    {canonicalId : String} {e : Entry}
    (h : lookup? canonicalId = some e) :
    e.identity.canonicalId = canonicalId := by
  unfold lookup? at h
  have hMatch := List.find?_some h
  exact eq_of_beq hMatch

/-
  The resolvable IDs are exactly the published ones: the
  worker's supported-ID list and its dispatch cannot drift
  apart, whatever `entries` holds.
-/
theorem isSome_lookup?_iff_mem
    {canonicalId : String} :
    (lookup? canonicalId).isSome = true <->
      canonicalId ∈ supportedTaskIds := by
  unfold lookup? supportedTaskIds
  induction entries with
  | nil => simp
  | cons e rest ih =>
      by_cases h : e.identity.canonicalId = canonicalId
      · simp [h]
      · simp [h, ih, Ne.symm h]

/- An unregistered ID resolves to nothing at all. -/
theorem lookup?_eq_none_of_not_mem
    {canonicalId : String}
    (h : canonicalId ∉ supportedTaskIds) :
    lookup? canonicalId = none := by
  have : ¬ (lookup? canonicalId).isSome = true := by
    simpa [isSome_lookup?_iff_mem] using h
  exact Option.not_isSome_iff_eq_none.mp this

end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
