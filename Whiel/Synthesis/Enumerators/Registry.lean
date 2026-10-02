-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.FastContract

/-
  Proof-gated realization registry: the entry types.

  A `RegisteredRealization` packages a selectable proposal
  stream together with the proofs the pipeline's soundness
  story requires of it: finite-prefix coverage of the
  protected reference stream (the `FastContract` obligation)
  and duplicate-free output. Because the proofs are fields,
  an unproven stream cannot be registered at all --- the
  entry fails to elaborate --- so the gate acts at compile
  time, in the worker binary, rather than by convention in
  an audit checklist.

  An `ExperimentalRealization` carries a stream with no
  proof obligations. Experimental entries are never
  default-selectable; a run that uses one must mark its
  provenance explicitly.

  The concrete tables and their binding to the wire-level
  realization identifiers live in
  `Runtime/RealizationRegistry.lean`; this file defines only
  the entry types, so the `Enumerators` root stays free of
  runtime imports.

  Proof fields are computationally irrelevant and erase at
  compilation: carrying them costs nothing at runtime.
-/

------------------------------------------------------------
-- Registered Realizations
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

open DisjunctiveClause

variable (A D : Type)
variable [RelationNames A] [Domain D]
variable (Γ : UnnamedSchema A)
variable [LinearOrder A] [LinearOrder D]

/-
  One proven, selectable realization. The stream takes the
  task alphabet and the task's seeded literals; realizations
  that do not use seeds ignore the argument. Streams with
  further parameters (schedules, policies) are registered at
  a fixed instantiation, so an entry always denotes one
  concrete selectable behavior.
-/
structure RegisteredRealization where
  id : String
  version : Nat
  stream :
    Alphabet D Γ → Finset (Literal D Γ) →
      Nat → List (QFAssertExpr D Γ)
  covers :
    ∀ (alphabet : Alphabet D Γ)
      (seeds : Finset (Literal D Γ)),
      FastEnumerator.CoversReference alphabet
        (stream alphabet seeds)
  nodup :
    ∀ (alphabet : Alphabet D Γ)
      (seeds : Finset (Literal D Γ))
      (completedStages : Nat),
      (stream alphabet seeds completedStages).Nodup

/-
  One experimental realization: a stream with no proof
  obligations. Never default-selectable.
-/
structure ExperimentalRealization where
  id : String
  version : Nat
  stream :
    Alphabet D Γ → Finset (Literal D Γ) →
      Nat → List (QFAssertExpr D Γ)

end Enumerators

end Synthesis

end Whiel
