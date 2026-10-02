-- Author: Jesse Comer
import Whiel.Synthesis.Correspondence

/-
  Focused checks for the class-agnostic semantic layer.
-/

------------------------------------------------------------
-- Clauses and Candidate Denotation
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

example
    (clause : QFAssertExpr D Γ) :
    (clause : Clause D Γ) = clause :=
  rfl

example
    (clauseClass : ClauseClass D Γ)
    (clause : Clause D Γ) :
    clause ∈ clauseClass ↔ clauseClass clause :=
  Iff.rfl

example
    {clauseClass : ClauseClass D Γ}
    (slice : clauseClass.Slice)
    {clause : Clause D Γ}
    (hMember : clause ∈ slice.clauses) :
    clause ∈ clauseClass :=
  slice.mem_class hMember

example
    {clauseClass : ClauseClass D Γ}
    (slice : clauseClass.Slice) :
    slice.clauses.Finite :=
  slice.finite

example
    (clauses : Candidate D Γ)
    (I : Instance D Γ) :
    clauses.denote I ↔
      ∀ clause ∈ clauses, clause.eval I :=
  Candidate.denote_apply_iff clauses I

example
    (I : Instance D Γ) :
    (∅ : Candidate D Γ).denote I := by
  simp [Candidate.denote]

example
    {clauses : Candidate D Γ}
    {clause : Clause D Γ}
    (hMember : clause ∈ clauses) :
    Assertion.entails
      clauses.denote clause.eval :=
  Candidate.denote_entails_of_mem hMember

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Semantic Loop Obligations
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema) :
    assertion.Init P =
      Assertion.entails
        P.loopPre.eval assertion :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema) :
    assertion.Term P =
      Assertion.entails
        (Assertion.andNotGuard
          assertion P.loopGuard)
        P.loopPost.eval :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (active target : Assertion D P.outSchema) :
    active.Step P target =
      Assertion.entails
        (Assertion.andGuard active P.loopGuard)
        (Hoare.wp P.loopBody target) :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema) :
    assertion.Maint P =
      assertion.Step P assertion :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema) :
    assertion.IsInductiveFor P =
      (assertion.Init P ∧ assertion.Maint P) :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema) :
    assertion.IsSufficientFor P =
      (assertion.IsInductiveFor P ∧
        assertion.Term P) :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : Candidate D P.outSchema) :
    clauses.IsInductiveFor P =
      clauses.denote.IsInductiveFor P :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : Candidate D P.outSchema) :
    clauses.IsSufficientFor P =
      clauses.denote.IsSufficientFor P :=
  rfl

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Member-Wise and Congruence Laws
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : Candidate D P.outSchema) :
    clauses.denote.Init P ↔
      ∀ clause ∈ clauses,
        Assertion.Init P clause.eval :=
  Candidate.init_denote_iff P clauses

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (active : Assertion D P.outSchema)
    (clauses : Candidate D P.outSchema) :
    active.Step P clauses.denote ↔
      ∀ clause ∈ clauses,
        active.Step P clause.eval :=
  Candidate.step_denote_iff P active clauses

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : Candidate D P.outSchema) :
    clauses.denote.Maint P ↔
      ∀ clause ∈ clauses,
        clauses.denote.Step
          P clause.eval :=
  Candidate.maint_denote_iff P clauses

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    {assertion assertion' : Assertion D P.outSchema}
    (hEquiv :
      Assertion.equiv assertion assertion') :
    assertion.IsSufficientFor P ↔
      assertion'.IsSufficientFor P :=
  Assertion.isSufficientFor_congr P hEquiv

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Readable List Materialization
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

example :
    ClauseObligation.materialize
      ([] : List (Clause D Γ)) =
        QFAssertExpr.«true» :=
  rfl

example
    (clause : Clause D Γ) :
    ClauseObligation.materialize [clause] =
      clause :=
  rfl

example
    (left right : Clause D Γ) :
    ([left, right] :
      List (Clause D Γ)).toFinset =
        ([right, left] :
          List (Clause D Γ)).toFinset := by
  simp [Finset.ext_iff, or_comm]

example
    (clause : Clause D Γ) :
    ([clause, clause] :
      List (Clause D Γ)).toFinset =
        ([clause] :
          List (Clause D Γ)).toFinset := by
  simp

example
    (clauses : List (Clause D Γ))
    (I : Instance D Γ) :
    (ClauseObligation.materialize clauses).eval I ↔
      Candidate.denote clauses.toFinset I :=
  ClauseObligation.materialize_eval_iff_denote
    clauses I

example
    (left right : Clause D Γ) :
    QFAssertExpr.equiv
      (ClauseObligation.materialize [left, right])
      (ClauseObligation.materialize
        [right, left]) := by
  apply
    ClauseObligation.materialize_equiv_of_toFinset_eq
  simp [Finset.ext_iff, or_comm]

example
    (clause : Clause D Γ) :
    QFAssertExpr.equiv
      (ClauseObligation.materialize
        [clause, clause])
      (ClauseObligation.materialize [clause]) := by
  apply
    ClauseObligation.materialize_equiv_of_toFinset_eq
  simp

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- QF Obligation Correspondence
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (target : Clause D P.outSchema) :
    ClauseObligation.init P target =
      QFInvariantObligation.init
        P.loopPre P.loopPre_noBound target :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (active : List (Clause D P.outSchema))
    (target : Clause D P.outSchema) :
    ClauseObligation.step P active target =
      QFInvariantObligation.step
        (ClauseObligation.materialize active)
        target P.loopGuard P.loopBody
        P.loopBody_loopFree :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (active : List (Clause D P.outSchema)) :
    ClauseObligation.initCandidate P active =
      QFInvariantObligation.init
        P.loopPre P.loopPre_noBound
        (ClauseObligation.materialize active) :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (active : List (Clause D P.outSchema)) :
    ClauseObligation.maintCandidate P active =
      QFInvariantObligation.step
        (ClauseObligation.materialize active)
        (ClauseObligation.materialize active)
        P.loopGuard P.loopBody
        P.loopBody_loopFree :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (active : List (Clause D P.outSchema)) :
    ClauseObligation.termCandidate P active =
      QFInvariantObligation.term
        (ClauseObligation.materialize active)
        P.loopPost P.loopPost_noBound
        P.loopGuard :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (target : Clause D P.outSchema) :
    (ClauseObligation.init P target).Valid ↔
      Assertion.Init P target.eval :=
  ClauseObligation.init_valid_iff P target

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (active : List (Clause D P.outSchema)) :
    (ClauseObligation.initCandidate P active).Valid ↔
      Assertion.Init P
        (Candidate.denote active.toFinset) :=
  ClauseObligation.initCandidate_valid_iff P active

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (active : List (Clause D P.outSchema))
    (target : Clause D P.outSchema) :
    (ClauseObligation.step P active target).Valid ↔
      Assertion.Step P
        (Candidate.denote active.toFinset)
        target.eval :=
  ClauseObligation.step_valid_iff
    P active target

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (active : List (Clause D P.outSchema)) :
    (ClauseObligation.maintCandidate
      P active).Valid ↔
      Assertion.Maint P
        (Candidate.denote active.toFinset) :=
  ClauseObligation.maintCandidate_valid_iff
    P active

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (active : List (Clause D P.outSchema)) :
    (ClauseObligation.termCandidate
      P active).Valid ↔
      Assertion.Term P
        (Candidate.denote active.toFinset) :=
  ClauseObligation.termCandidate_valid_iff
    P active

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Source Soundness
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema)
    (hSufficient :
      assertion.IsSufficientFor P) :
    HoareValid inputPre inputCmd inputPost :=
  P.valid_of_sufficient assertion hSufficient

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : Candidate D P.outSchema)
    (hSufficient :
      clauses.IsSufficientFor P) :
    HoareValid inputPre inputCmd inputPost :=
  P.valid_of_sufficient
    clauses.denote hSufficient

end Tests

end Synthesis

end Whiel
