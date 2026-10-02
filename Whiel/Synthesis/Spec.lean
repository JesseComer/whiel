-- Author: Jesse Comer
import Whiel.Hoare.Preproc

/-
  Class-agnostic semantics for symbolic synthesis.

  A clause is a quantifier-free assertion. A slice is a
  finite subset of a clause class. A candidate is a finite
  set of clauses interpreted as their conjunction. Clause
  classes and enumeration strategies are specified in
  separate modules.
-/

------------------------------------------------------------
-- Clauses, Classes, Slices, and Candidates
------------------------------------------------------------

namespace Whiel

namespace Synthesis

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- A symbolic clause is a quantifier-free assertion. -/
abbrev Clause
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) :=
  QFAssertExpr D Γ

/- A clause class is a set of symbolic clauses. -/
abbrev ClauseClass
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) :=
  Set (Clause D Γ)

namespace Clause

/-
  QF clauses have executable equality through their
  injective erasure to raw guard syntax.
-/
instance instDecidableEq :
    DecidableEq (Clause D Γ) :=
  Function.Injective.decidableEq
    (fun _ _ h => Guard.eq_of_toRaw_eq h)

end Clause

namespace ClauseClass

/- A slice is an extensional finite subset of one class. -/
structure Slice
    (clauseClass : ClauseClass D Γ) where
  clauses : Set (Clause D Γ)
  finite : clauses.Finite
  subset_class :
    ∀ clause ∈ clauses, clause ∈ clauseClass

namespace Slice

/- Every member of a slice belongs to its class. -/
theorem mem_class
    {clauseClass : ClauseClass D Γ}
    (slice : clauseClass.Slice)
    {clause : Clause D Γ}
    (hMember : clause ∈ slice.clauses) :
    clause ∈ clauseClass :=
  slice.subset_class clause hMember

end Slice

end ClauseClass

/-
  A candidate is an arbitrary finite set of symbolic clauses.
  Initialization, maintenance, and runtime membership are
  external to this type.
-/
abbrev Candidate
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) :=
  Finset (Clause D Γ)

namespace Candidate

/- A candidate denotes the conjunction of its clauses. -/
def denote
    (clauses : Candidate D Γ) :
    Assertion D Γ :=
  fun I =>
    ∀ clause ∈ clauses, clause.eval I

@[simp] theorem denote_apply_iff
    (clauses : Candidate D Γ)
    (I : Instance D Γ) :
    clauses.denote I ↔
      ∀ clause ∈ clauses, clause.eval I :=
  Iff.rfl

/- A candidate entails each of its member clauses. -/
theorem denote_entails_of_mem
    {clauses : Candidate D Γ}
    {clause : Clause D Γ}
    (hMember : clause ∈ clauses) :
    Assertion.entails clauses.denote clause.eval := by
  intro I hClauses
  exact hClauses clause hMember

end Candidate

end Synthesis

end Whiel

------------------------------------------------------------
-- Semantic Loop Obligations
------------------------------------------------------------

namespace Whiel

namespace Assertion

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- The loop precondition establishes an assertion. -/
def Init
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema) :
    Prop :=
  Whiel.Assertion.entails P.loopPre.eval assertion

/- One antecedent assertion maintains one target assertion. -/
def Step
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (antecedent : Assertion D P.outSchema)
    (target : Assertion D P.outSchema) :
    Prop :=
  Whiel.Assertion.entails
    (Whiel.Assertion.andGuard antecedent P.loopGuard)
    (Hoare.wp P.loopBody target)

/- An assertion is maintained by itself. -/
def Maint
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema) :
    Prop :=
  assertion.Step P assertion

/- An assertion satisfies initialization and maintenance. -/
def IsInductiveFor
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema) :
    Prop :=
  assertion.Init P ∧ assertion.Maint P

/- Loop exit establishes the postcondition. -/
def Term
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema) :
    Prop :=
  Whiel.Assertion.entails
    (Whiel.Assertion.andNotGuard
      assertion P.loopGuard)
    P.loopPost.eval

/- Sufficiency packages all three loop obligations. -/
def IsSufficientFor
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema) :
    Prop :=
  assertion.IsInductiveFor P ∧ assertion.Term P

end Assertion

namespace Synthesis

namespace Candidate

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- A candidate is inductive when its denotation is. -/
def IsInductiveFor
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : Candidate D P.outSchema) :
    Prop :=
  clauses.denote.IsInductiveFor P

/- A candidate is sufficient when its denotation is. -/
def IsSufficientFor
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : Candidate D P.outSchema) :
    Prop :=
  clauses.denote.IsSufficientFor P

end Candidate

end Synthesis

end Whiel

------------------------------------------------------------
-- Member-Wise Candidate Laws
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Candidate

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- Candidate initialization holds exactly member-wise. -/
theorem init_denote_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : Candidate D P.outSchema) :
    clauses.denote.Init P ↔
      ∀ clause ∈ clauses,
        Whiel.Assertion.Init P clause.eval := by
  constructor
  · intro hInit clause hMember I hPre
    exact hInit I hPre clause hMember
  · intro hInit I hPre clause hMember
    exact hInit clause hMember I hPre

/- A step into a candidate holds exactly member-wise. -/
theorem step_denote_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (antecedent : Assertion D P.outSchema)
    (clauses : Candidate D P.outSchema) :
    antecedent.Step P clauses.denote ↔
      ∀ clause ∈ clauses,
        antecedent.Step P clause.eval := by
  constructor
  · intro hStep clause hMember I hGuarded J hBody
    exact hStep I hGuarded J hBody clause hMember
  · intro hStep I hGuarded J hBody clause hMember
    exact hStep clause hMember I hGuarded J hBody

/- Candidate maintenance holds exactly member-wise. -/
theorem maint_denote_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : Candidate D P.outSchema) :
    clauses.denote.Maint P ↔
      ∀ clause ∈ clauses,
        clauses.denote.Step P clause.eval := by
  exact step_denote_iff P clauses.denote clauses

end Candidate

end Synthesis

end Whiel

------------------------------------------------------------
-- Semantic Equivalence Congruence
------------------------------------------------------------

namespace Whiel

namespace Assertion

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- Initialization respects assertion equivalence. -/
theorem init_congr
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    {assertion assertion' : Assertion D P.outSchema}
    (hEquiv :
      Whiel.Assertion.equiv assertion assertion') :
    assertion.Init P ↔ assertion'.Init P := by
  constructor
  · intro hInit I hPre
    exact hEquiv.1 I (hInit I hPre)
  · intro hInit I hPre
    exact hEquiv.2 I (hInit I hPre)

/- Step respects antecedent and target equivalence. -/
theorem step_congr
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    {antecedent antecedent' target target' :
      Assertion D P.outSchema}
    (hAntecedent :
      Whiel.Assertion.equiv antecedent antecedent')
    (hTarget :
      Whiel.Assertion.equiv target target') :
    antecedent.Step P target ↔
      antecedent'.Step P target' := by
  constructor
  · intro hStep I hGuarded
    have hWp :=
      hStep I
        ⟨hAntecedent.2 I hGuarded.1,
          hGuarded.2⟩
    exact
      (Hoare.wp_mono P.loopBody hTarget.1) I hWp
  · intro hStep I hGuarded
    have hWp :=
      hStep I
        ⟨hAntecedent.1 I hGuarded.1,
          hGuarded.2⟩
    exact
      (Hoare.wp_mono P.loopBody hTarget.2) I hWp

/- Maintenance respects assertion equivalence. -/
theorem maint_congr
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    {assertion assertion' : Assertion D P.outSchema}
    (hEquiv :
      Whiel.Assertion.equiv assertion assertion') :
    assertion.Maint P ↔ assertion'.Maint P :=
  step_congr P hEquiv hEquiv

/- Inductiveness respects assertion equivalence. -/
theorem isInductiveFor_congr
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    {assertion assertion' : Assertion D P.outSchema}
    (hEquiv :
      Whiel.Assertion.equiv assertion assertion') :
    assertion.IsInductiveFor P ↔
      assertion'.IsInductiveFor P := by
  constructor
  · rintro ⟨hInit, hMaint⟩
    exact
      ⟨(init_congr P hEquiv).mp hInit,
        (maint_congr P hEquiv).mp hMaint⟩
  · rintro ⟨hInit, hMaint⟩
    exact
      ⟨(init_congr P hEquiv).mpr hInit,
        (maint_congr P hEquiv).mpr hMaint⟩

/- Termination respects assertion equivalence. -/
theorem term_congr
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    {assertion assertion' : Assertion D P.outSchema}
    (hEquiv :
      Whiel.Assertion.equiv assertion assertion') :
    assertion.Term P ↔ assertion'.Term P := by
  constructor
  · intro hTerm I hExit
    exact
      hTerm I
        ⟨hEquiv.2 I hExit.1, hExit.2⟩
  · intro hTerm I hExit
    exact
      hTerm I
        ⟨hEquiv.1 I hExit.1, hExit.2⟩

/- Sufficiency respects assertion equivalence. -/
theorem isSufficientFor_congr
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    {assertion assertion' : Assertion D P.outSchema}
    (hEquiv :
      Whiel.Assertion.equiv assertion assertion') :
    assertion.IsSufficientFor P ↔
      assertion'.IsSufficientFor P := by
  constructor
  · rintro ⟨hInductive, hTerm⟩
    exact
      ⟨(isInductiveFor_congr P hEquiv).mp
          hInductive,
        (term_congr P hEquiv).mp hTerm⟩
  · rintro ⟨hInductive, hTerm⟩
    exact
      ⟨(isInductiveFor_congr P hEquiv).mpr
          hInductive,
        (term_congr P hEquiv).mpr hTerm⟩

end Assertion

end Whiel

------------------------------------------------------------
-- Source Hoare Soundness
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace Preproc

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- Sufficiency proves the normalized loop-only triple. -/
theorem loopValid_of_sufficient
    (P : Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema)
    (hSufficient : assertion.IsSufficientFor P) :
    HoareValid P.loopPre P.loopCmd P.loopPost := by
  exact
    Hoare.hoareValid_while_of_vcs
      hSufficient.1.1
      hSufficient.1.2
      hSufficient.2

/- Sufficiency proves the original source Hoare triple. -/
theorem valid_of_sufficient
    (P : Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema)
    (hSufficient : assertion.IsSufficientFor P) :
    HoareValid inputPre inputCmd inputPost :=
  P.valid_input
    (P.loopValid_of_sufficient
      assertion hSufficient)

end Preproc

end Hoare

end Whiel
