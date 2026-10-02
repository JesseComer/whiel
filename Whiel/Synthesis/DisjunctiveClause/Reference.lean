-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.CanonicalEnumeration

/-
  Parameter growth for the readable disjunctive-clause
  reference enumerator.

  This module defines the parameter order, canonical
  all-enabled schedule, and pure executable proposal
  boundary. `Coverage.lean` proves eventual coverage.

  Main declarations:
    * `Parameters.Dominates`
    * `ParameterSchedule.IsCofinal`
    * `referenceParameters`
    * `referenceParameters_isCofinal`
    * `proposalFor` and `referenceProposal`
-/

------------------------------------------------------------
-- Parameter Domination
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace Parameters

/-
  The larger parameter choice enables every choice and
  bound enabled by the smaller parameter choice.
-/
def Dominates
    (larger smaller : Parameters) : Prop :=
  smaller.enabledRABases ⊆ larger.enabledRABases ∧
    smaller.enabledRAOperators ⊆
      larger.enabledRAOperators ∧
    smaller.enabledAtomKinds ⊆
      larger.enabledAtomKinds ∧
    smaller.enabledLiteralSigns ⊆
      larger.enabledLiteralSigns ∧
    smaller.maxRAOps ≤ larger.maxRAOps ∧
    smaller.maxSelectionConditionNodes ≤
      larger.maxSelectionConditionNodes ∧
    smaller.maxProjectionExcess ≤
      larger.maxProjectionExcess ∧
    smaller.maxOutputArity ≤
      larger.maxOutputArity ∧
    smaller.maxClauseWidth ≤
      larger.maxClauseWidth

@[refl] theorem dominates_refl
    (parameters : Parameters) :
    parameters.Dominates parameters := by
  simp [Dominates]

@[trans] theorem dominates_trans
    {largest middle smallest : Parameters}
    (hLargest : largest.Dominates middle)
    (hMiddle : middle.Dominates smallest) :
    largest.Dominates smallest := by
  rcases hLargest with
    ⟨hBases₁, hOperators₁, hAtoms₁, hSigns₁,
      hRA₁, hSelection₁, hProjection₁,
      hOutput₁, hWidth₁⟩
  rcases hMiddle with
    ⟨hBases₂, hOperators₂, hAtoms₂, hSigns₂,
      hRA₂, hSelection₂, hProjection₂,
      hOutput₂, hWidth₂⟩
  exact
    ⟨Finset.Subset.trans hBases₂ hBases₁,
      Finset.Subset.trans hOperators₂ hOperators₁,
      Finset.Subset.trans hAtoms₂ hAtoms₁,
      Finset.Subset.trans hSigns₂ hSigns₁,
      hRA₂.trans hRA₁,
      hSelection₂.trans hSelection₁,
      hProjection₂.trans hProjection₁,
      hOutput₂.trans hOutput₁,
      hWidth₂.trans hWidth₁⟩

end Parameters

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Eligibility Monotonicity
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

theorem SelectionCondition.IsEligible.mono
    {condition : Sel D}
    {inputArity : Nat}
    {alphabet : Alphabet D Γ}
    {larger smaller : Parameters}
    (hDominates : larger.Dominates smaller)
    (hEligible :
      SelectionCondition.IsEligible condition
        inputArity alphabet smaller) :
  SelectionCondition.IsEligible condition
      inputArity alphabet larger :=
  ⟨hEligible.1, hEligible.2.1,
    hEligible.2.2.trans hDominates.2.2.2.2.2.1⟩

theorem ProjectionList.IsEligible.mono
    {indices : List Nat}
    {inputArity : Nat}
    {larger smaller : Parameters}
    (hDominates : larger.Dominates smaller)
    (hEligible :
      ProjectionList.IsEligible indices inputArity
        smaller) :
  ProjectionList.IsEligible indices inputArity larger :=
  ⟨hEligible.1,
    hEligible.2.trans
      hDominates.2.2.2.2.2.2.1⟩

theorem Term.IsEligible.mono
    {term : Term D Γ}
    {alphabet : Alphabet D Γ}
    {larger smaller : Parameters}
    (hDominates : larger.Dominates smaller)
    (hEligible : term.IsEligible alphabet smaller) :
    term.IsEligible alphabet larger := by
  induction hEligible with
  | top hEnabled =>
      exact .top (hDominates.1 hEnabled)
  | empty arity hEnabled hArity =>
      apply Term.IsEligible.empty arity
        (hDominates.1 hEnabled)
      by_cases hRelationEnabled :
          RABase.relation ∈ smaller.enabledRABases
      · have hLargerRelation :
            RABase.relation ∈ larger.enabledRABases :=
          hDominates.1 hRelationEnabled
        simp only [emptyArities, Finset.mem_union,
          Finset.mem_range, relationArities,
          hRelationEnabled, hLargerRelation,
          if_true] at hArity ⊢
        rcases hArity with hExplicit | hRelation
        · exact Or.inl
            (Nat.lt_succ_iff.mpr
              ((Nat.lt_succ_iff.mp hExplicit).trans
                hDominates.2.2.2.2.2.2.2.1))
        · exact Or.inr hRelation
      · have hExplicit :
            arity < smaller.maxOutputArity + 1 := by
          have hRange :
              arity ∈ Finset.range
                (smaller.maxOutputArity + 1) := by
            simpa [emptyArities, relationArities,
              hRelationEnabled] using hArity
          exact Finset.mem_range.mp hRange
        rw [emptyArities]
        apply Finset.mem_union_left
        rw [Finset.mem_range, Nat.lt_succ_iff]
        exact
          (Nat.lt_succ_iff.mp hExplicit).trans
            hDominates.2.2.2.2.2.2.2.1
  | relation relation hEnabled hRelation =>
      exact .relation relation
        (hDominates.1 hEnabled) hRelation
  | singleton constant hEnabled hConstant =>
      exact .singleton constant
        (hDominates.1 hEnabled) hConstant
  | selection condition term _ hEnabled hCondition
      hOutput hCost ih =>
      exact .selection condition term ih
        (hDominates.2.1 hEnabled)
        (hCondition.mono hDominates)
        (hOutput.trans
          hDominates.2.2.2.2.2.2.2.1)
        (hCost.trans hDominates.2.2.2.2.1)
  | projection indices term _ hEnabled hIndices
      hOutput hCost ih =>
      exact .projection indices term ih
        (hDominates.2.1 hEnabled)
        (hIndices.mono hDominates)
        (hOutput.trans
          hDominates.2.2.2.2.2.2.2.1)
        (hCost.trans hDominates.2.2.2.2.1)
  | product left right _ _ hEnabled hOutput hCost
      ihLeft ihRight =>
      exact .product left right ihLeft ihRight
        (hDominates.2.1 hEnabled)
        (hOutput.trans
          hDominates.2.2.2.2.2.2.2.1)
        (hCost.trans hDominates.2.2.2.2.1)
  | union left right sameArity _ _ hEnabled hOutput
      hCost ihLeft ihRight =>
      exact .union left right sameArity ihLeft ihRight
        (hDominates.2.1 hEnabled)
        (hOutput.trans
          hDominates.2.2.2.2.2.2.2.1)
        (hCost.trans hDominates.2.2.2.2.1)
  | difference left right sameArity _ _ hEnabled
      hOutput hCost ihLeft ihRight =>
      exact .difference left right sameArity
        ihLeft ihRight (hDominates.2.1 hEnabled)
        (hOutput.trans
          hDominates.2.2.2.2.2.2.2.1)
        (hCost.trans hDominates.2.2.2.2.1)

theorem Atom.IsEligible.mono
    {atom : Atom D Γ}
    {alphabet : Alphabet D Γ}
    {larger smaller : Parameters}
    (hDominates : larger.Dominates smaller)
    (hEligible : atom.IsEligible alphabet smaller) :
    atom.IsEligible alphabet larger := by
  rcases hEligible with
    ⟨kind, hKind, left, hLeft, right, hRight,
      sameArity, rfl⟩
  exact
    ⟨kind, hDominates.2.2.1 hKind,
      left, hLeft.mono hDominates,
      right, hRight.mono hDominates,
      sameArity, rfl⟩

theorem Literal.IsEligible.mono
    {literal : Literal D Γ}
    {alphabet : Alphabet D Γ}
    {larger smaller : Parameters}
    (hDominates : larger.Dominates smaller)
    (hEligible : literal.IsEligible alphabet smaller) :
    literal.IsEligible alphabet larger :=
  ⟨hDominates.2.2.2.1 hEligible.1,
    hEligible.2.mono hDominates⟩

theorem LiteralList.IsEligible.mono
    {literalList : LiteralList D Γ}
    {alphabet : Alphabet D Γ}
    {larger smaller : Parameters}
    (hDominates : larger.Dominates smaller)
    (hEligible :
      literalList.IsEligible alphabet smaller) :
    literalList.IsEligible alphabet larger := by
  refine
    ⟨hEligible.1.trans
        hDominates.2.2.2.2.2.2.2.2,
      ?_⟩
  intro literal hLiteral
  exact (hEligible.2 literal hLiteral).mono hDominates

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Canonical Cofinal Schedule
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

/- Every relational-algebra base constructor. -/
def allRABases : Finset RABase :=
  {.top, .empty, .relation, .singleton}

/- Every non-base relational-algebra constructor. -/
def allRAOperators : Finset RAOperator :=
  {.selection, .projection, .product, .union, .difference}

/- Every atom kind. -/
def allAtomKinds : Finset AtomKind :=
  {.equality, .containment}

/- Every literal sign. -/
def allLiteralSigns : Finset LiteralSign :=
  {.positive, .negative}

/-
  The stage-`n` reference parameters enable every
  constructor and set every numeric bound to `n`.
-/
def referenceParameters
    (stage : Nat) : Parameters where
  enabledRABases := allRABases
  enabledRAOperators := allRAOperators
  enabledAtomKinds := allAtomKinds
  enabledLiteralSigns := allLiteralSigns
  maxRAOps := stage
  maxSelectionConditionNodes := stage
  maxProjectionExcess := stage
  maxOutputArity := stage
  maxClauseWidth := stage

/-
  A parameter schedule eventually dominates every choice.
-/
def ParameterSchedule.IsCofinal
    (schedule : Nat → Parameters) : Prop :=
  ∀ parameters, ∃ firstStage, ∀ stage,
    firstStage ≤ stage →
      (schedule stage).Dominates parameters

theorem referenceParameters_mono
    {smaller larger : Nat}
    (hStages : smaller ≤ larger) :
    (referenceParameters larger).Dominates
      (referenceParameters smaller) := by
  simp [Parameters.Dominates, referenceParameters,
    hStages]

/- The canonical all-enabled schedule is cofinal. -/
theorem referenceParameters_isCofinal :
    ParameterSchedule.IsCofinal referenceParameters := by
  intro parameters
  let firstStage :=
    parameters.maxRAOps +
      parameters.maxSelectionConditionNodes +
      parameters.maxProjectionExcess +
      parameters.maxOutputArity +
      parameters.maxClauseWidth
  refine ⟨firstStage, ?_⟩
  intro stage hStage
  simp only [Parameters.Dominates,
    referenceParameters]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro base _
    cases base <;> simp [allRABases]
  · intro operator _
    cases operator <;> simp [allRAOperators]
  · intro kind _
    cases kind <;> simp [allAtomKinds]
  · intro sign _
    cases sign <;> simp [allLiteralSigns]
  all_goals
    dsimp [firstStage] at hStage
    omega

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Executable Reference Proposal
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

open CanonicalEnumeration

/-
  Materialize the full readable enumerator at one parameter
  choice. The structural literal order comes from the
  ordered name and domain carriers. This is the pure Lean
  proposal boundary.
-/
def proposalFor
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Candidate D Γ :=
  CanonicalEnumeration.clauses alphabet parameters

/- Materialize the canonical proposal at one stage. -/
def referenceProposal
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    Candidate D Γ :=
  proposalFor alphabet (referenceParameters stage)

/- Every proposal formula belongs to the full slice. -/
theorem proposalFor_sound
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {formula : Clause D Γ}
    (hMember :
      formula ∈ proposalFor alphabet parameters) :
    formula ∈ (slice alphabet parameters).clauses := by
  rcases Finset.mem_image.mp hMember with
    ⟨representation, hRepresentation, rfl⟩
  exact
    CanonicalEnumeration.representations_sound
      alphabet parameters hRepresentation

/-
  Every full-slice formula has an equivalent formula in the
  canonical proposal.
-/
theorem proposalFor_complete_up_to_equiv
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (formula : Clause D Γ)
    (hMember :
      formula ∈ (slice alphabet parameters).clauses) :
    ∃ emitted ∈ proposalFor alphabet parameters,
      QFAssertExpr.equiv emitted formula := by
  rcases
      representations_complete_up_to_equiv
        alphabet parameters formula hMember with
    ⟨representation, hRepresentation, hEquiv⟩
  exact
    ⟨FullEnumeration.decode representation,
      Finset.mem_image.mpr
        ⟨representation, hRepresentation, rfl⟩,
      hEquiv⟩

/- Every materialized proposal member is in the class. -/
theorem proposalFor_subset_clauseClass
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    ∀ formula ∈ proposalFor alphabet parameters,
      formula ∈
        (clauseClass : ClauseClass D Γ) := by
  intro formula hMember
  exact
    (slice alphabet parameters).mem_class
      (proposalFor_sound
        alphabet parameters hMember)


------------------------------------------------------------
-- Proposal Monotonicity
------------------------------------------------------------

/- Canonical proposals grow under parameter domination. -/
theorem proposalFor_mono
    (alphabet : Alphabet D Γ)
    {smaller larger : Parameters}
    (hDominates : larger.Dominates smaller) :
    proposalFor alphabet smaller ⊆
      proposalFor alphabet larger := by
  intro formula hFormula
  rcases Finset.mem_image.mp hFormula with
    ⟨representation, hRepresentation, rfl⟩
  have hNormalized :=
    CanonicalEnumeration.representation_normalized
      alphabet smaller hRepresentation
  have hEligible :=
    CanonicalEnumeration.representation_eligible
      alphabet smaller hRepresentation
  have hLarger :
      CanonicalEnumeration.canonicalize representation ∈
        CanonicalEnumeration.representations
          alphabet larger :=
    CanonicalEnumeration.canonicalize_mem_representations
      alphabet larger representation hNormalized
        (hEligible.mono hDominates)
  have hCanonical :
      CanonicalEnumeration.canonicalize representation =
        representation :=
    (CanonicalEnumeration.canonicalize_sameLiterals
      representation hNormalized).eq_of_pairwise'
        (Finset.pairwise_sort _ _)
        (CanonicalEnumeration.representation_pairwise
          alphabet smaller hRepresentation)
  apply Finset.mem_image.mpr
  exact
    ⟨CanonicalEnumeration.canonicalize representation,
      hLarger, congrArg FullEnumeration.decode hCanonical⟩

/- Reference proposals grow with their stage. -/
theorem referenceProposal_mono
    (alphabet : Alphabet D Γ)
    {smaller larger : Nat}
    (hStages : smaller ≤ larger) :
    referenceProposal alphabet smaller ⊆
      referenceProposal alphabet larger := by
  exact proposalFor_mono alphabet
    (referenceParameters_mono hStages)

end DisjunctiveClause

end Synthesis

end Whiel
