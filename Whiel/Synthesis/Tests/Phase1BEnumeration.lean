-- Author: Jesse Comer
import Whiel.Concrete.Notation
import Whiel.Synthesis.DisjunctiveClause.Coverage

/-
  Focused checks for the full bounded clause grammar,
  readable finite enumerator, extensional slice, and
  canonical cofinal schedule.
-/

open Whiel.Concrete

namespace Whiel

namespace Synthesis

namespace Tests

namespace Phase1BEnumerationTests

open DisjunctiveClause
open DisjunctiveClause.FullEnumeration

------------------------------------------------------------
-- Small Enumeration Request
------------------------------------------------------------

def schema :
    UnnamedSchema IndexAlphaName :=
  whielSch![Unary (arity: 1), _ (arity: 0)]

def unaryRelation : schema.syms :=
  schema.sym (IndexAlphaName.baseString "Unary")

def constant : Data :=
  Data.num 0

def alphabet : Alphabet Data schema where
  relations := schema.syms.attach
  constants := {constant}

def parameters : Parameters where
  enabledRABases := allRABases
  enabledRAOperators := allRAOperators
  enabledAtomKinds := allAtomKinds
  enabledLiteralSigns := allLiteralSigns
  maxRAOps := 1
  maxSelectionConditionNodes := 1
  maxProjectionExcess := 1
  maxOutputArity := 2
  maxClauseWidth := 2

def zeroCostParameters : Parameters :=
  {parameters with maxRAOps := 0}

def emptyParameters : Parameters where
  enabledRABases := ∅
  enabledRAOperators := ∅
  enabledAtomKinds := ∅
  enabledLiteralSigns := ∅
  maxRAOps := 0
  maxSelectionConditionNodes := 0
  maxProjectionExcess := 0
  maxOutputArity := 0
  maxClauseWidth := 0

def noProjectionExcessParameters : Parameters :=
  {parameters with maxProjectionExcess := 0}

def singletonTerm : Term Data schema :=
  Term.singleton constant

def relationTerm : Term Data schema :=
  Term.relation unaryRelation

def selectionCondition : Sel Data :=
  Sel.eqConst 0 constant

def selectionTerm : Term Data schema :=
  Term.select selectionCondition singletonTerm (by
    simp [selectionCondition, singletonTerm,
      Term.singleton, Sel.arityReq])

def repeatedProjection : List Nat :=
  [0, 0]

def projectionTerm : Term Data schema :=
  Term.project repeatedProjection singletonTerm (by
    simp [repeatedProjection, singletonTerm,
      Term.singleton])

def emptyProjectionTerm : Term Data schema :=
  Term.project [] singletonTerm (by simp)

def productTerm : Term Data schema :=
  Term.product singletonTerm singletonTerm

def unionTerm : Term Data schema :=
  Term.union singletonTerm singletonTerm rfl

def differenceTerm : Term Data schema :=
  Term.difference singletonTerm singletonTerm rfl

------------------------------------------------------------
-- Conditions and Projection Lists
------------------------------------------------------------

example :
    SelectionCondition.nodeCount selectionCondition = 1 :=
  rfl

example :
    selectionCondition ∈
        selectionConditions 1 alphabet parameters ↔
      SelectionCondition.IsEligible
        selectionCondition 1 alphabet parameters :=
  mem_selectionConditions_iff
    1 alphabet parameters selectionCondition

example :
    repeatedProjection ∈
      projectionLists 1 parameters := by
  apply
    (mem_projectionLists_iff
      1 parameters repeatedProjection).mpr
  constructor
  · simp [repeatedProjection]
  · simp [ProjectionList.excess, repeatedProjection,
      parameters]

example :
    [0, 1] ∈
      projectionLists 2
        noProjectionExcessParameters := by
  apply
    (mem_projectionLists_iff 2
      noProjectionExcessParameters [0, 1]).mpr
  simp [ProjectionList.IsEligible,
    ProjectionList.excess,
    noProjectionExcessParameters]

example :
    [0, 1, 0] ∉
      projectionLists 2
        noProjectionExcessParameters := by
  rw [mem_projectionLists_iff]
  simp [ProjectionList.IsEligible,
    ProjectionList.excess,
    noProjectionExcessParameters]

example :
    ([] : List Nat) ∈ projectionLists 1 parameters := by
  apply
    (mem_projectionLists_iff
      1 parameters []).mpr
  simp [ProjectionList.IsEligible,
    ProjectionList.excess]

------------------------------------------------------------
-- Every Relational-Algebra Constructor
------------------------------------------------------------

theorem singletonTerm_eligible :
    singletonTerm.IsEligible alphabet parameters := by
  apply Term.IsEligible.singleton constant
  · simp [parameters, allRABases]
  · simp [alphabet, constant]

theorem relationTerm_eligible :
    relationTerm.IsEligible alphabet parameters := by
  apply Term.IsEligible.relation unaryRelation
  · simp [parameters, allRABases]
  · simp [alphabet]

theorem selectionTerm_eligible :
    selectionTerm.IsEligible alphabet parameters := by
  apply Term.IsEligible.selection
      selectionCondition singletonTerm
      singletonTerm_eligible
  · simp [parameters, allRAOperators]
  · exact
      ⟨by simp [selectionCondition, singletonTerm,
          Term.singleton, Sel.arityReq],
      by simp [selectionCondition, Sel.constants,
        alphabet, constant],
      by simp [selectionCondition, parameters]⟩
  · simp [singletonTerm, Term.singleton, parameters]
  · change
      1 + Term.raCost
        (Term.singleton constant : Term Data schema) ≤ 1
    simp

theorem projectionTerm_eligible :
    projectionTerm.IsEligible alphabet parameters := by
  apply Term.IsEligible.projection
      repeatedProjection singletonTerm
      singletonTerm_eligible
  · simp [parameters, allRAOperators]
  · exact
      ⟨by simp [repeatedProjection, singletonTerm,
          Term.singleton],
      by simp [ProjectionList.excess,
        repeatedProjection, singletonTerm,
        Term.singleton, parameters]⟩
  · simp [repeatedProjection, parameters]
  · change
      1 + Term.raCost
        (Term.singleton constant : Term Data schema) ≤ 1
    simp

theorem emptyProjectionTerm_eligible :
    emptyProjectionTerm.IsEligible alphabet parameters := by
  apply Term.IsEligible.projection
      [] singletonTerm singletonTerm_eligible
  · simp [parameters, allRAOperators]
  · simp [ProjectionList.IsEligible,
      ProjectionList.excess, parameters]
  · simp [parameters]
  · change
      1 + Term.raCost
        (Term.singleton constant : Term Data schema) ≤ 1
    simp

theorem productTerm_eligible :
    productTerm.IsEligible alphabet parameters := by
  apply Term.IsEligible.product
      singletonTerm singletonTerm
      singletonTerm_eligible singletonTerm_eligible
  · simp [parameters, allRAOperators]
  · simp [singletonTerm, Term.singleton, parameters]
  · change
      1 + Term.raCost
          (Term.singleton constant : Term Data schema) +
        Term.raCost
          (Term.singleton constant : Term Data schema) ≤ 1
    simp

theorem unionTerm_eligible :
    unionTerm.IsEligible alphabet parameters := by
  apply Term.IsEligible.union
      singletonTerm singletonTerm rfl
      singletonTerm_eligible singletonTerm_eligible
  · simp [parameters, allRAOperators]
  · simp [singletonTerm, Term.singleton, parameters]
  · change
      1 + Term.raCost
          (Term.singleton constant : Term Data schema) +
        Term.raCost
          (Term.singleton constant : Term Data schema) ≤ 1
    simp

theorem differenceTerm_eligible :
    differenceTerm.IsEligible alphabet parameters := by
  apply Term.IsEligible.difference
      singletonTerm singletonTerm rfl
      singletonTerm_eligible singletonTerm_eligible
  · simp [parameters, allRAOperators]
  · simp [singletonTerm, Term.singleton, parameters]
  · change
      1 + Term.raCost
          (Term.singleton constant : Term Data schema) +
        Term.raCost
          (Term.singleton constant : Term Data schema) ≤ 1
    simp

theorem topTerm_eligible :
    (Term.top : Term Data schema).IsEligible
      alphabet parameters := by
  apply Term.IsEligible.top
  simp [parameters, allRABases]

theorem emptyTerm_eligible :
    (Term.empty 2 : Term Data schema).IsEligible
      alphabet parameters := by
  apply Term.IsEligible.empty 2
  · simp [parameters, allRABases]
  · simp [emptyArities, parameters]

example :
    (Term.top : Term Data schema) ∈
      terms alphabet parameters :=
  (mem_terms_iff alphabet parameters Term.top).mpr
    topTerm_eligible

example :
    (Term.empty 2 : Term Data schema) ∈
      terms alphabet parameters :=
  (mem_terms_iff
    alphabet parameters (Term.empty 2)).mpr
      emptyTerm_eligible

example :
    singletonTerm ∈ terms alphabet parameters :=
  (mem_terms_iff alphabet parameters singletonTerm).mpr
    singletonTerm_eligible

example :
    relationTerm ∈ terms alphabet parameters :=
  (mem_terms_iff alphabet parameters relationTerm).mpr
    relationTerm_eligible

example :
    selectionTerm ∈ terms alphabet parameters :=
  (mem_terms_iff alphabet parameters selectionTerm).mpr
    selectionTerm_eligible

example :
    projectionTerm ∈ terms alphabet parameters :=
  (mem_terms_iff alphabet parameters projectionTerm).mpr
    projectionTerm_eligible

example :
    emptyProjectionTerm ∈ terms alphabet parameters :=
  (mem_terms_iff
    alphabet parameters emptyProjectionTerm).mpr
      emptyProjectionTerm_eligible

example :
    productTerm ∈ terms alphabet parameters :=
  (mem_terms_iff alphabet parameters productTerm).mpr
    productTerm_eligible

example :
    unionTerm ∈ terms alphabet parameters :=
  (mem_terms_iff alphabet parameters unionTerm).mpr
    unionTerm_eligible

example :
    differenceTerm ∈ terms alphabet parameters :=
  (mem_terms_iff alphabet parameters differenceTerm).mpr
    differenceTerm_eligible

example
    (term : Term Data schema) :
    term ∈ terms alphabet parameters ↔
      term.IsEligible alphabet parameters :=
  mem_terms_iff alphabet parameters term

------------------------------------------------------------
-- Representations and Full-Slice Correspondence
------------------------------------------------------------

def equalityAtom : Atom Data schema :=
  Atom.ofTerms .equality selectionTerm selectionTerm rfl

def positiveLiteral : Literal Data schema where
  sign := .positive
  atom := equalityAtom

def negativeLiteral : Literal Data schema where
  sign := .negative
  atom := equalityAtom

def orderSmokeParameters : Parameters where
  enabledRABases := {.top}
  enabledRAOperators := ∅
  enabledAtomKinds := {.equality}
  enabledLiteralSigns := {.positive, .negative}
  maxRAOps := 0
  maxSelectionConditionNodes := 0
  maxProjectionExcess := 0
  maxOutputArity := 0
  maxClauseWidth := 1

/- Distinct literals use the derived structural order. -/
def structuralOrderSmoke : Bool :=
  letI : LinearOrder (Literal Data schema) :=
    DisjunctiveClause.StructuralOrder.literalLinearOrder
  decide (positiveLiteral < negativeLiteral)

example : structuralOrderSmoke = Bool.true := by
  decide

/- A nonempty proposal executes sorting and enumeration. -/
set_option linter.hashCommand false in
#guard
  (proposalFor alphabet orderSmokeParameters).card == 3

def representation : LiteralList Data schema :=
  [positiveLiteral]

theorem equalityAtom_eligible :
    equalityAtom.IsEligible alphabet parameters := by
  exact
    ⟨.equality, by simp [parameters, allAtomKinds],
      selectionTerm, selectionTerm_eligible,
      selectionTerm, selectionTerm_eligible,
      rfl, rfl⟩

theorem positiveLiteral_eligible :
    positiveLiteral.IsEligible alphabet parameters := by
  exact
    ⟨by simp [positiveLiteral, parameters,
        allLiteralSigns],
      equalityAtom_eligible⟩

theorem testRepresentation_normalized :
    representation.IsNormalized := by
  simp [representation, LiteralList.IsNormalized]

theorem testRepresentation_eligible :
    representation.IsEligible alphabet parameters := by
  constructor
  · simp [representation, parameters]
  · intro literal hLiteral
    simp only [representation, List.mem_singleton]
      at hLiteral
    subst literal
    exact positiveLiteral_eligible

section

variable (requestAlphabet : Alphabet Data schema)
variable (requestParameters : Parameters)

example
    (atom : Atom Data schema) :
    atom ∈ atoms requestAlphabet requestParameters ↔
      atom.IsEligible requestAlphabet requestParameters :=
  mem_atoms_iff requestAlphabet requestParameters atom

example
    (literal : Literal Data schema) :
    literal ∈
        literals requestAlphabet requestParameters ↔
      literal.IsEligible requestAlphabet
        requestParameters :=
  mem_literals_iff
    requestAlphabet requestParameters literal

example
    (literalList : LiteralList Data schema) :
    literalList ∈
        representations requestAlphabet
          requestParameters ↔
      literalList.IsNormalized ∧
        literalList.IsEligible requestAlphabet
          requestParameters :=
  mem_representations_iff
    requestAlphabet requestParameters literalList

example
    (literalList : LiteralList Data schema)
    (hNormalized : literalList.IsNormalized)
    (hEligible :
      literalList.IsEligible requestAlphabet
        requestParameters) :
    literalList ∈
      representations requestAlphabet requestParameters :=
  representations_cover requestAlphabet requestParameters
    literalList hNormalized hEligible

example
    {literalList : LiteralList Data schema}
    (hMember :
      literalList ∈
        representations requestAlphabet
          requestParameters) :
    literalList.IsNormalized :=
  FullEnumeration.representation_normalized
    requestAlphabet requestParameters hMember

example
    {literalList : LiteralList Data schema}
    (hMember :
      literalList ∈
        representations requestAlphabet
          requestParameters) :
    literalList.IsEligible requestAlphabet
      requestParameters :=
  FullEnumeration.representation_eligible
    requestAlphabet requestParameters hMember

example
    {literalList : LiteralList Data schema}
    (hMember :
      literalList ∈
        representations requestAlphabet
          requestParameters) :
    decode literalList ∈
      (slice requestAlphabet requestParameters).clauses :=
  representations_sound
    requestAlphabet requestParameters hMember

example
    (formula : Clause Data schema) :
    formula ∈
        (slice requestAlphabet
          requestParameters).clauses ↔
      ∃ literalList : LiteralList Data schema,
        literalList.IsNormalized ∧
          literalList.IsEligible requestAlphabet
            requestParameters ∧
          literalList.formula = formula :=
  mem_slice_iff requestAlphabet requestParameters formula

example
    (formula : Clause Data schema)
    (hMember :
      formula ∈
        (slice requestAlphabet requestParameters).clauses) :
    ∃ emitted ∈
        representations requestAlphabet requestParameters,
      decode emitted = formula :=
  representations_complete
    requestAlphabet requestParameters formula hMember

end

------------------------------------------------------------
-- Base-Slice Compatibility and Schedule
------------------------------------------------------------

example :
    (baseSlice alphabet parameters).clauses ⊆
      (slice alphabet parameters).clauses :=
  baseSlice_subset_slice alphabet parameters

example :
    slice alphabet zeroCostParameters =
      baseSlice alphabet zeroCostParameters :=
  slice_eq_baseSlice_of_maxRAOps_eq_zero
    alphabet zeroCostParameters rfl

example :
    ParameterSchedule.IsCofinal referenceParameters :=
  referenceParameters_isCofinal

example :
    (referenceParameters 2).Dominates parameters := by
  simp [Parameters.Dominates, referenceParameters,
    parameters, allRABases, allRAOperators,
    allAtomKinds, allLiteralSigns]

------------------------------------------------------------
-- Eventual Proposal Coverage
------------------------------------------------------------

section

open CanonicalEnumeration in
example
    (requestAlphabet : Alphabet Data schema)
    (requestParameters : Parameters)
    {left right : LiteralList Data schema}
    (hLeft :
      left ∈ CanonicalEnumeration.representations
        requestAlphabet requestParameters)
    (hRight :
      right ∈ CanonicalEnumeration.representations
        requestAlphabet requestParameters) :
    left.SameLiterals right ↔ left = right :=
  sameLiterals_iff_eq_of_mem_representations
      requestAlphabet requestParameters hLeft hRight

example
    (requestAlphabet : Alphabet Data schema)
    (requestParameters : Parameters)
    (formula : Clause Data schema)
    (hMember :
      formula ∈
        (slice requestAlphabet requestParameters).clauses) :
    ∃ emitted ∈
        CanonicalEnumeration.representations
          requestAlphabet requestParameters,
      QFAssertExpr.equiv
        (FullEnumeration.decode emitted) formula :=
  CanonicalEnumeration.representations_complete_up_to_equiv
      requestAlphabet requestParameters formula hMember

example
    (input : QFAssertExpr Data schema)
    (requestParameters : Parameters)
    (hEligible :
      ∀ clause ∈ CNF.clauses input,
        clause.IsEligible alphabet requestParameters) :
    CNF.canonicalCandidate input ⊆
      proposalFor alphabet requestParameters :=
  CNF.canonicalCandidate_subset_proposalFor
    input alphabet requestParameters hEligible

example
    (input : QFAssertExpr Data schema)
    (hConstants :
      input.constants ⊆ alphabet.constants) :
    ∃ firstStage, ∀ stage,
      firstStage ≤ stage →
        CNF.canonicalCandidate input ⊆
          referenceProposal alphabet stage := by
  apply
    CNF.eventually_canonical_subset_referenceProposal
  · simp [alphabet]
  · exact hConstants

example
    (input : QFAssertExpr Data schema)
    (schedule : Nat → Parameters)
    (hCofinal :
      ParameterSchedule.IsCofinal schedule)
    (hConstants :
      input.constants ⊆ alphabet.constants) :
    ∃ firstStage, ∀ stage,
      firstStage ≤ stage →
        CNF.canonicalCandidate input ⊆
          proposalFor alphabet (schedule stage) := by
  apply
    CNF.eventually_canonical_subset_proposalFor
  · exact hCofinal
  · simp [alphabet]
  · exact hConstants

section

variable {B E : Type}
variable [RelationNameSupply B] [Domain E]
variable [LinearOrder B] [LinearOrder E]
variable {Δ : UnnamedSchema B}
variable {pre post : AssertExpr E Δ}
variable {command : Cmd E Δ}

example
    (P : Hoare.Preproc pre command post)
    (witness : QFAssertExpr E P.outSchema)
    (hInductive :
      Assertion.IsInductiveFor P witness.eval)
    {clause : Clause E P.outSchema}
    (hMember :
      clause ∈ CNF.canonicalCandidate witness) :
    Assertion.Init P clause.eval :=
  CNF.canonicalCandidate_member_init_of_inductive
    P witness hInductive hMember

example
    (P : Hoare.Preproc pre command post)
    (witness : QFAssertExpr E P.outSchema)
    (hInductive :
      Assertion.IsInductiveFor P witness.eval) :
    (CNF.canonicalCandidate witness).denote.Maint P :=
  CNF.canonicalCandidate_maint_of_inductive
    P witness hInductive

example
    (P : Hoare.Preproc pre command post)
    (witness : QFAssertExpr E P.outSchema)
    (hSufficient :
      Assertion.IsSufficientFor P witness.eval) :
    (CNF.canonicalCandidate witness).denote.Term P :=
  CNF.canonicalCandidate_term_of_sufficient
    P witness hSufficient

example
    (P : Hoare.Preproc pre command post)
    (witness : QFAssertExpr E P.outSchema)
    (hSufficient :
      Assertion.IsSufficientFor P witness.eval) :
    (∀ clause ∈ CNF.canonicalCandidate witness,
        Assertion.Init P clause.eval) ∧
      (CNF.canonicalCandidate witness).denote.Maint P ∧
      (CNF.canonicalCandidate witness).denote.Term P :=
  CNF.canonicalCandidate_obligations_of_sufficient
    P witness hSufficient

example
    (P : Hoare.Preproc pre command post)
    (witness : QFAssertExpr E P.outSchema)
    (schedule : Nat → Parameters)
    (hCofinal :
      ParameterSchedule.IsCofinal schedule)
    (hConstants :
      witness.constants ⊆ programConstants P)
    (hSufficient :
      Assertion.IsSufficientFor P witness.eval) :
    ∃ firstStage, ∀ stage,
      firstStage ≤ stage →
        CNF.canonicalCandidate witness ⊆
            proposalFor (Alphabet.ofPreproc P)
              (schedule stage) ∧
          Candidate.IsSufficientFor P
            (CNF.canonicalCandidate witness) :=
  CNF.eventual_qf_witness_completeness
    P witness schedule hCofinal hConstants hSufficient

end

end

end Phase1BEnumerationTests

end Tests

end Synthesis

end Whiel
