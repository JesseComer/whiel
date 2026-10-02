-- Author: Jesse Comer
import Whiel.Concrete.Notation
import Whiel.Synthesis.Enumerators.BaseSlice.Enumeration

set_option linter.style.nativeDecide false

/-
  Focused checks for the disjunctive base slice.
-/

open Whiel.Concrete

namespace Whiel

namespace Synthesis

namespace Tests

namespace DisjunctiveClauseTests

open Whiel.Synthesis.Enumerators.BaseSlice
open DisjunctiveClause.LiteralList

------------------------------------------------------------
-- Small Mixed-Arity Alphabet
------------------------------------------------------------

def schema :
    UnnamedSchema IndexAlphaName :=
  whielSch![
    Nullary (arity: 0),
    Unary (arity: 1),
    {BinaryLeft, BinaryRight} (arity: 2),
    _ (arity: 0)
  ]

def nullaryRelation :
    schema.syms :=
  schema.sym
    (IndexAlphaName.baseString "Nullary")

def unaryRelation :
    schema.syms :=
  schema.sym
    (IndexAlphaName.baseString "Unary")

def binaryLeftRelation :
    schema.syms :=
  schema.sym
    (IndexAlphaName.baseString "BinaryLeft")

def binaryRightRelation :
    schema.syms :=
  schema.sym
    (IndexAlphaName.baseString "BinaryRight")

def alphabet :
    DisjunctiveClause.Alphabet Data schema where
  relations := schema.syms.attach
  constants := {Data.num 7}

def parameters
    (bases : Finset DisjunctiveClause.RABase)
    (maxOutputArity maxClauseWidth : Nat) :
    DisjunctiveClause.Parameters where
  enabledRABases := bases
  enabledRAOperators := ∅
  enabledAtomKinds :=
    {.equality, .containment}
  enabledLiteralSigns :=
    {.positive, .negative}
  maxRAOps := 0
  maxSelectionConditionNodes := 0
  maxProjectionExcess := 0
  maxOutputArity := maxOutputArity
  maxClauseWidth := maxClauseWidth

def relationParameters
    (maxOutputArity maxClauseWidth : Nat) :
    DisjunctiveClause.Parameters :=
  parameters {.relation}
    maxOutputArity maxClauseWidth

def equalityOnly :
    DisjunctiveClause.Parameters where
  enabledRABases := {.relation}
  enabledRAOperators := ∅
  enabledAtomKinds := {.equality}
  enabledLiteralSigns := {.positive}
  maxRAOps := 0
  maxSelectionConditionNodes := 0
  maxProjectionExcess := 0
  maxOutputArity := 0
  maxClauseWidth := 1

------------------------------------------------------------
-- Base and Arity Selection
------------------------------------------------------------

example :
    DisjunctiveClause.relationArities alphabet
        (relationParameters 0 1) =
      {0, 1, 2} := by
  native_decide

example :
    DisjunctiveClause.emptyArities alphabet
        (relationParameters 0 1) =
      {0, 1, 2} := by
  native_decide

example :
    DisjunctiveClause.emptyArities alphabet
        (parameters ∅ 0 1) =
      {0} := by
  native_decide

example :
    (Enumerators.BaseSlice.baseTerms alphabet
      (relationParameters 0 1)).length = 4 := by
  native_decide

/-
  Source relations are present even when their arity exceeds
  `maxOutputArity`.
-/
example :
    DisjunctiveClause.Term.relation
        (D := Data) binaryLeftRelation ∈
      Enumerators.BaseSlice.baseTerms alphabet
        (relationParameters 0 1) := by
  native_decide

example :
    DisjunctiveClause.Term.empty
        (D := Data) (Γ := schema) 2 ∈
      Enumerators.BaseSlice.baseTerms alphabet
        (parameters {.empty, .relation} 0 1) := by
  native_decide

example :
    DisjunctiveClause.Term.empty
        (D := Data) (Γ := schema) 3 ∉
      Enumerators.BaseSlice.baseTerms alphabet
        (parameters {.empty, .relation} 0 1) := by
  native_decide

example :
    DisjunctiveClause.Term.singleton
        (Γ := schema) (Data.num 7) ∈
      Enumerators.BaseSlice.baseTerms alphabet
        (parameters {.singleton} 0 1) := by
  native_decide

------------------------------------------------------------
-- Same-Arity Atoms and Bounded Clauses
------------------------------------------------------------

example :
    (Enumerators.BaseSlice.atomsForBasePair
      (D := Data) (relationParameters 0 1)
      (DisjunctiveClause.Term.relation binaryLeftRelation)
      (DisjunctiveClause.Term.relation
        binaryRightRelation)).length = 2 := by
  native_decide

example :
    (Enumerators.BaseSlice.atomsForBasePair
      (D := Data) equalityOnly
      (DisjunctiveClause.Term.relation binaryLeftRelation)
      (DisjunctiveClause.Term.relation
        binaryRightRelation)).length = 1 := by
  native_decide

example :
    Enumerators.BaseSlice.atomsForBasePair
        (D := Data) (relationParameters 0 1)
        (DisjunctiveClause.Term.relation nullaryRelation)
        (DisjunctiveClause.Term.relation
          unaryRelation) = [] := by
  native_decide

example :
    (Enumerators.BaseSlice.baseAtoms alphabet
      (relationParameters 0 1)).length = 12 := by
  native_decide

example :
    (Enumerators.BaseSlice.baseLiterals alphabet
      (relationParameters 0 1)).length = 24 := by
  native_decide

example :
    (Enumerators.BaseSlice.baseRepresentations
      alphabet (relationParameters 0 0)).length = 1 := by
  native_decide

example :
    (Enumerators.BaseSlice.baseRepresentations
      alphabet (relationParameters 0 1)).length = 25 := by
  native_decide

example :
    (Enumerators.BaseSlice.baseRepresentations
      alphabet (relationParameters 0 2)).length = 301 := by
  native_decide

example :
    Enumerators.BaseSlice.baseRepresentations
        alphabet (parameters ∅ 0 2) =
      [([] :
        DisjunctiveClause.LiteralList Data schema)] := by
  native_decide

------------------------------------------------------------
-- Extensional Permutation Regression
------------------------------------------------------------

def positiveNullaryEquality :
    DisjunctiveClause.Literal Data schema where
  sign := .positive
  atom :=
    DisjunctiveClause.Atom.ofTerms .equality
      (DisjunctiveClause.Term.relation
        nullaryRelation)
      (DisjunctiveClause.Term.relation
        nullaryRelation)
      rfl

def negativeNullaryEquality :
    DisjunctiveClause.Literal Data schema where
  sign := .negative
  atom := positiveNullaryEquality.atom

def canonicalPair :
    DisjunctiveClause.LiteralList Data schema :=
  [positiveNullaryEquality, negativeNullaryEquality]

def permutedPair :
    DisjunctiveClause.LiteralList Data schema :=
  [negativeNullaryEquality, positiveNullaryEquality]

theorem canonicalPair_perm_permutedPair :
    canonicalPair.SameLiterals permutedPair := by
  change
    [positiveNullaryEquality,
      negativeNullaryEquality].Perm
      [negativeNullaryEquality,
        positiveNullaryEquality]
  exact
    (List.Perm.swap positiveNullaryEquality
      negativeNullaryEquality []).symm

example :
    permutedPair.formula ∈
      (DisjunctiveClause.baseSlice alphabet
        (relationParameters 0 2)).clauses := by
  have hCanonical :
      canonicalPair ∈
        baseRepresentations alphabet
          (relationParameters 0 2) := by
    native_decide
  have hPerm :=
    canonicalPair_perm_permutedPair
  have hNormalized :
      permutedPair.IsNormalized := by
    have hCanonicalNormalized :=
      baseRepresentation_normalized
        alphabet (relationParameters 0 2)
        hCanonical
    exact hPerm.nodup_iff.mp hCanonicalNormalized
  have hEligible :
      permutedPair.IsBaseEligible alphabet
        (relationParameters 0 2) := by
    have hCanonicalEligible :=
      baseRepresentation_eligible
        alphabet (relationParameters 0 2)
        hCanonical
    constructor
    · rw [← hPerm.length_eq]
      exact hCanonicalEligible.1
    · intro literal hLiteral
      apply hCanonicalEligible.2 literal
      exact hPerm.mem_iff.mpr hLiteral
  apply
    (DisjunctiveClause.mem_baseSlice_iff
      alphabet (relationParameters 0 2)
      permutedPair.formula).mpr
  exact ⟨permutedPair, hNormalized, hEligible, rfl⟩

example :
    canonicalPair ∈
      Enumerators.BaseSlice.baseRepresentations
        alphabet (relationParameters 0 2) := by
  native_decide

example :
    permutedPair ∉
      Enumerators.BaseSlice.baseRepresentations
        alphabet (relationParameters 0 2) := by
  native_decide

example :
    QFAssertExpr.equiv
      canonicalPair.formula permutedPair.formula :=
  canonicalPair.formula_equiv_of_sameLiterals
    canonicalPair_perm_permutedPair

------------------------------------------------------------
-- Slice Correspondence
------------------------------------------------------------

example
    (term : DisjunctiveClause.Term Data schema) :
    term ∈
        Enumerators.BaseSlice.baseTerms
          alphabet (relationParameters 0 2) ↔
      term.IsBaseEligible alphabet
        (relationParameters 0 2) :=
  Enumerators.BaseSlice.mem_baseTerms_iff
    alphabet (relationParameters 0 2) term

example
    (literal : DisjunctiveClause.Literal Data schema) :
    literal ∈
        Enumerators.BaseSlice.baseLiterals
          alphabet (relationParameters 0 2) ↔
      literal.IsBaseEligible alphabet
        (relationParameters 0 2) :=
  Enumerators.BaseSlice.mem_baseLiterals_iff
    alphabet (relationParameters 0 2) literal

example
    (literalList :
      DisjunctiveClause.LiteralList Data schema) :
    literalList ∈
        Enumerators.BaseSlice.baseRepresentations
          alphabet (relationParameters 0 2) ↔
      literalList.Sublist
          (Enumerators.BaseSlice.baseLiterals
            alphabet (relationParameters 0 2)) ∧
        literalList.length ≤ 2 :=
  Enumerators.BaseSlice.mem_baseRepresentations_iff
    alphabet (relationParameters 0 2) literalList

example
    (literalList :
      DisjunctiveClause.LiteralList Data schema)
    (hNormalized : literalList.IsNormalized)
    (hEligible :
      literalList.IsBaseEligible
        alphabet (relationParameters 0 2)) :
    ∃ representation ∈
        Enumerators.BaseSlice.baseRepresentations
          alphabet (relationParameters 0 2),
      representation.SameLiterals literalList :=
  Enumerators.BaseSlice.baseRepresentations_cover
    alphabet (relationParameters 0 2)
      literalList hNormalized hEligible

example
    {left right :
      Enumerators.BaseSlice.Representation
        Data schema}
    (hLeft :
      left ∈
        Enumerators.BaseSlice.baseRepresentations
          alphabet (relationParameters 0 2))
    (hRight :
      right ∈
        Enumerators.BaseSlice.baseRepresentations
          alphabet (relationParameters 0 2)) :
    left.SameLiterals right ↔
      left = right :=
  sameLiterals_iff_eq_of_mem_baseRepresentations
    alphabet (relationParameters 0 2) hLeft hRight

example
    {literalList :
      Enumerators.BaseSlice.Representation
        Data schema}
    (hMember :
      literalList ∈
        Enumerators.BaseSlice.baseRepresentations
          alphabet (relationParameters 0 2)) :
    literalList.IsNormalized :=
  baseRepresentation_normalized
    alphabet (relationParameters 0 2) hMember

example
    (literalList :
      DisjunctiveClause.LiteralList Data schema)
    (hNormalized : literalList.IsNormalized) :
    literalList.formula ∈
      (DisjunctiveClause.clauseClass :
        ClauseClass Data schema) :=
  formula_mem_clauseClass
    literalList hNormalized

example
    (formula : Clause Data schema) :
    formula ∈
        (DisjunctiveClause.baseSlice alphabet
          (relationParameters 0 2)).clauses ↔
      ∃ literalList :
          DisjunctiveClause.LiteralList Data schema,
        literalList.IsNormalized ∧
          literalList.IsBaseEligible alphabet
            (relationParameters 0 2) ∧
          literalList.formula = formula :=
  DisjunctiveClause.mem_baseSlice_iff
    alphabet (relationParameters 0 2) formula

example
    {representation :
      Enumerators.BaseSlice.Representation
        Data schema}
    (hMember :
      representation ∈
        Enumerators.BaseSlice.baseRepresentations
          alphabet (relationParameters 0 2)) :
    Enumerators.BaseSlice.decode representation ∈
      (DisjunctiveClause.baseSlice alphabet
        (relationParameters 0 2)).clauses :=
  Enumerators.BaseSlice.baseRepresentations_sound
    alphabet (relationParameters 0 2) hMember

example
    (formula : Clause Data schema)
    (hMember :
      formula ∈
        (DisjunctiveClause.baseSlice alphabet
          (relationParameters 0 2)).clauses) :
    ∃ representation ∈
        Enumerators.BaseSlice.baseRepresentations
          alphabet (relationParameters 0 2),
      QFAssertExpr.equiv
        (Enumerators.BaseSlice.decode
          representation)
        formula :=
  baseRepresentations_complete_up_to_equiv
    alphabet (relationParameters 0 2)
      formula hMember

example
    {formula : Clause Data schema}
    (hMember :
      formula ∈
        (DisjunctiveClause.baseSlice alphabet
          (relationParameters 0 2)).clauses) :
    formula ∈ (DisjunctiveClause.clauseClass :
      ClauseClass Data schema) :=
  (DisjunctiveClause.baseSlice alphabet
    (relationParameters 0 2)).mem_class hMember

example :
    (Enumerators.BaseSlice.baseRepresentations
      alphabet (relationParameters 0 2)).Nodup :=
  Enumerators.BaseSlice.baseRepresentations_nodup
    alphabet (relationParameters 0 2)

------------------------------------------------------------
-- Complete Problem Alphabet
------------------------------------------------------------

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (relation : P.outSchema.syms) :
    relation ∈
      (DisjunctiveClause.Alphabet.ofPreproc P).relations :=
  DisjunctiveClause.Alphabet.mem_relations_ofPreproc
    P relation

example
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    DisjunctiveClause.programConstants P =
      inputPre.constants ∪ inputCmd.constants ∪
        inputPost.constants ∪ P.loopPre.constants ∪
        P.loopGuard.constants ∪
        P.loopBody.constants ∪
        P.loopPost.constants :=
  rfl

end DisjunctiveClauseTests

end Tests

end Synthesis

end Whiel
