-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.Reference
import Whiel.Synthesis.DisjunctiveClause.CNF

/-
  Eventual reference-proposal coverage for finite QF
  assertions over a fixed alphabet.

  Main declarations:
    * `Term.eventually_isEligible`
    * `CNF.eventually_clausesEligible`
    * `CNF.eventually_canonical_subset_proposalFor`
    * `CNF.eventual_qf_witness_completeness`
-/

------------------------------------------------------------
-- Eventual Term Eligibility
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace Term

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Every checked RA term over the alphabet constants becomes
  eligible at some stage of the all-enabled schedule.
-/
theorem eventually_isEligible
    (term : Term D Γ)
    (alphabet : Alphabet D Γ)
    (hRelations :
      ∀ relation : Γ.syms,
        relation ∈ alphabet.relations)
    (hConstants :
      term.expr.constants ⊆ alphabet.constants) :
    ∃ stage,
      term.IsEligible alphabet
        (referenceParameters stage) := by
  rcases term with
    ⟨arity, expression, hWellFormed⟩
  induction expression generalizing arity with
  | top =>
      have hArity : arity = 0 := by
        simpa [RawRAExpr.arity?] using
          Option.some.inj hWellFormed.symm
      subst arity
      refine ⟨0, ?_⟩
      exact Term.IsEligible.top (by
        simp [referenceParameters, allRABases])
  | empty emptyArity =>
      have hArity : arity = emptyArity := by
        simpa [RawRAExpr.arity?] using
          Option.some.inj hWellFormed.symm
      subst arity
      refine ⟨emptyArity, ?_⟩
      apply Term.IsEligible.empty emptyArity
      · simp [referenceParameters, allRABases]
      · apply Finset.mem_union_left
        simp [referenceParameters]
  | rel relationName =>
      have hName : relationName ∈ Γ.syms :=
        RawRAExpr.symbols_subset_of_schema
          hWellFormed (by simp [RawRAExpr.symbols])
      let relation : Γ.syms := ⟨relationName, hName⟩
      have hArity : arity = Γ.arity relation := by
        exact Option.some.inj
          (hWellFormed.symm.trans
            (Term.relation
              (D := D) relation).wellFormed)
      subst arity
      refine ⟨0, ?_⟩
      have hEligible :
          (Term.relation (D := D) relation).IsEligible
            alphabet (referenceParameters 0) :=
        Term.IsEligible.relation relation
          (by simp [referenceParameters, allRABases])
          (hRelations relation)
      rw [Term.eq_of_expr_eq
        (left :=
          ⟨Γ.arity relation, .rel relationName,
            hWellFormed⟩)
        (right := Term.relation (D := D) relation) rfl]
      exact hEligible
  | single constant =>
      have hArity : arity = 1 := by
        simpa [RawRAExpr.arity?] using
          Option.some.inj hWellFormed.symm
      subst arity
      have hConstant : constant ∈ alphabet.constants :=
        hConstants (by simp [RawRAExpr.constants])
      refine ⟨0, ?_⟩
      exact Term.IsEligible.singleton constant
        (by simp [referenceParameters, allRABases])
        hConstant
  | select condition child ih =>
      cases hChildArity : child.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hChildArity]
            at hWellFormed
      | some childArity =>
          by_cases hCondition :
              condition.arityReq < childArity
          · have hArity : arity = childArity := by
              have hSelected :
                  RawRAExpr.arity? Γ
                      (.select condition child) =
                    some childArity := by
                simp [RawRAExpr.arity?, hChildArity,
                  hCondition]
              exact Option.some.inj
                (hWellFormed.symm.trans hSelected)
            subst arity
            let childTerm : Term D Γ :=
              ⟨childArity, child, hChildArity⟩
            have hChildConstants :
                child.constants ⊆ alphabet.constants := by
              intro constant hConstant
              exact hConstants
                (Finset.mem_union_right _ hConstant)
            rcases ih childArity hChildArity
                hChildConstants with
              ⟨childStage, hChildEligible⟩
            have hConditionConstants :
                condition.constants ⊆
                  alphabet.constants := by
              intro constant hConstant
              exact hConstants
                (Finset.mem_union_left _ hConstant)
            let stage := childStage +
              SelectionCondition.nodeCount condition +
              childArity + (1 + childTerm.raCost)
            have hChildStage : childStage ≤ stage := by
              dsimp [stage]
              omega
            have hPromoted :
                childTerm.IsEligible alphabet
                  (referenceParameters stage) :=
              hChildEligible.mono
                (referenceParameters_mono hChildStage)
            have hEligible :
                (Term.select condition childTerm
                  hCondition).IsEligible alphabet
                    (referenceParameters stage) := by
              apply Term.IsEligible.selection
                condition childTerm hPromoted
              · simp [referenceParameters, allRAOperators]
              · exact
                  ⟨hCondition, hConditionConstants, by
                    dsimp [stage, referenceParameters]
                    omega⟩
              · dsimp [stage, referenceParameters,
                  childTerm]
                omega
              · dsimp [stage, referenceParameters,
                  childTerm]
                omega
            refine ⟨stage, ?_⟩
            rw [Term.eq_of_expr_eq
              (left :=
                ⟨childArity, .select condition child,
                  hWellFormed⟩)
              (right := Term.select condition childTerm
                hCondition) rfl]
            exact hEligible
          · simp [RawRAExpr.arity?, hChildArity,
              hCondition] at hWellFormed
  | proj indices child ih =>
      cases hChildArity : child.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hChildArity]
            at hWellFormed
      | some childArity =>
          by_cases hIndices :
              ∀ index ∈ indices, index < childArity
          · have hArity : arity = indices.length := by
              have hProjected :
                  RawRAExpr.arity? Γ
                      (.proj indices child) =
                    some indices.length := by
                  rw [RawRAExpr.arity?, hChildArity]
                  have hDecide :
                      decide
                        (∀ index ∈ indices,
                          index < childArity) = true :=
                    decide_eq_true hIndices
                  simp only [hDecide, if_true]
              exact Option.some.inj
                (hWellFormed.symm.trans hProjected)
            subst arity
            let childTerm : Term D Γ :=
              ⟨childArity, child, hChildArity⟩
            have hChildConstants :
                child.constants ⊆ alphabet.constants := by
              simpa [RawRAExpr.constants] using hConstants
            rcases ih childArity hChildArity
                hChildConstants with
              ⟨childStage, hChildEligible⟩
            let stage := childStage + indices.length +
              (1 + childTerm.raCost)
            have hChildStage : childStage ≤ stage := by
              dsimp [stage]
              omega
            have hPromoted :
                childTerm.IsEligible alphabet
                  (referenceParameters stage) :=
              hChildEligible.mono
                (referenceParameters_mono hChildStage)
            have hEligible :
                (Term.project indices childTerm
                  hIndices).IsEligible alphabet
                    (referenceParameters stage) := by
              apply Term.IsEligible.projection
                indices childTerm hPromoted
              · simp [referenceParameters, allRAOperators]
              · exact ⟨hIndices, by
                  dsimp [stage, referenceParameters,
                    ProjectionList.excess]
                  omega⟩
              · dsimp [stage, referenceParameters,
                  childTerm]
                omega
              · dsimp [stage, referenceParameters,
                  childTerm]
                omega
            refine ⟨stage, ?_⟩
            rw [Term.eq_of_expr_eq
              (left :=
                ⟨indices.length, .proj indices child,
                  hWellFormed⟩)
              (right := Term.project indices childTerm
                hIndices) rfl]
            exact hEligible
          · simp [RawRAExpr.arity?, hChildArity,
              hIndices] at hWellFormed
  | prod left right leftIH rightIH =>
      cases hLeftArity : left.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hLeftArity]
            at hWellFormed
      | some leftArity =>
          cases hRightArity : right.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, hLeftArity,
                hRightArity] at hWellFormed
          | some rightArity =>
              have hArity :
                  arity = leftArity + rightArity := by
                have hProduct :
                    RawRAExpr.arity? Γ
                        (.prod left right) =
                      some (leftArity + rightArity) := by
                  simp [RawRAExpr.arity?, hLeftArity,
                    hRightArity]
                exact Option.some.inj
                  (hWellFormed.symm.trans hProduct)
              subst arity
              let leftTerm : Term D Γ :=
                ⟨leftArity, left, hLeftArity⟩
              let rightTerm : Term D Γ :=
                ⟨rightArity, right, hRightArity⟩
              have hLeftConstants :
                  left.constants ⊆
                    alphabet.constants := by
                intro constant hConstant
                exact hConstants
                  (Finset.mem_union_left _ hConstant)
              have hRightConstants :
                  right.constants ⊆
                    alphabet.constants := by
                intro constant hConstant
                exact hConstants
                  (Finset.mem_union_right _ hConstant)
              rcases leftIH leftArity hLeftArity
                  hLeftConstants with
                ⟨leftStage, hLeftEligible⟩
              rcases rightIH rightArity hRightArity
                  hRightConstants with
                ⟨rightStage, hRightEligible⟩
              let stage := leftStage + rightStage +
                (leftArity + rightArity) +
                (1 + leftTerm.raCost + rightTerm.raCost)
              have hLeftStage : leftStage ≤ stage := by
                dsimp [stage]
                omega
              have hRightStage : rightStage ≤ stage := by
                dsimp [stage]
                omega
              have hEligible :
                  (Term.product leftTerm
                    rightTerm).IsEligible alphabet
                      (referenceParameters stage) := by
                apply Term.IsEligible.product
                · exact hLeftEligible.mono
                    (referenceParameters_mono hLeftStage)
                · exact hRightEligible.mono
                    (referenceParameters_mono hRightStage)
                · simp [referenceParameters,
                    allRAOperators]
                · dsimp [stage, referenceParameters,
                    leftTerm, rightTerm]
                  omega
                · dsimp [stage, referenceParameters,
                    leftTerm, rightTerm]
                  omega
              refine ⟨stage, ?_⟩
              rw [Term.eq_of_expr_eq
                (left :=
                  ⟨leftArity + rightArity,
                    .prod left right, hWellFormed⟩)
                (right := Term.product leftTerm rightTerm)
                rfl]
              exact hEligible
  | union left right leftIH rightIH =>
      cases hLeftArity : left.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hLeftArity]
            at hWellFormed
      | some leftArity =>
          cases hRightArity : right.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, hLeftArity,
                hRightArity] at hWellFormed
          | some rightArity =>
              by_cases hSame : leftArity = rightArity
              · have hArity : arity = leftArity := by
                  have hUnion :
                      RawRAExpr.arity? Γ
                          (.union left right) =
                        some leftArity := by
                    simp [RawRAExpr.arity?, hLeftArity,
                      hRightArity, hSame]
                  exact Option.some.inj
                    (hWellFormed.symm.trans hUnion)
                subst arity
                subst rightArity
                let leftTerm : Term D Γ :=
                  ⟨leftArity, left, hLeftArity⟩
                let rightTerm : Term D Γ :=
                  ⟨leftArity, right, hRightArity⟩
                have hLeftConstants :
                    left.constants ⊆
                      alphabet.constants := by
                  intro constant hConstant
                  exact hConstants
                    (Finset.mem_union_left _ hConstant)
                have hRightConstants :
                    right.constants ⊆
                      alphabet.constants := by
                  intro constant hConstant
                  exact hConstants
                    (Finset.mem_union_right _ hConstant)
                rcases leftIH leftArity hLeftArity
                    hLeftConstants with
                  ⟨leftStage, hLeftEligible⟩
                rcases rightIH leftArity hRightArity
                    hRightConstants with
                  ⟨rightStage, hRightEligible⟩
                let stage := leftStage + rightStage +
                  leftArity +
                  (1 + leftTerm.raCost + rightTerm.raCost)
                have hLeftStage : leftStage ≤ stage := by
                  dsimp [stage]
                  omega
                have hRightStage :
                    rightStage ≤ stage := by
                  dsimp [stage]
                  omega
                have hEligible :
                    (Term.union leftTerm rightTerm
                      rfl).IsEligible alphabet
                        (referenceParameters stage) := by
                  apply Term.IsEligible.union
                    leftTerm rightTerm rfl
                  · exact hLeftEligible.mono
                      (referenceParameters_mono hLeftStage)
                  · exact hRightEligible.mono
                      (referenceParameters_mono hRightStage)
                  · simp [referenceParameters,
                      allRAOperators]
                  · dsimp [stage, referenceParameters,
                      leftTerm, rightTerm]
                    omega
                  · dsimp [stage, referenceParameters,
                      leftTerm, rightTerm]
                    omega
                refine ⟨stage, ?_⟩
                rw [Term.eq_of_expr_eq
                  (left :=
                    ⟨leftArity, .union left right,
                      hWellFormed⟩)
                  (right :=
                    Term.union leftTerm rightTerm rfl) rfl]
                exact hEligible
              · simp [RawRAExpr.arity?, hLeftArity,
                  hRightArity, hSame] at hWellFormed
  | diff left right leftIH rightIH =>
      cases hLeftArity : left.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hLeftArity]
            at hWellFormed
      | some leftArity =>
          cases hRightArity : right.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, hLeftArity,
                hRightArity] at hWellFormed
          | some rightArity =>
              by_cases hSame : leftArity = rightArity
              · have hArity : arity = leftArity := by
                  have hDifference :
                      RawRAExpr.arity? Γ
                          (.diff left right) =
                        some leftArity := by
                    simp [RawRAExpr.arity?, hLeftArity,
                      hRightArity, hSame]
                  exact Option.some.inj
                    (hWellFormed.symm.trans hDifference)
                subst arity
                subst rightArity
                let leftTerm : Term D Γ :=
                  ⟨leftArity, left, hLeftArity⟩
                let rightTerm : Term D Γ :=
                  ⟨leftArity, right, hRightArity⟩
                have hLeftConstants :
                    left.constants ⊆
                      alphabet.constants := by
                  intro constant hConstant
                  exact hConstants
                    (Finset.mem_union_left _ hConstant)
                have hRightConstants :
                    right.constants ⊆
                      alphabet.constants := by
                  intro constant hConstant
                  exact hConstants
                    (Finset.mem_union_right _ hConstant)
                rcases leftIH leftArity hLeftArity
                    hLeftConstants with
                  ⟨leftStage, hLeftEligible⟩
                rcases rightIH leftArity hRightArity
                    hRightConstants with
                  ⟨rightStage, hRightEligible⟩
                let stage := leftStage + rightStage +
                  leftArity +
                  (1 + leftTerm.raCost + rightTerm.raCost)
                have hLeftStage : leftStage ≤ stage := by
                  dsimp [stage]
                  omega
                have hRightStage :
                    rightStage ≤ stage := by
                  dsimp [stage]
                  omega
                have hEligible :
                    (Term.difference leftTerm rightTerm
                      rfl).IsEligible alphabet
                        (referenceParameters stage) := by
                  apply Term.IsEligible.difference
                    leftTerm rightTerm rfl
                  · exact hLeftEligible.mono
                      (referenceParameters_mono hLeftStage)
                  · exact hRightEligible.mono
                      (referenceParameters_mono hRightStage)
                  · simp [referenceParameters,
                      allRAOperators]
                  · dsimp [stage, referenceParameters,
                      leftTerm, rightTerm]
                    omega
                  · dsimp [stage, referenceParameters,
                      leftTerm, rightTerm]
                    omega
                refine ⟨stage, ?_⟩
                rw [Term.eq_of_expr_eq
                  (left :=
                    ⟨leftArity, .diff left right,
                      hWellFormed⟩)
                  (right := Term.difference leftTerm
                    rightTerm rfl) rfl]
                exact hEligible
              · simp [RawRAExpr.arity?, hLeftArity,
                  hRightArity, hSame] at hWellFormed

end Term

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Eventual Literal and CNF Eligibility
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Every supported literal becomes eligible at one stage. -/
theorem Literal.eventually_isEligible
    (literal : Literal D Γ)
    (alphabet : Alphabet D Γ)
    (hRelations :
      ∀ relation : Γ.syms,
        relation ∈ alphabet.relations)
    (hConstants :
      literal.formula.constants ⊆ alphabet.constants) :
    ∃ stage,
      literal.IsEligible alphabet
        (referenceParameters stage) := by
  rcases literal with ⟨sign, atom⟩
  rcases atom with
    ⟨kind, arity, left, right,
      leftWellFormed, rightWellFormed⟩
  let leftTerm : Term D Γ :=
    ⟨arity, left, leftWellFormed⟩
  let rightTerm : Term D Γ :=
    ⟨arity, right, rightWellFormed⟩
  have hLeftConstants :
      left.constants ⊆ alphabet.constants := by
    intro constant hConstant
    apply hConstants
    cases sign <;> cases kind <;>
      simp [Literal.formula, Atom.formula,
        Atom.leftExpr, Atom.rightExpr,
        RAExpr.constants, Guard.constants, hConstant]
  have hRightConstants :
      right.constants ⊆ alphabet.constants := by
    intro constant hConstant
    apply hConstants
    cases sign <;> cases kind <;>
      simp [Literal.formula, Atom.formula,
        Atom.leftExpr, Atom.rightExpr,
        RAExpr.constants, Guard.constants, hConstant]
  rcases Term.eventually_isEligible leftTerm alphabet
      hRelations hLeftConstants with
    ⟨leftStage, hLeftEligible⟩
  rcases Term.eventually_isEligible rightTerm alphabet
      hRelations hRightConstants with
    ⟨rightStage, hRightEligible⟩
  let stage := leftStage + rightStage
  have hLeftStage : leftStage ≤ stage := by
    dsimp [stage]
    omega
  have hRightStage : rightStage ≤ stage := by
    dsimp [stage]
    omega
  have hAtomEligible :
      ({ kind := kind
         arity := arity
         left := left
         right := right
         leftWellFormed := leftWellFormed
         rightWellFormed := rightWellFormed } :
        Atom D Γ).IsEligible alphabet
          (referenceParameters stage) := by
    refine
      ⟨kind, ?_, leftTerm, ?_, rightTerm, ?_,
        rfl, ?_⟩
    · cases kind <;>
        simp [referenceParameters, allAtomKinds]
    · exact hLeftEligible.mono
        (referenceParameters_mono hLeftStage)
    · exact hRightEligible.mono
        (referenceParameters_mono hRightStage)
    · rfl
  refine ⟨stage, ?_⟩
  exact
    ⟨by cases sign <;>
        simp [referenceParameters, allLiteralSigns],
      hAtomEligible⟩

/-
  Every finite supported literal list becomes eligible at
  one common stage. Normalization is independent of this
  result.
-/
theorem LiteralList.eventually_isEligible
    (literalList : LiteralList D Γ)
    (alphabet : Alphabet D Γ)
    (hRelations :
      ∀ relation : Γ.syms,
        relation ∈ alphabet.relations)
    (hConstants :
      ∀ literal ∈ literalList,
        literal.formula.constants ⊆
          alphabet.constants) :
    ∃ stage,
      literalList.IsEligible alphabet
        (referenceParameters stage) := by
  induction literalList with
  | nil =>
      refine ⟨0, ?_⟩
      simp [LiteralList.IsEligible,
        referenceParameters]
  | cons literal literalList ih =>
      have hHeadConstants :
          literal.formula.constants ⊆
            alphabet.constants :=
        hConstants literal (by simp)
      have hTailConstants :
          ∀ item ∈ literalList,
            item.formula.constants ⊆
              alphabet.constants := by
        intro item hItem
        exact hConstants item (by simp [hItem])
      rcases literal.eventually_isEligible alphabet
          hRelations hHeadConstants with
        ⟨headStage, hHeadEligible⟩
      rcases ih hTailConstants with
        ⟨tailStage, hTailEligible⟩
      let stage := headStage + tailStage +
        (literal :: literalList).length
      have hHeadStage : headStage ≤ stage := by
        dsimp [stage]
        omega
      have hTailStage : tailStage ≤ stage := by
        dsimp [stage]
        omega
      refine ⟨stage, ?_⟩
      constructor
      · dsimp [stage, referenceParameters]
        omega
      · intro item hItem
        simp only [List.mem_cons] at hItem
        rcases hItem with rfl | hItem
        · exact hHeadEligible.mono
            (referenceParameters_mono hHeadStage)
        · exact
            (hTailEligible.2 item hItem).mono
              (referenceParameters_mono hTailStage)

/-
  All clauses in the converted CNF become eligible together
  at one finite reference stage.
-/
private theorem exists_commonEligibleStage
    (literalLists : List (LiteralList D Γ))
    (alphabet : Alphabet D Γ)
    (hEach :
      ∀ literalList ∈ literalLists,
        ∃ stage,
          literalList.IsEligible alphabet
            (referenceParameters stage)) :
    ∃ stage,
      ∀ literalList ∈ literalLists,
        literalList.IsEligible alphabet
          (referenceParameters stage) := by
  induction literalLists with
  | nil =>
      exact ⟨0, by simp⟩
  | cons literalList literalLists ih =>
      rcases hEach literalList (by simp) with
        ⟨headStage, hHeadEligible⟩
      have hTailEach :
          ∀ item ∈ literalLists,
            ∃ stage,
              item.IsEligible alphabet
                (referenceParameters stage) := by
        intro item hItem
        exact hEach item (by simp [hItem])
      rcases ih hTailEach with
        ⟨tailStage, hTailEligible⟩
      let stage := headStage + tailStage
      have hHeadStage : headStage ≤ stage := by
        dsimp [stage]
        omega
      have hTailStage : tailStage ≤ stage := by
        dsimp [stage]
        omega
      refine ⟨stage, ?_⟩
      intro item hItem
      simp only [List.mem_cons] at hItem
      rcases hItem with rfl | hItem
      · exact hHeadEligible.mono
          (referenceParameters_mono hHeadStage)
      · exact (hTailEligible item hItem).mono
          (referenceParameters_mono hTailStage)

theorem CNF.eventually_clausesEligible
    (input : QFAssertExpr D Γ)
    (alphabet : Alphabet D Γ)
    (hRelations :
      ∀ relation : Γ.syms,
        relation ∈ alphabet.relations)
    (hConstants :
      input.constants ⊆ alphabet.constants) :
    ∃ stage,
      ∀ clause ∈ CNF.clauses input,
        clause.IsEligible alphabet
          (referenceParameters stage) := by
  apply exists_commonEligibleStage
  intro clause hClause
  apply clause.eventually_isEligible alphabet hRelations
  intro literal hLiteral
  exact Finset.Subset.trans
    ((CNF.clauses_useOnlyInput input
      hClause literal hLiteral).2)
    hConstants

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Eventual Proposal Coverage
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

namespace CNF

variable [LinearOrder A] [LinearOrder D]

open CanonicalEnumeration

/-
  Reorder every converted CNF clause by the configured
  serialization order. This is the fixed selected candidate
  used to witness semantic proposal coverage.
-/
def canonicalCandidate
    (input : QFAssertExpr D Γ) :
    Candidate D Γ :=
  List.toFinset
    ((clauses input).map fun clause =>
      FullEnumeration.decode
        (canonicalize clause))

/- Canonical candidate membership comes from one clause. -/
@[simp] theorem mem_canonicalCandidate_iff
    (input : QFAssertExpr D Γ)
    (formula : Clause D Γ) :
    formula ∈ canonicalCandidate input ↔
      ∃ clause ∈ clauses input,
        FullEnumeration.decode
          (canonicalize clause) =
            formula := by
  simp [canonicalCandidate]

/- Canonical reordering preserves the CNF denotation. -/
theorem canonicalCandidate_denote_equiv
    (input : QFAssertExpr D Γ) :
    Assertion.equiv
      (canonicalCandidate input).denote input.eval := by
  constructor
  · intro I hCanonical
    apply (candidate_denote_equiv input).1 I
    intro formula hFormula
    rw [mem_candidate_iff] at hFormula
    rcases hFormula with ⟨clause, hClause, rfl⟩
    have hCanonicalMember :
        FullEnumeration.decode
            (canonicalize clause) ∈
          canonicalCandidate input :=
      (mem_canonicalCandidate_iff input _).mpr
        ⟨clause, hClause, rfl⟩
    have hCanonicalEval :=
      hCanonical _ hCanonicalMember
    have hEquiv :=
      LiteralList.formula_equiv_of_sameLiterals
        (canonicalize_sameLiterals clause
          (clauses_normalized input hClause))
    exact hEquiv.1 I hCanonicalEval
  · intro I hInput
    have hCandidate :=
      (candidate_denote_equiv input).2 I hInput
    intro formula hFormula
    rw [mem_canonicalCandidate_iff] at hFormula
    rcases hFormula with
      ⟨clause, hClause, rfl⟩
    have hClauseMember :
        clause.formula ∈ candidate input :=
      (mem_candidate_iff input _).mpr
        ⟨clause, hClause, rfl⟩
    have hClauseEval := hCandidate _ hClauseMember
    have hEquiv :=
      LiteralList.formula_equiv_of_sameLiterals
        (canonicalize_sameLiterals clause
          (clauses_normalized input hClause))
    exact hEquiv.2 I hClauseEval

/-
  If every converted clause is eligible, the proposal
  contains its canonical selected candidate.
-/
theorem canonicalCandidate_subset_proposalFor
    (input : QFAssertExpr D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (hEligible :
      ∀ clause ∈ clauses input,
        clause.IsEligible alphabet parameters) :
    canonicalCandidate input ⊆
      proposalFor alphabet parameters := by
  intro formula hFormula
  rw [mem_canonicalCandidate_iff] at hFormula
  rcases hFormula with
    ⟨clause, hClause, rfl⟩
  change
    FullEnumeration.decode
        (canonicalize clause) ∈
      CanonicalEnumeration.clauses
        alphabet parameters
  apply Finset.mem_image.mpr
  exact
    ⟨canonicalize clause,
      canonicalize_mem_representations
        alphabet parameters clause
          (clauses_normalized input hClause)
          (hEligible clause hClause),
      rfl⟩

/-
  The canonical proposal eventually contains the canonical
  selected candidate and retains it at every later stage.
-/
theorem eventually_canonical_subset_referenceProposal
    (input : QFAssertExpr D Γ)
    (alphabet : Alphabet D Γ)
    (hRelations :
      ∀ relation : Γ.syms,
        relation ∈ alphabet.relations)
    (hConstants :
      input.constants ⊆ alphabet.constants) :
    ∃ firstStage, ∀ stage,
      firstStage ≤ stage →
        canonicalCandidate input ⊆
          referenceProposal alphabet stage := by
  rcases eventually_clausesEligible input alphabet
      hRelations hConstants with
    ⟨firstStage, hEligible⟩
  refine ⟨firstStage, ?_⟩
  intro stage hStage
  apply canonicalCandidate_subset_proposalFor
  intro clause hClause
  exact
    (hEligible clause hClause).mono
      (referenceParameters_mono hStage)

/-
  Every cofinal schedule eventually retains the canonical
  selected candidate in its executable proposal.
-/
theorem eventually_canonical_subset_proposalFor
    (input : QFAssertExpr D Γ)
    (alphabet : Alphabet D Γ)
    (schedule : Nat → Parameters)
    (hCofinal :
      ParameterSchedule.IsCofinal schedule)
    (hRelations :
      ∀ relation : Γ.syms,
        relation ∈ alphabet.relations)
    (hConstants :
      input.constants ⊆ alphabet.constants) :
    ∃ firstStage, ∀ stage,
      firstStage ≤ stage →
        canonicalCandidate input ⊆
          proposalFor alphabet (schedule stage) := by
  rcases eventually_clausesEligible input alphabet
      hRelations hConstants with
    ⟨requiredStage, hEligible⟩
  rcases hCofinal (referenceParameters requiredStage) with
    ⟨firstStage, hDominates⟩
  refine ⟨firstStage, ?_⟩
  intro stage hStage
  apply canonicalCandidate_subset_proposalFor
  intro clause hClause
  exact
    (hEligible clause hClause).mono
      (hDominates stage hStage)

end CNF

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- QF Witness Completeness
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace CNF

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/-
  Every canonical clause satisfies initialization when the
  source witness is inductive.
-/
theorem canonicalCandidate_member_init_of_inductive
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (witness : QFAssertExpr D P.outSchema)
    (hInductive :
      Assertion.IsInductiveFor P witness.eval)
    {clause : Clause D P.outSchema}
    (hMember :
      clause ∈ canonicalCandidate witness) :
    Assertion.Init P clause.eval := by
  have hCandidateInductive :
      (canonicalCandidate witness).IsInductiveFor P :=
    (Assertion.isInductiveFor_congr P
      (canonicalCandidate_denote_equiv witness)).mpr
        hInductive
  exact
    (Candidate.init_denote_iff P
      (canonicalCandidate witness)).mp
        hCandidateInductive.1 clause hMember

/- Canonical CNF conversion preserves maintenance. -/
theorem canonicalCandidate_maint_of_inductive
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (witness : QFAssertExpr D P.outSchema)
    (hInductive :
      Assertion.IsInductiveFor P witness.eval) :
    (canonicalCandidate witness).denote.Maint P := by
  exact
    ((Assertion.isInductiveFor_congr P
      (canonicalCandidate_denote_equiv witness)).mpr
        hInductive).2

/- Canonical CNF conversion preserves termination. -/
theorem canonicalCandidate_term_of_sufficient
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (witness : QFAssertExpr D P.outSchema)
    (hSufficient :
      Assertion.IsSufficientFor P witness.eval) :
    (canonicalCandidate witness).denote.Term P := by
  exact
    ((Assertion.isSufficientFor_congr P
      (canonicalCandidate_denote_equiv witness)).mpr
        hSufficient).2

/-
  A sufficient witness transfers all three obligations to
  its canonical CNF candidate.
-/
theorem canonicalCandidate_obligations_of_sufficient
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (witness : QFAssertExpr D P.outSchema)
    (hSufficient :
      Assertion.IsSufficientFor P witness.eval) :
    (∀ clause ∈ canonicalCandidate witness,
        Assertion.Init P clause.eval) ∧
      (canonicalCandidate witness).denote.Maint P ∧
      (canonicalCandidate witness).denote.Term P := by
  exact
    ⟨fun clause hMember =>
      canonicalCandidate_member_init_of_inductive
        P witness hSufficient.1 hMember,
      canonicalCandidate_maint_of_inductive
        P witness hSufficient.1,
      canonicalCandidate_term_of_sufficient
        P witness hSufficient⟩

/-
  Eventual QF witness completeness: if a sufficient QF
  witness exists, every cofinal schedule eventually emits
  proposals containing an equivalent sufficient CNF
  witness. This does not claim that a whole proposal is
  sufficient.
-/
theorem eventual_qf_witness_completeness
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (witness : QFAssertExpr D P.outSchema)
    (schedule : Nat → Parameters)
    (hCofinal :
      ParameterSchedule.IsCofinal schedule)
    (hConstants :
      witness.constants ⊆ programConstants P)
    (hSufficient :
      Assertion.IsSufficientFor P witness.eval) :
    ∃ firstStage, ∀ stage,
      firstStage ≤ stage →
        canonicalCandidate witness ⊆
            proposalFor
              (Alphabet.ofPreproc P)
              (schedule stage) ∧
          Candidate.IsSufficientFor P
            (canonicalCandidate witness) := by
  have hRelations :
      ∀ relation : P.outSchema.syms,
        relation ∈
          (Alphabet.ofPreproc P).relations :=
    Alphabet.mem_relations_ofPreproc P
  have hProposal :=
    eventually_canonical_subset_proposalFor witness
      (Alphabet.ofPreproc P) schedule hCofinal
        hRelations hConstants
  rcases hProposal with
    ⟨firstStage, hSubset⟩
  have hCandidateSufficient :
      (canonicalCandidate witness).IsSufficientFor P := by
    exact
      (Assertion.isSufficientFor_congr P
        (canonicalCandidate_denote_equiv witness)).mpr
          hSufficient
  exact
    ⟨firstStage, fun stage hStage =>
      ⟨hSubset stage hStage, hCandidateSufficient⟩⟩

end CNF

end DisjunctiveClause

end Synthesis

end Whiel
