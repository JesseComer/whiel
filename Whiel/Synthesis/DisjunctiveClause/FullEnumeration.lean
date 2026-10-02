-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.FullSpec
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Union

/-
  Order-free finite universe for the full bounded
  disjunctive-clause grammar.

  The realization uses `Finset` throughout. It requires no
  arbitrary order on relation names or domain values.

  Main declarations:
    * `selectionConditions` and `projectionLists`
    * `termsThroughCost` and `terms`
    * `atoms`, `literals`, and `representations`
    * exact membership and coverage theorems
-/

------------------------------------------------------------
-- Generic Finite List Closure
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace FullEnumeration

variable {T : Type} [DecidableEq T]

/-
  All lists over `items` whose length is at most
  `bound`.
-/
def listsUpTo
    (items : Finset T) : Nat → Finset (List T)
| 0 => {[]}
| bound + 1 =>
    {[]} ∪
      items.biUnion fun item =>
        (listsUpTo items bound).image fun tail =>
          item :: tail

@[simp] theorem mem_listsUpTo_iff
    (items : Finset T)
    (bound : Nat)
    (values : List T) :
    values ∈ listsUpTo items bound ↔
      values.length ≤ bound ∧
        ∀ value ∈ values, value ∈ items := by
  induction bound generalizing values with
  | zero =>
      constructor
      · intro hMember
        have hEmpty : values = [] := by
          simpa [listsUpTo] using hMember
        subst values
        simp
      · rintro ⟨hLength, _⟩
        cases values with
        | nil => simp [listsUpTo]
        | cons head tail => simp at hLength
  | succ bound ih =>
      constructor
      · intro hMember
        simp only [listsUpTo, Finset.mem_union,
          Finset.mem_singleton, Finset.mem_biUnion,
          Finset.mem_image] at hMember
        rcases hMember with rfl | hCons
        · simp
        · rcases hCons with
            ⟨head, hHead, tail, hTail, rfl⟩
          have hTailProperties :=
            (ih tail).mp hTail
          constructor
          · simpa only [List.length_cons,
              Nat.succ_le_succ_iff] using
                hTailProperties.1
          · intro value hValue
            simp only [List.mem_cons] at hValue
            rcases hValue with rfl | hValue
            · exact hHead
            · exact hTailProperties.2 value hValue
      · rintro ⟨hLength, hValues⟩
        cases values with
        | nil => simp [listsUpTo]
        | cons head tail =>
            have hHead : head ∈ items :=
              hValues head (by simp)
            have hTailLength : tail.length ≤ bound := by
              simpa using hLength
            have hTailValues :
                ∀ value ∈ tail, value ∈ items := by
              intro value hValue
              exact hValues value (by simp [hValue])
            have hTail :
                tail ∈ listsUpTo items bound :=
              (ih tail).mpr
                ⟨hTailLength, hTailValues⟩
            simp only [listsUpTo, Finset.mem_union,
              Finset.mem_singleton, Finset.mem_biUnion,
              Finset.mem_image]
            exact Or.inr
              ⟨head, hHead, tail, hTail, rfl⟩

end FullEnumeration

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Selection Conditions
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace FullEnumeration

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Atomic conditions valid at one input arity. -/
def atomicSelectionConditions
    (inputArity : Nat)
    (alphabet : Alphabet D Γ) :
    Finset (Sel D) :=
  let indexEqualities : Finset (Sel D) :=
    ((Finset.range inputArity).product
      (Finset.range inputArity)).image fun pair =>
        Sel.eqIdx pair.1 pair.2
  let constantEqualities : Finset (Sel D) :=
    ((Finset.range inputArity).product
      alphabet.constants).image fun pair =>
        Sel.eqConst pair.1 pair.2
  indexEqualities ∪ constantEqualities

/-
  A finite syntax universe large enough for all conditions
  through the given node count. The final public function
  applies the exact node-count filter.
-/
def selectionConditionCandidates
    (inputArity : Nat)
    (alphabet : Alphabet D Γ) :
    Nat → Finset (Sel D)
| 0 => ∅
| bound + 1 =>
    let prior :=
      selectionConditionCandidates inputArity alphabet bound
    let negations : Finset (Sel D) :=
      prior.image Sel.not
    let conjunctions : Finset (Sel D) :=
      (prior.product prior).image fun pair =>
        Sel.and pair.1 pair.2
    let disjunctions : Finset (Sel D) :=
      (prior.product prior).image fun pair =>
        Sel.or pair.1 pair.2
    atomicSelectionConditions inputArity alphabet ∪
      (negations ∪ (conjunctions ∪ disjunctions))

/-
  Conditions satisfying the exact public eligibility
  bound.
-/
def selectionConditions
    (inputArity : Nat)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Finset (Sel D) :=
  (selectionConditionCandidates inputArity alphabet
      parameters.maxSelectionConditionNodes).filter
        fun condition =>
    SelectionCondition.nodeCount condition ≤
      parameters.maxSelectionConditionNodes

private theorem atomicSelectionConditions_valid
    (inputArity : Nat)
    (alphabet : Alphabet D Γ)
    {condition : Sel D}
    (hMember :
      condition ∈
        atomicSelectionConditions inputArity alphabet) :
    condition.arityReq < inputArity ∧
      condition.constants ⊆ alphabet.constants := by
  rw [atomicSelectionConditions,
    Finset.mem_union] at hMember
  rcases hMember with hIndices | hConstant
  · rcases Finset.mem_image.mp hIndices with
      ⟨pair, hPair, rfl⟩
    have hPairMember := Finset.mem_product.mp hPair
    have hLeft := Finset.mem_range.mp hPairMember.1
    have hRight := Finset.mem_range.mp hPairMember.2
    simp [Sel.arityReq, hLeft, hRight, Sel.constants]
  · rcases Finset.mem_image.mp hConstant with
      ⟨pair, hPair, rfl⟩
    have hPairMember := Finset.mem_product.mp hPair
    have hIndex := Finset.mem_range.mp hPairMember.1
    have hConstant := hPairMember.2
    simp [Sel.arityReq, Sel.constants, hIndex,
      hConstant]

private theorem atomicSelectionConditions_complete
    (inputArity : Nat)
    (alphabet : Alphabet D Γ)
    {condition : Sel D}
    (hAtomic :
      (∃ left right,
        left < inputArity ∧ right < inputArity ∧
          condition = .eqIdx left right) ∨
      (∃ index constant,
        index < inputArity ∧
          constant ∈ alphabet.constants ∧
          condition = .eqConst index constant)) :
    condition ∈
      atomicSelectionConditions inputArity alphabet := by
  rcases hAtomic with
      ⟨left, right, hLeft, hRight, rfl⟩ |
      ⟨index, constant, hIndex, hConstant, rfl⟩
  · rw [atomicSelectionConditions, Finset.mem_union]
    apply Or.inl
    apply Finset.mem_image.mpr
    exact
      ⟨(left, right),
        Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hLeft,
            Finset.mem_range.mpr hRight⟩,
        rfl⟩
  · rw [atomicSelectionConditions, Finset.mem_union]
    apply Or.inr
    apply Finset.mem_image.mpr
    exact
      ⟨(index, constant),
        Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hIndex, hConstant⟩,
        rfl⟩

private theorem selectionConditionCandidates_valid
    (inputArity : Nat)
    (alphabet : Alphabet D Γ)
    (bound : Nat)
    {condition : Sel D}
    (hMember :
      condition ∈ selectionConditionCandidates
        inputArity alphabet bound) :
    condition.arityReq < inputArity ∧
      condition.constants ⊆ alphabet.constants := by
  induction bound generalizing condition with
  | zero => simp [selectionConditionCandidates] at hMember
  | succ bound ih =>
      rw [selectionConditionCandidates,
        Finset.mem_union] at hMember
      rcases hMember with hAtomic | hRest
      · exact atomicSelectionConditions_valid
          inputArity alphabet hAtomic
      · rw [Finset.mem_union] at hRest
        rcases hRest with hNot | hBinary
        · rcases Finset.mem_image.mp hNot with
            ⟨child, hChild, rfl⟩
          have hValid := ih hChild
          simpa [Sel.arityReq, Sel.constants] using hValid
        · rw [Finset.mem_union] at hBinary
          rcases hBinary with hAnd | hOr
          · rcases Finset.mem_image.mp hAnd with
              ⟨pair, hPair, rfl⟩
            have hPairMember := Finset.mem_product.mp hPair
            have hLeftValid := ih hPairMember.1
            have hRightValid := ih hPairMember.2
            constructor
            · simpa [Sel.arityReq] using
                And.intro hLeftValid.1 hRightValid.1
            · simpa [Sel.constants] using
                Finset.union_subset
                  hLeftValid.2 hRightValid.2
          · rcases Finset.mem_image.mp hOr with
              ⟨pair, hPair, rfl⟩
            have hPairMember := Finset.mem_product.mp hPair
            have hLeftValid := ih hPairMember.1
            have hRightValid := ih hPairMember.2
            constructor
            · simpa [Sel.arityReq] using
                And.intro hLeftValid.1 hRightValid.1
            · simpa [Sel.constants] using
                Finset.union_subset
                  hLeftValid.2 hRightValid.2

private theorem selectionConditionCandidates_complete
    (inputArity : Nat)
    (alphabet : Alphabet D Γ)
    (bound : Nat)
    (condition : Sel D)
    (hArity : condition.arityReq < inputArity)
    (hConstants :
      condition.constants ⊆ alphabet.constants)
    (hNodes :
      SelectionCondition.nodeCount condition ≤ bound) :
    condition ∈ selectionConditionCandidates
      inputArity alphabet bound := by
  induction bound generalizing condition with
  | zero =>
      have hPositive :=
        SelectionCondition.nodeCount_pos condition
      omega
  | succ bound ih =>
      rw [selectionConditionCandidates,
        Finset.mem_union]
      cases condition with
      | eqIdx left right =>
          have hArityPair :
              left < inputArity ∧ right < inputArity := by
            simpa [Sel.arityReq] using hArity
          apply Or.inl
          apply atomicSelectionConditions_complete
          exact Or.inl
            ⟨left, right,
              hArityPair.1, hArityPair.2, rfl⟩
      | eqConst index constant =>
          apply Or.inl
          apply atomicSelectionConditions_complete
          exact Or.inr
            ⟨index, constant, hArity,
              (by simpa [Sel.constants] using hConstants),
              rfl⟩
      | not child =>
          apply Or.inr
          rw [Finset.mem_union]
          apply Or.inl
          apply Finset.mem_image.mpr
          refine ⟨child, ?_, rfl⟩
          apply ih child
          · exact hArity
          · exact hConstants
          · simp only [SelectionCondition.nodeCount]
              at hNodes
            omega
      | and leftCondition rightCondition =>
          have hArityPair :
              leftCondition.arityReq < inputArity ∧
                rightCondition.arityReq < inputArity := by
            simpa [Sel.arityReq] using hArity
          apply Or.inr
          rw [Finset.mem_union]
          apply Or.inr
          rw [Finset.mem_union]
          apply Or.inl
          apply Finset.mem_image.mpr
          refine
            ⟨(leftCondition, rightCondition), ?_, rfl⟩
          apply Finset.mem_product.mpr
          constructor
          · apply ih leftCondition
            · exact hArityPair.1
            · intro constant hConstant
              exact hConstants (by
                simp [Sel.constants, hConstant])
            · simp only [SelectionCondition.nodeCount]
                at hNodes
              omega
          · apply ih rightCondition
            · exact hArityPair.2
            · intro constant hConstant
              exact hConstants (by
                simp [Sel.constants, hConstant])
            · simp only [SelectionCondition.nodeCount]
                at hNodes
              omega
      | or leftCondition rightCondition =>
          have hArityPair :
              leftCondition.arityReq < inputArity ∧
                rightCondition.arityReq < inputArity := by
            simpa [Sel.arityReq] using hArity
          apply Or.inr
          rw [Finset.mem_union]
          apply Or.inr
          rw [Finset.mem_union]
          apply Or.inr
          apply Finset.mem_image.mpr
          refine
            ⟨(leftCondition, rightCondition), ?_, rfl⟩
          apply Finset.mem_product.mpr
          constructor
          · apply ih leftCondition
            · exact hArityPair.1
            · intro constant hConstant
              exact hConstants (by
                simp [Sel.constants, hConstant])
            · simp only [SelectionCondition.nodeCount]
                at hNodes
              omega
          · apply ih rightCondition
            · exact hArityPair.2
            · intro constant hConstant
              exact hConstants (by
                simp [Sel.constants, hConstant])
            · simp only [SelectionCondition.nodeCount]
                at hNodes
              omega

@[simp] theorem mem_selectionConditions_iff
    (inputArity : Nat)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (condition : Sel D) :
    condition ∈ selectionConditions inputArity alphabet
        parameters ↔
      SelectionCondition.IsEligible condition inputArity
        alphabet parameters := by
  constructor
  · intro hMember
    have hFiltered :=
      Finset.mem_filter.mp hMember
    have hValid :=
      selectionConditionCandidates_valid
        inputArity alphabet
          parameters.maxSelectionConditionNodes
        hFiltered.1
    exact ⟨hValid.1, hValid.2, hFiltered.2⟩
  · intro hEligible
    apply Finset.mem_filter.mpr
    exact
      ⟨selectionConditionCandidates_complete
          inputArity alphabet
          parameters.maxSelectionConditionNodes
          condition hEligible.1 hEligible.2.1
          hEligible.2.2,
        hEligible.2.2⟩

end FullEnumeration

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Projection Lists and Base Terms
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace FullEnumeration

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Every eligible projection list for one input arity. -/
def projectionLists
    (inputArity : Nat)
    (parameters : Parameters) :
    Finset (List Nat) :=
  listsUpTo (Finset.range inputArity)
    (inputArity + parameters.maxProjectionExcess)

@[simp] theorem mem_projectionLists_iff
    (inputArity : Nat)
    (parameters : Parameters)
    (indices : List Nat) :
    indices ∈ projectionLists inputArity parameters ↔
      ProjectionList.IsEligible indices inputArity
        parameters := by
  rw [projectionLists, mem_listsUpTo_iff]
  simp only [Finset.mem_range]
  constructor
  · rintro ⟨hLength, hIndices⟩
    exact ⟨hIndices, by
      simp only [ProjectionList.excess]
      omega⟩
  · rintro ⟨hIndices, hLength⟩
    exact ⟨by
      simp only [ProjectionList.excess] at hLength
      omega, hIndices⟩

/- All enabled base terms as an order-free finite set. -/
def baseTerms
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Finset (Term D Γ) :=
  let tops : Finset (Term D Γ) :=
    if RABase.top ∈ parameters.enabledRABases then
      {Term.top}
    else
      ∅
  let empties : Finset (Term D Γ) :=
    if RABase.empty ∈ parameters.enabledRABases then
      (emptyArities alphabet parameters).image Term.empty
    else
      ∅
  let relations : Finset (Term D Γ) :=
    if RABase.relation ∈ parameters.enabledRABases then
      alphabet.relations.image Term.relation
    else
      ∅
  let singletons : Finset (Term D Γ) :=
    if RABase.singleton ∈ parameters.enabledRABases then
      alphabet.constants.image Term.singleton
    else
      ∅
  tops ∪ (empties ∪ (relations ∪ singletons))

@[simp] theorem mem_baseTerms_iff
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (term : Term D Γ) :
    term ∈ baseTerms alphabet parameters ↔
      term.IsBaseEligible alphabet parameters := by
  simp only [baseTerms, Finset.mem_union]
  constructor
  · rintro (hTop | hEmpty | hRelation | hSingleton)
    · by_cases hEnabled :
          RABase.top ∈ parameters.enabledRABases
      · have hTerm : term = Term.top := by
          simpa [hEnabled] using hTop
        exact Or.inl ⟨hEnabled, hTerm⟩
      · simp [hEnabled] at hTop
    · by_cases hEnabled :
          RABase.empty ∈ parameters.enabledRABases
      · have hImage :
            term ∈
              (emptyArities alphabet parameters).image
                Term.empty := by
          simpa [hEnabled] using hEmpty
        rcases Finset.mem_image.mp hImage with
          ⟨arity, hArity, hTerm⟩
        exact Or.inr <| Or.inl
          ⟨hEnabled, arity, hArity, hTerm.symm⟩
      · simp [hEnabled] at hEmpty
    · by_cases hEnabled :
          RABase.relation ∈ parameters.enabledRABases
      · have hImage :
            term ∈ alphabet.relations.image
              Term.relation := by
          simpa [hEnabled] using hRelation
        rcases Finset.mem_image.mp hImage with
          ⟨relation, hMember, hTerm⟩
        exact Or.inr <| Or.inr <| Or.inl
          ⟨hEnabled, relation, hMember, hTerm.symm⟩
      · simp [hEnabled] at hRelation
    · by_cases hEnabled :
          RABase.singleton ∈ parameters.enabledRABases
      · have hImage :
            term ∈ alphabet.constants.image
              Term.singleton := by
          simpa [hEnabled] using hSingleton
        rcases Finset.mem_image.mp hImage with
          ⟨constant, hMember, hTerm⟩
        exact Or.inr <| Or.inr <| Or.inr
          ⟨hEnabled, constant, hMember, hTerm.symm⟩
      · simp [hEnabled] at hSingleton
  · rintro (hTop | hEmpty | hRelation | hSingleton)
    · apply Or.inl
      simp [hTop.1, hTop.2]
    · apply Or.inr; apply Or.inl
      rcases hEmpty with
        ⟨hEnabled, arity, hArity, rfl⟩
      rw [if_pos hEnabled]
      apply Finset.mem_image.mpr
      exact ⟨arity, hArity, rfl⟩
    · apply Or.inr; apply Or.inr; apply Or.inl
      rcases hRelation with
        ⟨hEnabled, relation, hMember, rfl⟩
      rw [if_pos hEnabled]
      apply Finset.mem_image.mpr
      exact ⟨relation, hMember, rfl⟩
    · apply Or.inr; apply Or.inr; apply Or.inr
      rcases hSingleton with
        ⟨hEnabled, constant, hMember, rfl⟩
      rw [if_pos hEnabled]
      apply Finset.mem_image.mpr
      exact ⟨constant, hMember, rfl⟩

end FullEnumeration

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Derived-Term Closure
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace FullEnumeration

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Enabled, bounded selections over one finite term set. -/
def selectionTerms
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (source : Finset (Term D Γ)) :
    Finset (Term D Γ) :=
  if RAOperator.selection ∈
      parameters.enabledRAOperators then
    (source.filter fun term =>
      term.arity ≤ parameters.maxOutputArity).biUnion
        fun term =>
          (selectionConditions term.arity alphabet
            parameters).attach.image
            fun condition =>
              Term.select condition.1 term
                ((mem_selectionConditions_iff
                  term.arity alphabet parameters
                  condition.1).mp condition.2).1
  else
    ∅

/- Enabled, bounded projections over one finite term set. -/
def projectionTerms
    (parameters : Parameters)
    (source : Finset (Term D Γ)) :
    Finset (Term D Γ) :=
  if RAOperator.projection ∈
      parameters.enabledRAOperators then
    source.biUnion fun term =>
      ((projectionLists term.arity parameters).filter
        fun indices =>
          indices.length ≤
            parameters.maxOutputArity).attach.image
        fun indices =>
          Term.project indices.1 term
            ((mem_projectionLists_iff
              term.arity parameters indices.1).mp
                (Finset.mem_filter.mp indices.2).1).1
  else
    ∅

/- Enabled, output-bounded products. -/
def productTerms
    (parameters : Parameters)
    (source : Finset (Term D Γ)) :
    Finset (Term D Γ) :=
  if RAOperator.product ∈
      parameters.enabledRAOperators then
    ((source.product source).filter fun pair =>
      pair.1.arity + pair.2.arity ≤
        parameters.maxOutputArity).image fun pair =>
          Term.product pair.1 pair.2
  else
    ∅

/- Equal-arity, output-bounded source pairs. -/
def equalArityPairs
    (parameters : Parameters)
    (source : Finset (Term D Γ)) :
    Finset (Term D Γ × Term D Γ) :=
  (source.product source).filter fun pair =>
    pair.1.arity = pair.2.arity ∧
      pair.1.arity ≤ parameters.maxOutputArity

/- Enabled unions over one finite term set. -/
def unionTerms
    (parameters : Parameters)
    (source : Finset (Term D Γ)) :
    Finset (Term D Γ) :=
  if RAOperator.union ∈
      parameters.enabledRAOperators then
    (equalArityPairs parameters source).attach.image
      fun pair =>
        Term.union pair.1.1 pair.1.2
          (Finset.mem_filter.mp pair.2).2.1
  else
    ∅

/- Enabled differences over one finite term set. -/
def differenceTerms
    (parameters : Parameters)
    (source : Finset (Term D Γ)) :
    Finset (Term D Γ) :=
  if RAOperator.difference ∈
      parameters.enabledRAOperators then
    (equalArityPairs parameters source).attach.image
      fun pair =>
        Term.difference pair.1.1 pair.1.2
          (Finset.mem_filter.mp pair.2).2.1
  else
    ∅

/- All one-step derived terms over one finite source set. -/
def derivedTerms
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (source : Finset (Term D Γ)) :
    Finset (Term D Γ) :=
  selectionTerms alphabet parameters source ∪
    (projectionTerms parameters source ∪
      (productTerms parameters source ∪
        (unionTerms parameters source ∪
          differenceTerms parameters source)))

/-
  All eligible terms of structural cost at most `fuel`.

  The explicit `maxRAOps` filter keeps this helper exact
  even when a caller supplies more fuel than the public
  bound.
-/
def termsThroughCost
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Nat → Finset (Term D Γ)
| 0 => baseTerms alphabet parameters
| fuel + 1 =>
    let prior := termsThroughCost alphabet parameters fuel
    (prior ∪
      derivedTerms alphabet parameters prior).filter
      fun term =>
        term.raCost ≤ fuel + 1 ∧
          term.raCost ≤ parameters.maxRAOps

/- The complete bounded term set for one request. -/
def terms
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Finset (Term D Γ) :=
  termsThroughCost alphabet parameters parameters.maxRAOps

/-
  Membership in the cost closure is sound for
  eligibility.
-/
theorem termsThroughCost_sound
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (fuel : Nat)
    {term : Term D Γ}
    (hMember :
      term ∈ termsThroughCost alphabet parameters fuel) :
    term.IsEligible alphabet parameters ∧
      term.raCost ≤ fuel := by
  induction fuel generalizing term with
  | zero =>
      have hBase :=
        (mem_baseTerms_iff alphabet parameters term).mp
          hMember
      exact
        ⟨Term.isEligible_of_isBaseEligible
            term alphabet parameters hBase,
          by
            rcases hBase with hTop | hEmpty |
                hRelation | hSingleton
            · rw [hTop.2]
              simp
            · rcases hEmpty with
                ⟨_, arity, _, rfl⟩
              simp
            · rcases hRelation with
                ⟨_, relation, _, rfl⟩
              simp
            · rcases hSingleton with
                ⟨_, constant, _, rfl⟩
              simp⟩
  | succ fuel ih =>
      have hFiltered := Finset.mem_filter.mp hMember
      have hCost : term.raCost ≤ fuel + 1 :=
        hFiltered.2.1
      rcases Finset.mem_union.mp hFiltered.1 with
          hPrior | hDerived
      · exact ⟨(ih hPrior).1, hCost⟩
      · unfold derivedTerms at hDerived
        rcases Finset.mem_union.mp hDerived with
            hSelection | hDerived
        · unfold selectionTerms at hSelection
          split at hSelection
          · rename_i hEnabled
            rcases Finset.mem_biUnion.mp hSelection with
              ⟨source, hSourceFiltered, hOutput⟩
            have hSourceMember :=
              (Finset.mem_filter.mp hSourceFiltered).1
            have hOutputBound :=
              (Finset.mem_filter.mp hSourceFiltered).2
            rcases Finset.mem_image.mp hOutput with
              ⟨condition, _, hTerm⟩
            rw [← hTerm] at hCost hFiltered ⊢
            have hCondition :=
              (mem_selectionConditions_iff
                source.arity alphabet parameters
                condition.1).mp condition.2
            exact
              ⟨Term.IsEligible.selection
                  condition.1 source (ih hSourceMember).1
                  hEnabled hCondition hOutputBound
                  (by simpa using hFiltered.2.2),
                hCost⟩
          · simp_all
        · rcases Finset.mem_union.mp hDerived with
              hProjection | hDerived
          · unfold projectionTerms at hProjection
            split at hProjection
            · rename_i hEnabled
              rcases Finset.mem_biUnion.mp hProjection with
                ⟨source, hSourceMember, hOutput⟩
              rcases Finset.mem_image.mp hOutput with
                ⟨indices, _, hTerm⟩
              have hListMember :=
                (Finset.mem_filter.mp indices.2).1
              have hOutputBound :=
                (Finset.mem_filter.mp indices.2).2
              have hIndices :=
                (mem_projectionLists_iff
                  source.arity parameters indices.1).mp
                    hListMember
              rw [← hTerm] at hCost hFiltered ⊢
              exact
                ⟨Term.IsEligible.projection
                    indices.1 source (ih hSourceMember).1
                    hEnabled hIndices hOutputBound
                    (by simpa using hFiltered.2.2),
                  hCost⟩
            · simp_all
          · rcases Finset.mem_union.mp hDerived with
                hProduct | hDerived
            · unfold productTerms at hProduct
              split at hProduct
              · rename_i hEnabled
                rcases Finset.mem_image.mp hProduct with
                  ⟨pair, hPairFiltered, hTerm⟩
                have hPair :=
                  Finset.mem_filter.mp hPairFiltered
                have hSources :=
                  Finset.mem_product.mp hPair.1
                rw [← hTerm] at hCost hFiltered ⊢
                exact
                  ⟨Term.IsEligible.product pair.1 pair.2
                      (ih hSources.1).1 (ih hSources.2).1
                      hEnabled hPair.2
                      (by simpa using hFiltered.2.2),
                    hCost⟩
              · simp_all
            · rcases Finset.mem_union.mp hDerived with
                  hUnion | hDifference
              · unfold unionTerms at hUnion
                split at hUnion
                · rename_i hEnabled
                  rcases Finset.mem_image.mp hUnion with
                    ⟨pair, _, hTerm⟩
                  have hPairFiltered :=
                    Finset.mem_filter.mp pair.2
                  have hSources :=
                    Finset.mem_product.mp hPairFiltered.1
                  rw [← hTerm] at hCost hFiltered ⊢
                  exact
                    ⟨Term.IsEligible.union
                        pair.1.1 pair.1.2
                        hPairFiltered.2.1
                        (ih hSources.1).1 (ih hSources.2).1
                        hEnabled hPairFiltered.2.2
                        (by simpa using hFiltered.2.2),
                      hCost⟩
                · simp_all
              · unfold differenceTerms at hDifference
                split at hDifference
                · rename_i hEnabled
                  rcases
                      Finset.mem_image.mp hDifference with
                    ⟨pair, _, hTerm⟩
                  have hPairFiltered :=
                    Finset.mem_filter.mp pair.2
                  have hSources :=
                    Finset.mem_product.mp hPairFiltered.1
                  rw [← hTerm] at hCost hFiltered ⊢
                  exact
                    ⟨Term.IsEligible.difference
                        pair.1.1 pair.1.2
                        hPairFiltered.2.1
                        (ih hSources.1).1 (ih hSources.2).1
                        hEnabled hPairFiltered.2.2
                        (by simpa using hFiltered.2.2),
                      hCost⟩
                · simp_all

/-
  Every eligible term appears once its structural cost
  fits.
-/
theorem termsThroughCost_complete
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (fuel : Nat)
    {term : Term D Γ}
    (hEligible : term.IsEligible alphabet parameters)
    (hCost : term.raCost ≤ fuel) :
    term ∈ termsThroughCost alphabet parameters fuel := by
  induction fuel generalizing term with
  | zero =>
      rw [termsThroughCost,
        mem_baseTerms_iff]
      cases hEligible with
      | top hEnabled =>
          exact Or.inl ⟨hEnabled, rfl⟩
      | empty arity hEnabled hArity =>
          exact Or.inr <| Or.inl
            ⟨hEnabled, arity, hArity, rfl⟩
      | relation relation hEnabled hRelation =>
          exact Or.inr <| Or.inr <| Or.inl
            ⟨hEnabled, relation, hRelation, rfl⟩
      | singleton constant hEnabled hConstant =>
          exact Or.inr <| Or.inr <| Or.inr
            ⟨hEnabled, constant, hConstant, rfl⟩
      | selection _ source _ _ _ _ _ =>
          simp at hCost
      | projection _ source _ _ _ _ _ =>
          simp at hCost
      | product left right _ _ _ _ _ =>
          simp at hCost
      | union left right _ _ _ _ _ _ =>
          simp at hCost
      | difference left right _ _ _ _ _ _ =>
          simp at hCost
  | succ fuel ih =>
      rw [termsThroughCost]
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_union.mpr
        cases hEligible with
        | top hEnabled =>
            apply Or.inl
            apply ih (Term.IsEligible.top hEnabled)
            simp
        | empty arity hEnabled hArity =>
            apply Or.inl
            apply ih
              (Term.IsEligible.empty arity hEnabled hArity)
            simp
        | relation relation hEnabled hRelation =>
            apply Or.inl
            apply ih
              (Term.IsEligible.relation relation hEnabled
                hRelation)
            simp
        | singleton constant hEnabled hConstant =>
            apply Or.inl
            apply ih
              (Term.IsEligible.singleton constant hEnabled
                hConstant)
            simp
        | selection condition source hSource hEnabled
              hCondition hOutput hBound =>
            apply Or.inr
            unfold derivedTerms
            apply Finset.mem_union.mpr
            apply Or.inl
            unfold selectionTerms
            rw [if_pos hEnabled]
            apply Finset.mem_biUnion.mpr
            have hSourceCost : source.raCost ≤ fuel := by
              simp only [Term.raCost_select] at hCost
              omega
            have hSourceMember := ih hSource hSourceCost
            refine
              ⟨source,
                Finset.mem_filter.mpr
                  ⟨hSourceMember, hOutput⟩, ?_⟩
            have hConditionMember :=
              (mem_selectionConditions_iff
                source.arity alphabet parameters
                condition).mpr hCondition
            let attachedCondition :
                {candidate //
                  candidate ∈ selectionConditions
                    source.arity alphabet parameters} :=
              ⟨condition, hConditionMember⟩
            apply Finset.mem_image.mpr
            refine
              ⟨attachedCondition,
                Finset.mem_attach _ attachedCondition, ?_⟩
            congr 1
        | projection indices source hSource hEnabled
              hIndices hOutput hBound =>
            apply Or.inr
            unfold derivedTerms
            apply Finset.mem_union.mpr
            apply Or.inr
            apply Finset.mem_union.mpr
            apply Or.inl
            unfold projectionTerms
            rw [if_pos hEnabled]
            apply Finset.mem_biUnion.mpr
            have hSourceCost : source.raCost ≤ fuel := by
              simp only [Term.raCost_project] at hCost
              omega
            have hSourceMember := ih hSource hSourceCost
            refine ⟨source, hSourceMember, ?_⟩
            have hIndicesMember :=
              (mem_projectionLists_iff
                source.arity parameters indices).mpr
                  hIndices
            have hFilteredIndices :
                indices ∈
                  (projectionLists source.arity
                    parameters).filter
                    fun candidate =>
                      candidate.length ≤
                        parameters.maxOutputArity :=
              Finset.mem_filter.mpr
                ⟨hIndicesMember, hOutput⟩
            let attachedIndices :
                {candidate //
                  candidate ∈
                    (projectionLists source.arity
                      parameters).filter
                      fun projection =>
                        projection.length ≤
                          parameters.maxOutputArity} :=
              ⟨indices, hFilteredIndices⟩
            apply Finset.mem_image.mpr
            refine
              ⟨attachedIndices,
                Finset.mem_attach _ attachedIndices, ?_⟩
            congr 1
        | product left right hLeft hRight hEnabled
              hOutput hBound =>
            apply Or.inr
            unfold derivedTerms
            apply Finset.mem_union.mpr
            apply Or.inr
            apply Finset.mem_union.mpr
            apply Or.inr
            apply Finset.mem_union.mpr
            apply Or.inl
            unfold productTerms
            rw [if_pos hEnabled]
            have hLeftCost : left.raCost ≤ fuel := by
              simp only [Term.raCost_product] at hCost
              omega
            have hRightCost : right.raCost ≤ fuel := by
              simp only [Term.raCost_product] at hCost
              omega
            have hPair :
                (left, right) ∈
                  (termsThroughCost alphabet parameters
                    fuel).product
                    (termsThroughCost alphabet parameters
                      fuel) :=
              Finset.mem_product.mpr
                ⟨ih hLeft hLeftCost,
                  ih hRight hRightCost⟩
            apply Finset.mem_image.mpr
            exact
              ⟨(left, right),
                Finset.mem_filter.mpr ⟨hPair, hOutput⟩,
                rfl⟩
        | union left right sameArity hLeft hRight
              hEnabled hOutput hBound =>
            apply Or.inr
            unfold derivedTerms
            apply Finset.mem_union.mpr
            apply Or.inr
            apply Finset.mem_union.mpr
            apply Or.inr
            apply Finset.mem_union.mpr
            apply Or.inr
            apply Finset.mem_union.mpr
            apply Or.inl
            unfold unionTerms
            rw [if_pos hEnabled]
            have hLeftCost : left.raCost ≤ fuel := by
              simp only [Term.raCost_union] at hCost
              omega
            have hRightCost : right.raCost ≤ fuel := by
              simp only [Term.raCost_union] at hCost
              omega
            have hPair :
                (left, right) ∈
                  equalArityPairs parameters
                    (termsThroughCost alphabet parameters
                      fuel) := by
              apply Finset.mem_filter.mpr
              exact
                ⟨Finset.mem_product.mpr
                    ⟨ih hLeft hLeftCost,
                      ih hRight hRightCost⟩,
                  ⟨sameArity, hOutput⟩⟩
            let attachedPair :
                {pair // pair ∈
                  equalArityPairs parameters
                    (termsThroughCost alphabet parameters
                      fuel)} :=
              ⟨(left, right), hPair⟩
            apply Finset.mem_image.mpr
            refine
              ⟨attachedPair,
                Finset.mem_attach _ attachedPair, ?_⟩
            congr 1
        | difference left right sameArity hLeft hRight
              hEnabled hOutput hBound =>
            apply Or.inr
            unfold derivedTerms
            apply Finset.mem_union.mpr
            apply Or.inr
            apply Finset.mem_union.mpr
            apply Or.inr
            apply Finset.mem_union.mpr
            apply Or.inr
            apply Finset.mem_union.mpr
            apply Or.inr
            unfold differenceTerms
            rw [if_pos hEnabled]
            have hLeftCost : left.raCost ≤ fuel := by
              simp only [Term.raCost_difference] at hCost
              omega
            have hRightCost : right.raCost ≤ fuel := by
              simp only [Term.raCost_difference] at hCost
              omega
            have hPair :
                (left, right) ∈
                  equalArityPairs parameters
                    (termsThroughCost alphabet parameters
                      fuel) := by
              apply Finset.mem_filter.mpr
              exact
                ⟨Finset.mem_product.mpr
                    ⟨ih hLeft hLeftCost,
                      ih hRight hRightCost⟩,
                  ⟨sameArity, hOutput⟩⟩
            let attachedPair :
                {pair // pair ∈
                  equalArityPairs parameters
                    (termsThroughCost alphabet parameters
                      fuel)} :=
              ⟨(left, right), hPair⟩
            apply Finset.mem_image.mpr
            refine
              ⟨attachedPair,
                Finset.mem_attach _ attachedPair, ?_⟩
            congr 1
      · exact
          ⟨hCost, hEligible.raCost_le⟩

@[simp] theorem mem_termsThroughCost_iff
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (fuel : Nat)
    (term : Term D Γ) :
    term ∈ termsThroughCost alphabet parameters fuel ↔
      term.IsEligible alphabet parameters ∧
        term.raCost ≤ fuel :=
  ⟨termsThroughCost_sound alphabet parameters fuel,
    fun h =>
      termsThroughCost_complete alphabet parameters fuel
        h.1 h.2⟩

@[simp] theorem mem_terms_iff
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (term : Term D Γ) :
    term ∈ terms alphabet parameters ↔
      term.IsEligible alphabet parameters := by
  rw [terms, mem_termsThroughCost_iff]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, h.raCost_le⟩

end FullEnumeration

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Atoms, Literals, and Clause Representations
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace FullEnumeration

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Enabled atoms for one pair of checked terms. -/
def atomsForPair
    (parameters : Parameters)
    (left right : Term D Γ) :
    Finset (Atom D Γ) :=
  if sameArity : left.arity = right.arity then
    parameters.enabledAtomKinds.image fun kind =>
      Atom.ofTerms kind left right sameArity
  else
    ∅

@[simp] theorem mem_atomsForPair_iff
    (parameters : Parameters)
    (left right : Term D Γ)
    (atom : Atom D Γ) :
    atom ∈ atomsForPair parameters left right ↔
      ∃ sameArity : left.arity = right.arity,
        ∃ kind,
          kind ∈ parameters.enabledAtomKinds ∧
            atom =
              Atom.ofTerms kind left right
                sameArity := by
  unfold atomsForPair
  split
  · rename_i sameArity
    constructor
    · intro hMember
      rcases Finset.mem_image.mp hMember with
        ⟨kind, hKind, hAtom⟩
      exact
        ⟨sameArity, kind, hKind, hAtom.symm⟩
    · rintro
        ⟨otherArity, kind, hKind, hAtom⟩
      apply Finset.mem_image.mpr
      refine ⟨kind, hKind, ?_⟩
      rw [hAtom]
  · rename_i differentArity
    constructor
    · simp
    · rintro ⟨sameArity, _⟩
      exact (differentArity sameArity).elim

/- All eligible atoms over the bounded term universe. -/
def atoms
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Finset (Atom D Γ) :=
  let termSet := terms alphabet parameters
  (termSet.product termSet).biUnion fun pair =>
    atomsForPair parameters pair.1 pair.2

@[simp] theorem mem_atoms_iff
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (atom : Atom D Γ) :
    atom ∈ atoms alphabet parameters ↔
      atom.IsEligible alphabet parameters := by
  constructor
  · intro hMember
    rcases Finset.mem_biUnion.mp hMember with
      ⟨pair, hPair, hAtom⟩
    rcases Finset.mem_product.mp hPair with
      ⟨hLeft, hRight⟩
    rcases (mem_atomsForPair_iff
      parameters pair.1 pair.2 atom).mp hAtom with
      ⟨sameArity, kind, hKind, hAtom⟩
    exact
      ⟨kind, hKind, pair.1,
        (mem_terms_iff alphabet parameters pair.1).mp
          hLeft,
        pair.2,
        (mem_terms_iff alphabet parameters pair.2).mp
          hRight,
        sameArity, hAtom⟩
  · rintro
      ⟨kind, hKind, left, hLeft, right, hRight,
        sameArity, hAtom⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(left, right), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨(mem_terms_iff alphabet parameters left).mpr
            hLeft,
          (mem_terms_iff alphabet parameters right).mpr
            hRight⟩
    · exact (mem_atomsForPair_iff
        parameters left right atom).mpr
          ⟨sameArity, kind, hKind, hAtom⟩

/- All enabled signs of every eligible atom. -/
def literals
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Finset (Literal D Γ) :=
  (atoms alphabet parameters).biUnion fun atom =>
    parameters.enabledLiteralSigns.image fun sign =>
      ⟨sign, atom⟩

@[simp] theorem mem_literals_iff
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (literal : Literal D Γ) :
    literal ∈ literals alphabet parameters ↔
      literal.IsEligible alphabet parameters := by
  constructor
  · intro hMember
    rcases Finset.mem_biUnion.mp hMember with
      ⟨atom, hAtom, hLiteral⟩
    rcases Finset.mem_image.mp hLiteral with
      ⟨sign, hSign, hLiteral⟩
    subst literal
    exact
      ⟨hSign,
        (mem_atoms_iff alphabet parameters atom).mp
          hAtom⟩
  · intro hEligible
    apply Finset.mem_biUnion.mpr
    refine ⟨literal.atom, ?_, ?_⟩
    · exact
        (mem_atoms_iff alphabet parameters
          literal.atom).mpr hEligible.2
    · apply Finset.mem_image.mpr
      exact ⟨literal.sign, hEligible.1, by
        cases literal
        rfl⟩

/- Literal-list member of the order-free universe. -/
abbrev Representation
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) :=
  LiteralList D Γ

/- Decode a normalized literal list to its QF clause. -/
def decode
    (representation : Representation D Γ) :
    Clause D Γ :=
  representation.formula

/-
  All normalized eligible literal lists through the width
  bound. Different literal orderings remain explicit. This
  is an internal universe, not protected proposal output.
-/
def representations
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Finset (Representation D Γ) :=
  (listsUpTo (literals alphabet parameters)
      parameters.maxClauseWidth).filter
    fun representation => representation.Nodup

@[simp] theorem mem_representations_iff
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (representation : Representation D Γ) :
    representation ∈ representations alphabet
        parameters ↔
      representation.IsNormalized ∧
        representation.IsEligible alphabet parameters := by
  rw [representations, Finset.mem_filter,
    mem_listsUpTo_iff]
  simp only [LiteralList.IsNormalized,
    LiteralList.IsEligible, mem_literals_iff]
  aesop

/- Every universe representation is normalized. -/
theorem representation_normalized
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {representation : Representation D Γ}
    (hMember :
      representation ∈
        representations alphabet parameters) :
    representation.IsNormalized :=
  ((mem_representations_iff alphabet parameters
    representation).mp hMember).1

/- Every universe representation obeys the full grammar. -/
theorem representation_eligible
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {representation : Representation D Γ}
    (hMember :
      representation ∈
        representations alphabet parameters) :
    representation.IsEligible alphabet parameters :=
  ((mem_representations_iff alphabet parameters
    representation).mp hMember).2

/- The universe contains every eligible literal list. -/
theorem representations_cover
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (representation : Representation D Γ)
    (hNormalized : representation.IsNormalized)
    (hEligible :
      representation.IsEligible alphabet parameters) :
    representation ∈ representations alphabet
        parameters :=
  (mem_representations_iff alphabet parameters
    representation).mpr ⟨hNormalized, hEligible⟩

/- Decode every representation in the finite slice. -/
def clauses
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Finset (Clause D Γ) :=
  (representations alphabet parameters).image decode

end FullEnumeration

end DisjunctiveClause

end Synthesis

end Whiel
