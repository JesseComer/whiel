-- Author: Jesse Comer
import Whiel.AssertExpr.PrettyPrint
import Whiel.Synthesis.DisjunctiveClause.FastContract
import Whiel.Synthesis.DisjunctiveClause.Coverage
import Whiel.Synthesis.Runtime.Task

/-
  Typed registration boundary for the readable reference
  enumerator.

  Rust receives only opaque source identities, complete
  structural identities, display syntax, and solver keys.
  The formulas remain typed Lean values owned by a compiled
  task worker.
-/

------------------------------------------------------------
-- Ordered Reference Slices
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace ReferenceProposal

open DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

/- Current reference-enumerator wire contract. -/
def version : Nat := 3

/- Ordered typed formulas underlying one cumulative reference slice. -/
private def rawFormulas
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    List (QFAssertExpr D Γ) :=
  (CanonicalEnumeration.boundedLiteralLists alphabet
      (referenceParameters stage)).map
    DisjunctiveClause.FullEnumeration.decode

/- Number of formulas before exact formula deduplication. -/
def rawFormulaCount
    (alphabet : Alphabet D Γ)
    (stage : Nat) : Nat :=
  (rawFormulas alphabet stage).length

/- Duplicate-free ordered formulas in one cumulative reference slice. -/
def formulas
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    List (QFAssertExpr D Γ) :=
  (rawFormulas alphabet stage).dedup

/- Number of formulas in the duplicate-free cumulative slice. -/
def canonicalFormulaCount
    (alphabet : Alphabet D Γ)
    (stage : Nat) : Nat :=
  (formulas alphabet stage).length

/- Every cumulative ordered slice has no duplicate formula. -/
theorem formulas_nodup
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    (formulas alphabet stage).Nodup := by
  exact List.nodup_dedup _

/- The ordered boundary has exactly the reference slice. -/
theorem mem_formulas_iff
    (alphabet : Alphabet D Γ)
    (stage : Nat)
    (formula : QFAssertExpr D Γ) :
    formula ∈ formulas alphabet stage ↔
      formula ∈ referenceProposal alphabet stage := by
  simp [formulas, referenceProposal, proposalFor,
    rawFormulas,
    CanonicalEnumeration.clauses,
    CanonicalEnumeration.representations]

/-
  The reference realization supports itself: its cumulative
  slices cover every finite reference proposal, from
  schedule cofinality and proposal monotonicity alone.
-/
theorem formulas_coversReference
    (alphabet : Alphabet D Γ) :
    FastEnumerator.CoversReference alphabet
      (formulas alphabet) := by
  intro parameters
  rcases referenceParameters_isCofinal parameters with
    ⟨firstStage, hDominates⟩
  refine ⟨firstStage, ?_⟩
  intro formula hFormula
  refine ⟨formula, ?_, QFAssertExpr.equiv_refl _⟩
  have hSlice : formula ∈ referenceProposal alphabet firstStage :=
    proposalFor_mono alphabet
      (hDominates firstStage (Nat.le_refl _)) hFormula
  exact
    (mem_formulas_iff alphabet firstStage formula).mpr hSlice

/- Cumulative ordered reference slices retain every earlier formula. -/
theorem mem_formulas_mono
    (alphabet : Alphabet D Γ)
    {smaller larger : Nat}
    (hStages : smaller ≤ larger)
    {formula : QFAssertExpr D Γ}
    (hFormula : formula ∈ formulas alphabet smaller) :
    formula ∈ formulas alphabet larger := by
  rw [mem_formulas_iff] at hFormula ⊢
  change formula ∈
      CanonicalEnumeration.clauses alphabet
        (referenceParameters smaller) at hFormula
  change formula ∈
      CanonicalEnumeration.clauses alphabet
        (referenceParameters larger)
  rcases Finset.mem_image.mp hFormula with
    ⟨representation, hRepresentation, rfl⟩
  have hNormalized :=
    CanonicalEnumeration.representation_normalized
      alphabet (referenceParameters smaller) hRepresentation
  have hEligible :=
    CanonicalEnumeration.representation_eligible
      alphabet (referenceParameters smaller) hRepresentation
  have hLargerRepresentation :
      CanonicalEnumeration.canonicalize representation ∈
        CanonicalEnumeration.representations alphabet
          (referenceParameters larger) :=
    CanonicalEnumeration.canonicalize_mem_representations
      alphabet (referenceParameters larger) representation
        hNormalized
        (hEligible.mono (referenceParameters_mono hStages))
  have hSame :=
    CanonicalEnumeration.canonicalize_sameLiterals
      representation hNormalized
  have hCanonical :
      CanonicalEnumeration.canonicalize representation =
        representation :=
    hSame.eq_of_pairwise'
      (Finset.pairwise_sort _ _)
      (CanonicalEnumeration.representation_pairwise
        alphabet (referenceParameters smaller) hRepresentation)
  apply Finset.mem_image.mpr
  exact
    ⟨CanonicalEnumeration.canonicalize representation,
      hLargerRepresentation,
      congrArg DisjunctiveClause.FullEnumeration.decode hCanonical⟩

/- Exact formulas introduced by one reference stage. -/
def wave
    (alphabet : Alphabet D Γ) :
    Nat → List (QFAssertExpr D Γ)
| 0 => formulas alphabet 0
| stage + 1 =>
    (formulas alphabet (stage + 1)).filter fun formula =>
      formula ∉ formulas alphabet stage

/- Number of formulas emitted by one exact incremental wave. -/
def waveFormulaCount
    (alphabet : Alphabet D Γ)
    (stage : Nat) : Nat :=
  (wave alphabet stage).length

@[simp] theorem wave_zero
    (alphabet : Alphabet D Γ) :
    wave alphabet 0 = formulas alphabet 0 :=
  rfl

@[simp] theorem mem_wave_succ
    (alphabet : Alphabet D Γ)
    (stage : Nat)
    (formula : QFAssertExpr D Γ) :
    formula ∈ wave alphabet (stage + 1) ↔
      formula ∈ formulas alphabet (stage + 1) ∧
        formula ∉ formulas alphabet stage := by
  simp [wave]

/- Each exact reference wave has no duplicate formula. -/
theorem wave_nodup
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    (wave alphabet stage).Nodup := by
  cases stage with
  | zero => exact formulas_nodup alphabet 0
  | succ stage =>
      exact (formulas_nodup alphabet (stage + 1)).filter _

/- Concatenate all exact waves through one completed stage. -/
def accumulatedWaves
    (alphabet : Alphabet D Γ) :
    Nat → List (QFAssertExpr D Γ)
| 0 => wave alphabet 0
| stage + 1 =>
    accumulatedWaves alphabet stage ++ wave alphabet (stage + 1)

/- Accumulated exact waves are extensionally the cumulative slice. -/
theorem mem_accumulatedWaves_iff
    (alphabet : Alphabet D Γ)
    (stage : Nat)
    (formula : QFAssertExpr D Γ) :
    formula ∈ accumulatedWaves alphabet stage ↔
      formula ∈ formulas alphabet stage := by
  induction stage with
  | zero => simp [accumulatedWaves]
  | succ stage ih =>
      rw [accumulatedWaves, List.mem_append, ih,
        mem_wave_succ]
      constructor
      · intro h
        rcases h with hOld | hNew
        · exact mem_formulas_mono alphabet (Nat.le_succ stage) hOld
        · exact hNew.1
      · intro hFormula
        by_cases hOld : formula ∈ formulas alphabet stage
        · exact Or.inl hOld
        · exact Or.inr ⟨hFormula, hOld⟩

/- No formula is repeated across accumulated exact waves. -/
theorem accumulatedWaves_nodup
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    (accumulatedWaves alphabet stage).Nodup := by
  induction stage with
  | zero => exact wave_nodup alphabet 0
  | succ stage ih =>
      rw [accumulatedWaves, List.nodup_append]
      refine ⟨ih, wave_nodup alphabet (stage + 1), ?_⟩
      intro old hAccumulated new hWave hEqual
      subst new
      have hOld : old ∈ formulas alphabet stage :=
        (mem_accumulatedWaves_iff alphabet stage old).mp
          hAccumulated
      exact ((mem_wave_succ alphabet stage old).mp hWave).2 hOld

/- Canonical semantic coverage lifts to the accumulated waves. -/
theorem eventually_canonical_subset_accumulatedWaves
    (input : QFAssertExpr D Γ)
    (alphabet : Alphabet D Γ)
    (hRelations :
      ∀ relation : Γ.syms,
        relation ∈ alphabet.relations)
    (hConstants :
      input.constants ⊆ alphabet.constants) :
    ∃ firstStage, ∀ stage,
      firstStage ≤ stage →
        ∀ formula ∈
          DisjunctiveClause.CNF.canonicalCandidate input,
          formula ∈ accumulatedWaves alphabet stage := by
  rcases
      DisjunctiveClause.CNF.eventually_canonical_subset_referenceProposal
        input alphabet hRelations hConstants with
    ⟨firstStage, hCoverage⟩
  refine ⟨firstStage, ?_⟩
  intro stage hStage formula hFormula
  apply (mem_accumulatedWaves_iff alphabet stage formula).mpr
  apply (mem_formulas_iff alphabet stage formula).mpr
  exact hCoverage stage hStage hFormula

end ReferenceProposal
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Exact Structural Identities
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace ReferenceProposal

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable [SolverKey A] [SolverKey D]

/- Solver-key structural syntax for selections. -/
inductive StructuralSelection where
| eqIdx (left right : Nat)
| eqConst (index : Nat) (valueKey : String)
| and (left right : StructuralSelection)
| or (left right : StructuralSelection)
| not (selection : StructuralSelection)
deriving DecidableEq, Repr

/- Solver-key structural syntax for relational expressions. -/
inductive StructuralExpression where
| top
| empty (arity : Nat)
| rel (relationKey : String)
| single (valueKey : String)
| select
    (selection : StructuralSelection)
    (expression : StructuralExpression)
| proj (indices : List Nat) (expression : StructuralExpression)
| prod (left right : StructuralExpression)
| union (left right : StructuralExpression)
| diff (left right : StructuralExpression)
deriving DecidableEq, Repr

/- Solver-key structural syntax for quantifier-free assertions. -/
inductive StructuralGuard where
| «true»
| «false»
| eq (left right : StructuralExpression)
| subset (left right : StructuralExpression)
| eqEmptyRight (expression : StructuralExpression)
| eqEmptyLeft (expression : StructuralExpression)
| subsetEmptyRight (expression : StructuralExpression)
| subsetEmptyLeft (expression : StructuralExpression)
| and (left right : StructuralGuard)
| or (left right : StructuralGuard)
| not (formula : StructuralGuard)
deriving DecidableEq, Repr

/- Replace every domain value in a selection by its injective key. -/
def structuralSelection : Sel D → StructuralSelection
| .eqIdx left right => .eqIdx left right
| .eqConst index value => .eqConst index (SolverKey.key value)
| .and left right =>
    .and (structuralSelection left) (structuralSelection right)
| .or left right =>
    .or (structuralSelection left) (structuralSelection right)
| .not selection => .not (structuralSelection selection)

/- Replace every symbol in an expression by its injective key. -/
def structuralExpression : RawRAExpr A D → StructuralExpression
| .top => .top
| .empty arity => .empty arity
| .rel relation => .rel (SolverKey.key relation)
| .single value => .single (SolverKey.key value)
| .select selection expression =>
    .select (structuralSelection selection)
      (structuralExpression expression)
| .proj indices expression =>
    .proj indices (structuralExpression expression)
| .prod left right =>
    .prod (structuralExpression left) (structuralExpression right)
| .union left right =>
    .union (structuralExpression left) (structuralExpression right)
| .diff left right =>
    .diff (structuralExpression left) (structuralExpression right)

/- Replace every symbol in a raw guard by its injective key. -/
def structuralGuard : RawGuard A D → StructuralGuard
| .«true» => .«true»
| .«false» => .«false»
| .eq left right =>
    .eq (structuralExpression left) (structuralExpression right)
| .subset left right =>
    .subset (structuralExpression left) (structuralExpression right)
| .eqEmptyRight expression =>
    .eqEmptyRight (structuralExpression expression)
| .eqEmptyLeft expression =>
    .eqEmptyLeft (structuralExpression expression)
| .subsetEmptyRight expression =>
    .subsetEmptyRight (structuralExpression expression)
| .subsetEmptyLeft expression =>
    .subsetEmptyLeft (structuralExpression expression)
| .and left right =>
    .and (structuralGuard left) (structuralGuard right)
| .or left right =>
    .or (structuralGuard left) (structuralGuard right)
| .not formula => .not (structuralGuard formula)

/- Solver-key replacement does not identify distinct selections. -/
theorem structuralSelection_injective :
    Function.Injective (@structuralSelection D _ _) := by
  intro left right h
  induction left generalizing right with
  | eqIdx left right =>
      cases right with
      | eqIdx otherLeft otherRight =>
          injection h with hLeft hRight
          simp_all
      | eqConst | and | or | not => cases h
  | eqConst index value =>
      cases right with
      | eqConst otherIndex otherValue =>
          injection h with hIndex hValue
          have := SolverKey.key_injective hValue
          simp_all
      | eqIdx | and | or | not => cases h
  | and left right leftIH rightIH =>
      cases right with
      | and otherLeft otherRight =>
          injection h with hLeft hRight
          rw [leftIH hLeft, rightIH hRight]
      | eqIdx | eqConst | or | not => cases h
  | or left right leftIH rightIH =>
      cases right with
      | or otherLeft otherRight =>
          injection h with hLeft hRight
          rw [leftIH hLeft, rightIH hRight]
      | eqIdx | eqConst | and | not => cases h
  | not selection selectionIH =>
      cases right with
      | not other =>
          injection h with hSelection
          rw [selectionIH hSelection]
      | eqIdx | eqConst | and | or => cases h

/- Solver-key replacement does not identify distinct expressions. -/
theorem structuralExpression_injective :
    Function.Injective (@structuralExpression A D _ _ _ _) := by
  intro left right h
  induction left generalizing right with
  | top =>
      cases right with
      | top => rfl
      | empty | rel | single | select | proj | prod | union | diff => cases h
  | empty arity =>
      cases right with
      | empty other => injection h with hArity; simp_all
      | top | rel | single | select | proj | prod | union | diff => cases h
  | rel relation =>
      cases right with
      | rel other =>
          injection h with hRelation
          have := SolverKey.key_injective hRelation
          simp_all
      | top | empty | single | select | proj | prod | union | diff => cases h
  | single value =>
      cases right with
      | single other =>
          injection h with hValue
          have := SolverKey.key_injective hValue
          simp_all
      | top | empty | rel | select | proj | prod | union | diff => cases h
  | select selection expression expressionIH =>
      cases right with
      | select otherSelection otherExpression =>
          injection h with hSelection hExpression
          rw [structuralSelection_injective hSelection,
            expressionIH hExpression]
      | top | empty | rel | single | proj | prod | union | diff => cases h
  | proj indices expression expressionIH =>
      cases right with
      | proj otherIndices otherExpression =>
          injection h with hIndices hExpression
          rw [hIndices, expressionIH hExpression]
      | top | empty | rel | single | select | prod | union | diff => cases h
  | prod left right leftIH rightIH =>
      cases right with
      | prod otherLeft otherRight =>
          injection h with hLeft hRight
          rw [leftIH hLeft, rightIH hRight]
      | top | empty | rel | single | select | proj | union | diff => cases h
  | union left right leftIH rightIH =>
      cases right with
      | union otherLeft otherRight =>
          injection h with hLeft hRight
          rw [leftIH hLeft, rightIH hRight]
      | top | empty | rel | single | select | proj | prod | diff => cases h
  | diff left right leftIH rightIH =>
      cases right with
      | diff otherLeft otherRight =>
          injection h with hLeft hRight
          rw [leftIH hLeft, rightIH hRight]
      | top | empty | rel | single | select | proj | prod | union => cases h

/- Solver-key replacement does not identify distinct raw guards. -/
theorem structuralGuard_injective :
    Function.Injective (@structuralGuard A D _ _ _ _) := by
  intro left right h
  induction left generalizing right with
  | «true» =>
      cases right with
      | «true» => rfl
      | «false» | eq | subset | eqEmptyRight | eqEmptyLeft |
          subsetEmptyRight | subsetEmptyLeft | and | or | not => cases h
  | «false» =>
      cases right with
      | «false» => rfl
      | «true» | eq | subset | eqEmptyRight | eqEmptyLeft |
          subsetEmptyRight | subsetEmptyLeft | and | or | not => cases h
  | eq left right =>
      cases right with
      | eq otherLeft otherRight =>
          injection h with hLeft hRight
          rw [structuralExpression_injective hLeft,
            structuralExpression_injective hRight]
      | «true» | «false» | subset | eqEmptyRight |
          eqEmptyLeft | subsetEmptyRight | subsetEmptyLeft | and | or |
          not => cases h
  | subset left right =>
      cases right with
      | subset otherLeft otherRight =>
          injection h with hLeft hRight
          rw [structuralExpression_injective hLeft,
            structuralExpression_injective hRight]
      | «true» | «false» | eq | eqEmptyRight |
          eqEmptyLeft | subsetEmptyRight | subsetEmptyLeft | and | or |
          not => cases h
  | eqEmptyRight expression =>
      cases right with
      | eqEmptyRight other =>
          injection h with hExpression
          rw [structuralExpression_injective hExpression]
      | «true» | «false» | eq | subset | eqEmptyLeft |
          subsetEmptyRight | subsetEmptyLeft | and | or | not => cases h
  | eqEmptyLeft expression =>
      cases right with
      | eqEmptyLeft other =>
          injection h with hExpression
          rw [structuralExpression_injective hExpression]
      | «true» | «false» | eq | subset | eqEmptyRight |
          subsetEmptyRight | subsetEmptyLeft | and | or | not => cases h
  | subsetEmptyRight expression =>
      cases right with
      | subsetEmptyRight other =>
          injection h with hExpression
          rw [structuralExpression_injective hExpression]
      | «true» | «false» | eq | subset | eqEmptyRight |
          eqEmptyLeft | subsetEmptyLeft | and | or | not => cases h
  | subsetEmptyLeft expression =>
      cases right with
      | subsetEmptyLeft other =>
          injection h with hExpression
          rw [structuralExpression_injective hExpression]
      | «true» | «false» | eq | subset | eqEmptyRight |
          eqEmptyLeft | subsetEmptyRight | and | or | not => cases h
  | and left right leftIH rightIH =>
      cases right with
      | and otherLeft otherRight =>
          injection h with hLeft hRight
          rw [leftIH hLeft, rightIH hRight]
      | «true» | «false» | eq | subset | eqEmptyRight |
          eqEmptyLeft | subsetEmptyRight | subsetEmptyLeft | or | not =>
          cases h
  | or left right leftIH rightIH =>
      cases right with
      | or otherLeft otherRight =>
          injection h with hLeft hRight
          rw [leftIH hLeft, rightIH hRight]
      | «true» | «false» | eq | subset | eqEmptyRight |
          eqEmptyLeft | subsetEmptyRight | subsetEmptyLeft | and | not =>
          cases h
  | not formula formulaIH =>
      cases right with
      | not other =>
          injection h with hFormula
          rw [formulaIH hFormula]
      | «true» | «false» | eq | subset | eqEmptyRight |
          eqEmptyLeft | subsetEmptyRight | subsetEmptyLeft | and | or =>
          cases h

/- Complete, unhashed structural identity of a typed formula. -/
def identity
    {Γ : UnnamedSchema A}
    (formula : QFAssertExpr D Γ) : StructuralGuard :=
  structuralGuard formula.toRaw

/- Structural identities uniquely determine typed formulas. -/
theorem identity_injective
    {Γ : UnnamedSchema A} :
    Function.Injective (@identity A D _ _ _ _ Γ) := by
  intro left right h
  apply Guard.eq_of_toRaw_eq
  exact structuralGuard_injective h

private def natListJson : List Nat → Lean.Json
| [] => Lean.Json.arr #[Lean.Json.str "nil"]
| value :: rest =>
    Lean.Json.arr #[Lean.Json.str "cons",
      Lean.Json.str (toString value), natListJson rest]

/- Serialize one structural selection without hashing. -/
def StructuralSelection.toJson : StructuralSelection → Lean.Json
| .eqIdx left right =>
    Lean.Json.arr #[Lean.Json.str "eq_idx",
      Lean.Json.str (toString left), Lean.Json.str (toString right)]
| .eqConst index valueKey =>
    Lean.Json.arr #[Lean.Json.str "eq_const",
      Lean.Json.str (toString index), Lean.Json.str valueKey]
| .and left right =>
    Lean.Json.arr #[Lean.Json.str "and", left.toJson, right.toJson]
| .or left right =>
    Lean.Json.arr #[Lean.Json.str "or", left.toJson, right.toJson]
| .not selection =>
    Lean.Json.arr #[Lean.Json.str "not", selection.toJson]

/- Serialize one structural relational expression without hashing. -/
def StructuralExpression.toJson : StructuralExpression → Lean.Json
| .top => Lean.Json.arr #[Lean.Json.str "top"]
| .empty arity =>
    Lean.Json.arr #[Lean.Json.str "empty", Lean.Json.str (toString arity)]
| .rel relationKey =>
    Lean.Json.arr #[Lean.Json.str "rel", Lean.Json.str relationKey]
| .single valueKey =>
    Lean.Json.arr #[Lean.Json.str "single", Lean.Json.str valueKey]
| .select selection expression =>
    Lean.Json.arr #[Lean.Json.str "select",
      selection.toJson, expression.toJson]
| .proj indices expression =>
    Lean.Json.arr #[Lean.Json.str "proj",
      natListJson indices, expression.toJson]
| .prod left right =>
    Lean.Json.arr #[Lean.Json.str "prod", left.toJson, right.toJson]
| .union left right =>
    Lean.Json.arr #[Lean.Json.str "union", left.toJson, right.toJson]
| .diff left right =>
    Lean.Json.arr #[Lean.Json.str "diff", left.toJson, right.toJson]

/- Serialize one structural guard without hashing. -/
def StructuralGuard.toJson : StructuralGuard → Lean.Json
| .«true» => Lean.Json.arr #[Lean.Json.str "true"]
| .«false» => Lean.Json.arr #[Lean.Json.str "false"]
| .eq left right =>
    Lean.Json.arr #[Lean.Json.str "eq", left.toJson, right.toJson]
| .subset left right =>
    Lean.Json.arr #[Lean.Json.str "subset", left.toJson, right.toJson]
| .eqEmptyRight expression =>
    Lean.Json.arr #[Lean.Json.str "eq_empty_right", expression.toJson]
| .eqEmptyLeft expression =>
    Lean.Json.arr #[Lean.Json.str "eq_empty_left", expression.toJson]
| .subsetEmptyRight expression =>
    Lean.Json.arr #[Lean.Json.str "subset_empty_right", expression.toJson]
| .subsetEmptyLeft expression =>
    Lean.Json.arr #[Lean.Json.str "subset_empty_left", expression.toJson]
| .and left right =>
    Lean.Json.arr #[Lean.Json.str "and", left.toJson, right.toJson]
| .or left right =>
    Lean.Json.arr #[Lean.Json.str "or", left.toJson, right.toJson]
| .not formula =>
    Lean.Json.arr #[Lean.Json.str "not", formula.toJson]

/- Structural selection serialization is injective. -/
private theorem natString_eq
    {left right : Nat} :
    toString left = toString right ↔ left = right :=
  ⟨Nat.repr_injective, congrArg toString⟩

theorem StructuralSelection.toJson_injective :
    Function.Injective StructuralSelection.toJson := by
  intro left right h
  induction left generalizing right <;>
    cases right <;>
    simp_all [StructuralSelection.toJson]
  all_goals aesop

@[simp] theorem StructuralSelection.toJson_eq
    {left right : StructuralSelection} :
    left.toJson = right.toJson ↔ left = right :=
  StructuralSelection.toJson_injective.eq_iff

private theorem natListJson_injective :
    Function.Injective natListJson := by
  intro left right h
  induction left generalizing right <;>
    cases right <;> simp_all [natListJson]
  all_goals aesop

@[simp] private theorem natListJson_eq
    {left right : List Nat} :
    natListJson left = natListJson right ↔ left = right :=
  natListJson_injective.eq_iff

/- Structural expression serialization is injective. -/
theorem StructuralExpression.toJson_injective :
    Function.Injective StructuralExpression.toJson := by
  intro left right h
  induction left generalizing right <;>
    cases right <;>
    simp_all [StructuralExpression.toJson]
  all_goals aesop

@[simp] theorem StructuralExpression.toJson_eq
    {left right : StructuralExpression} :
    left.toJson = right.toJson ↔ left = right :=
  StructuralExpression.toJson_injective.eq_iff

/- The structured wire identity is itself injective. -/
theorem StructuralGuard.toJson_injective :
    Function.Injective StructuralGuard.toJson := by
  intro left right h
  induction left generalizing right <;>
    cases right <;> simp_all [StructuralGuard.toJson]
  all_goals aesop

@[simp] theorem StructuralGuard.toJson_eq
    {left right : StructuralGuard} :
    left.toJson = right.toJson ↔ left = right :=
  StructuralGuard.toJson_injective.eq_iff

/- Equal wire identities uniquely determine typed formulas. -/
theorem identityJson_injective
    {Γ : UnnamedSchema A} :
    Function.Injective
      (fun formula : QFAssertExpr D Γ =>
        (identity formula).toJson) := by
  intro left right h
  apply identity_injective
  exact StructuralGuard.toJson_injective h

end ReferenceProposal
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Trusted Proposal Entries
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace ReferenceProposal

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]
variable [SolverKey A] [SolverKey D]

/- One typed entry retained behind the worker boundary. -/
structure Entry where
  sourceId : String
  identity : StructuralGuard
  display : String
  formula : QFAssertExpr D Γ

/- Stable source identity for one task, stage, and ordinal. -/
def sourceId
    (taskCanonicalId : String)
    (stage : Nat)
    (ordinal : Nat) : String :=
  "symbolic.reference:" ++ taskCanonicalId ++
    ":v" ++ toString version ++
    ":s" ++ toString stage ++
    ":o" ++ toString ordinal

private def entriesFromFormulasAux
    (taskCanonicalId : String)
    (stage : Nat) :
    Nat → List (QFAssertExpr D Γ) →
      List (Entry (D := D) (Γ := Γ))
| _, [] => []
| ordinal, formula :: rest =>
    { sourceId := sourceId taskCanonicalId stage ordinal
      identity := identity formula
      display := formula.pretty
      formula } ::
    entriesFromFormulasAux taskCanonicalId stage
      (ordinal + 1) rest

/- Add trusted transport metadata to an ordered formula list. -/
def entriesFromFormulas
    (taskCanonicalId : String)
    (stage : Nat)
    (proposal : List (QFAssertExpr D Γ)) :
    List (Entry (D := D) (Γ := Γ)) :=
  entriesFromFormulasAux taskCanonicalId stage 0 proposal

/- One shared evaluation of a reference stage and its counts. -/
structure StageBatch where
  entries : List (Entry (D := D) (Γ := Γ))
  rawFormulaCount : Nat
  canonicalFormulaCount : Nat

/- Evaluate the current cumulative slice only once per worker request. -/
def stageBatch
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (stage : Nat) : StageBatch (D := D) (Γ := Γ) :=
  let raw := rawFormulas alphabet stage
  let canonical := raw.dedup
  let emitted := match stage with
    | 0 => canonical
    | prior + 1 =>
        canonical.filter fun formula =>
          formula ∉ (rawFormulas alphabet prior).dedup
  { entries := entriesFromFormulas taskCanonicalId stage emitted
    rawFormulaCount := raw.length
    canonicalFormulaCount := canonical.length }

omit [LinearOrder A] [LinearOrder D] in
private theorem formulas_entriesFromFormulasAux
    (taskCanonicalId : String)
    (stage ordinal : Nat)
    (proposal : List (QFAssertExpr D Γ)) :
    (entriesFromFormulasAux taskCanonicalId stage ordinal
      proposal).map Entry.formula = proposal := by
  induction proposal generalizing ordinal with
  | nil => rfl
  | cons formula rest ih =>
      simp [entriesFromFormulasAux, ih]

/- Registration preserves the exact ordered typed formula list. -/
omit [LinearOrder A] [LinearOrder D] in
theorem formulas_entriesFromFormulas
    (taskCanonicalId : String)
    (stage : Nat)
    (proposal : List (QFAssertExpr D Γ)) :
    (entriesFromFormulas taskCanonicalId stage proposal).map
      Entry.formula = proposal := by
  exact formulas_entriesFromFormulasAux taskCanonicalId stage 0 proposal

/- Typed entries for one exact incremental reference wave. -/
def entries
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (stage : Nat) : List (Entry (D := D) (Γ := Γ)) :=
  entriesFromFormulas taskCanonicalId stage
    (wave alphabet stage)

/- The executable stage batch emits exactly the proved reference wave. -/
@[simp] theorem stageBatch_entries_eq_entries
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (stage : Nat) :
    (stageBatch taskCanonicalId alphabet stage).entries =
      entries taskCanonicalId alphabet stage := by
  cases stage <;> rfl

/- The executable raw count is the reference raw-slice count. -/
@[simp] theorem stageBatch_rawFormulaCount
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (stage : Nat) :
    (stageBatch taskCanonicalId alphabet stage).rawFormulaCount =
      rawFormulaCount alphabet stage := by
  cases stage <;> rfl

/- The executable canonical count is the reference canonical-slice count. -/
@[simp] theorem stageBatch_canonicalFormulaCount
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (stage : Nat) :
    (stageBatch taskCanonicalId alphabet stage).canonicalFormulaCount =
      canonicalFormulaCount alphabet stage := by
  cases stage <;> rfl

/- Entry formulas have exactly the incremental wave. -/
theorem exists_entry_iff_mem_wave
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (stage : Nat)
    (formula : QFAssertExpr D Γ) :
    (∃ entry ∈ entries taskCanonicalId alphabet stage,
      entry.formula = formula) ↔
      formula ∈ wave alphabet stage := by
  change
    (∃ entry, entry ∈ entriesFromFormulas taskCanonicalId stage
        (wave alphabet stage) ∧ entry.formula = formula) ↔
      formula ∈ wave alphabet stage
  constructor
  · rintro ⟨entry, hEntry, rfl⟩
    rw [← formulas_entriesFromFormulas taskCanonicalId stage
      (wave alphabet stage)]
    exact List.mem_map_of_mem hEntry
  · intro hFormula
    rw [← formulas_entriesFromFormulas taskCanonicalId stage
      (wave alphabet stage)] at hFormula
    obtain ⟨entry, hEntry, hFormula⟩ := List.mem_map.mp hFormula
    exact ⟨entry, hEntry, hFormula⟩

omit [LinearOrder A] [LinearOrder D] in
private theorem display_eq_pretty_of_mem_entriesFromFormulasAux
    (taskCanonicalId : String)
    (stage ordinal : Nat)
    (proposal : List (QFAssertExpr D Γ))
    (entry : Entry (D := D) (Γ := Γ))
    (hEntry : entry ∈
      entriesFromFormulasAux taskCanonicalId stage ordinal proposal) :
    entry.display = entry.formula.pretty := by
  induction proposal generalizing ordinal with
  | nil => simp [entriesFromFormulasAux] at hEntry
  | cons formula rest ih =>
      simp only [entriesFromFormulasAux, List.mem_cons] at hEntry
      rcases hEntry with hHead | hTail
      · subst entry
        rfl
      · exact ih (ordinal + 1) hTail

/- Every entry display is generated from its retained typed formula. -/
omit [LinearOrder A] [LinearOrder D] in
theorem display_eq_pretty_of_mem_entriesFromFormulas
    (taskCanonicalId : String)
    (stage : Nat)
    (proposal : List (QFAssertExpr D Γ))
    (entry : Entry (D := D) (Γ := Γ))
    (hEntry : entry ∈
      entriesFromFormulas taskCanonicalId stage proposal) :
    entry.display = entry.formula.pretty := by
  exact display_eq_pretty_of_mem_entriesFromFormulasAux
    taskCanonicalId stage 0 proposal entry hEntry

end ReferenceProposal
end Runtime
end Synthesis
end Whiel
