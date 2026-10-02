-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.Spec

/-
  Declarative specification of the full bounded
  disjunctive-clause grammar.

  This module defines structural costs, checked derived-term
  constructors, and parameter-relative eligibility. It does
  not choose an enumeration order or executable container.

  Main declarations:
    * `SelectionCondition.nodeCount` and `IsEligible`
    * `ProjectionList.IsEligible`
    * checked derived constructors in `Term`
    * `Term.IsEligible`
    * full atom, literal, and literal-list eligibility
-/

------------------------------------------------------------
-- Selection and Projection Bounds
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace SelectionCondition

variable {D : Type} [Domain D]

/- Number of syntax nodes in one selection condition. -/
def nodeCount : Sel D → Nat
| .eqIdx _ _ => 1
| .eqConst _ _ => 1
| .and left right =>
    1 + nodeCount left + nodeCount right
| .or left right =>
    1 + nodeCount left + nodeCount right
| .not condition => 1 + nodeCount condition

@[simp] theorem nodeCount_eqIdx
    (left right : Nat) :
    nodeCount (Sel.eqIdx left right : Sel D) = 1 :=
  rfl

@[simp] theorem nodeCount_eqConst
    (index : Nat)
    (constant : D) :
    nodeCount (Sel.eqConst index constant) = 1 :=
  rfl

@[simp] theorem nodeCount_and
    (left right : Sel D) :
    nodeCount (.and left right) =
      1 + nodeCount left + nodeCount right :=
  rfl

@[simp] theorem nodeCount_or
    (left right : Sel D) :
    nodeCount (.or left right) =
      1 + nodeCount left + nodeCount right :=
  rfl

@[simp] theorem nodeCount_not
    (condition : Sel D) :
    nodeCount (.not condition) =
      1 + nodeCount condition :=
  rfl

/- Every selection condition contains at least one node. -/
theorem nodeCount_pos
    (condition : Sel D) :
    0 < nodeCount condition := by
  induction condition <;> simp_all [nodeCount] <;> omega

/-
  A condition is eligible for one input arity when all
  coordinates are valid, all constants come from the finite
  alphabet, and its full syntax-node count is in bounds.
-/
def IsEligible
    {A : Type} [RelationNames A]
    {Γ : UnnamedSchema A}
    (condition : Sel D)
    (inputArity : Nat)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Prop :=
  condition.arityReq < inputArity ∧
    condition.constants ⊆ alphabet.constants ∧
    nodeCount condition ≤
      parameters.maxSelectionConditionNodes

end SelectionCondition

namespace ProjectionList

/- Output-length excess over the input arity. -/
def excess
    (indices : List Nat)
    (inputArity : Nat) : Nat :=
  indices.length - inputArity

/-
  A projection list uses only valid input coordinates and
  respects the projection-excess bound. Excess is the
  output length beyond the input arity, with truncated
  natural-number subtraction. Repeated coordinates are
  permitted by the relational-algebra syntax.
-/
def IsEligible
    (indices : List Nat)
    (inputArity : Nat)
    (parameters : Parameters) :
    Prop :=
  (∀ index ∈ indices, index < inputArity) ∧
    excess indices inputArity ≤
      parameters.maxProjectionExcess

end ProjectionList

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Checked Derived Terms and Structural Cost
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

namespace Term

/- Checked terms are determined by their raw expressions. -/
theorem eq_of_expr_eq
    {left right : Term D Γ}
    (hExpr : left.expr = right.expr) :
    left = right := by
  cases left with
  | mk leftArity leftExpr leftWellFormed =>
      cases right with
      | mk rightArity rightExpr rightWellFormed =>
          simp only at hExpr
          subst rightExpr
          have hArity : leftArity = rightArity := by
            exact Option.some.inj
              (leftWellFormed.symm.trans
                rightWellFormed)
          subst rightArity
          rfl

/- Apply a well-formed selection to a checked term. -/
def select
    (condition : Sel D)
    (term : Term D Γ)
    (hCondition : condition.arityReq < term.arity) :
    Term D Γ where
  arity := term.arity
  expr := .select condition term.expr
  wellFormed := by
    simp [RawRAExpr.arity?, term.wellFormed,
      hCondition]

/- Apply a well-formed projection to a checked term. -/
def project
    (indices : List Nat)
    (term : Term D Γ)
    (hIndices :
      ∀ index ∈ indices, index < term.arity) :
    Term D Γ where
  arity := indices.length
  expr := .proj indices term.expr
  wellFormed := by
    rw [RawRAExpr.arity?, term.wellFormed]
    have hDecide :
        decide
          (∀ index ∈ indices,
            index < term.arity) = true :=
      decide_eq_true hIndices
    simp only [hDecide, if_true]

/- Form the product of two checked terms. -/
def product
    (left right : Term D Γ) :
    Term D Γ where
  arity := left.arity + right.arity
  expr := .prod left.expr right.expr
  wellFormed := by
    simp [RawRAExpr.arity?, left.wellFormed,
      right.wellFormed]

/- Form the union of two equal-arity checked terms. -/
def union
    (left right : Term D Γ)
    (sameArity : left.arity = right.arity) :
    Term D Γ where
  arity := left.arity
  expr := .union left.expr right.expr
  wellFormed := by
    simp [RawRAExpr.arity?, left.wellFormed,
      right.wellFormed, sameArity]

/- Form the difference of two equal-arity checked terms. -/
def difference
    (left right : Term D Γ)
    (sameArity : left.arity = right.arity) :
    Term D Γ where
  arity := left.arity
  expr := .diff left.expr right.expr
  wellFormed := by
    simp [RawRAExpr.arity?, left.wellFormed,
      right.wellFormed, sameArity]

/- Structural RA cost of a checked term. -/
def raCost (term : Term D Γ) : Nat :=
  let rec cost : RawRAExpr A D → Nat
  | .top => 0
  | .empty _ => 0
  | .rel _ => 0
  | .single _ => 0
  | .select _ child => 1 + cost child
  | .proj _ child => 1 + cost child
  | .prod left right =>
      1 + cost left + cost right
  | .union left right =>
      1 + cost left + cost right
  | .diff left right =>
      1 + cost left + cost right
  cost term.expr

@[simp] theorem raCost_top :
    raCost (top : Term D Γ) = 0 :=
  rfl

@[simp] theorem raCost_empty
    (arity : Nat) :
    raCost
        (Term.empty (D := D) (Γ := Γ)
          (arity := arity)) = 0 :=
  rfl

@[simp] theorem raCost_relation
    (relation : Γ.syms) :
    raCost (Term.relation (D := D) relation) = 0 :=
  rfl

@[simp] theorem raCost_singleton
    (constant : D) :
    raCost (singleton (Γ := Γ) constant) = 0 :=
  rfl

@[simp] theorem raCost_select
    (condition : Sel D)
    (term : Term D Γ)
    (hCondition : condition.arityReq < term.arity) :
    raCost (select condition term hCondition) =
      1 + raCost term :=
  rfl

@[simp] theorem raCost_project
    (indices : List Nat)
    (term : Term D Γ)
    (hIndices :
      ∀ index ∈ indices, index < term.arity) :
    raCost (project indices term hIndices) =
      1 + raCost term :=
  rfl

@[simp] theorem raCost_product
    (left right : Term D Γ) :
    raCost (product left right) =
      1 + raCost left + raCost right :=
  rfl

@[simp] theorem raCost_union
    (left right : Term D Γ)
    (sameArity : left.arity = right.arity) :
    raCost (union left right sameArity) =
      1 + raCost left + raCost right :=
  rfl

@[simp] theorem raCost_difference
    (left right : Term D Γ)
    (sameArity : left.arity = right.arity) :
    raCost (difference left right sameArity) =
      1 + raCost left + raCost right :=
  rfl

end Term

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Full Term Grammar
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

namespace Term

/-
  Declarative membership in one bounded full term grammar.

  Base results keep their intrinsic arities. Every derived
  result is bounded by `maxOutputArity`. The structural cost
  premise applies to the complete derived term.
-/
inductive IsEligible
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Term D Γ → Prop
| top
    (hEnabled :
      RABase.top ∈ parameters.enabledRABases) :
    IsEligible alphabet parameters Term.top
| empty
    (arity : Nat)
    (hEnabled :
      RABase.empty ∈ parameters.enabledRABases)
    (hArity :
      arity ∈ emptyArities alphabet parameters) :
    IsEligible alphabet parameters (Term.empty arity)
| relation
    (relation : Γ.syms)
    (hEnabled :
      RABase.relation ∈ parameters.enabledRABases)
    (hRelation : relation ∈ alphabet.relations) :
    IsEligible alphabet parameters
      (Term.relation relation)
| singleton
    (constant : D)
    (hEnabled :
      RABase.singleton ∈ parameters.enabledRABases)
    (hConstant : constant ∈ alphabet.constants) :
    IsEligible alphabet parameters
      (Term.singleton constant)
| selection
    (condition : Sel D)
    (term : Term D Γ)
    (hTerm : IsEligible alphabet parameters term)
    (hEnabled :
      RAOperator.selection ∈
        parameters.enabledRAOperators)
    (hCondition :
      SelectionCondition.IsEligible condition
        term.arity alphabet parameters)
    (hOutput :
      term.arity ≤ parameters.maxOutputArity)
    (hCost :
      1 + term.raCost ≤ parameters.maxRAOps) :
    IsEligible alphabet parameters
      (Term.select condition term hCondition.1)
| projection
    (indices : List Nat)
    (term : Term D Γ)
    (hTerm : IsEligible alphabet parameters term)
    (hEnabled :
      RAOperator.projection ∈
        parameters.enabledRAOperators)
    (hIndices :
      ProjectionList.IsEligible indices term.arity
        parameters)
    (hOutput :
      indices.length ≤ parameters.maxOutputArity)
    (hCost :
      1 + term.raCost ≤ parameters.maxRAOps) :
    IsEligible alphabet parameters
      (Term.project indices term hIndices.1)
| product
    (left right : Term D Γ)
    (hLeft : IsEligible alphabet parameters left)
    (hRight : IsEligible alphabet parameters right)
    (hEnabled :
      RAOperator.product ∈
        parameters.enabledRAOperators)
    (hOutput :
      left.arity + right.arity ≤
        parameters.maxOutputArity)
    (hCost :
      1 + left.raCost + right.raCost ≤
        parameters.maxRAOps) :
    IsEligible alphabet parameters
      (Term.product left right)
| union
    (left right : Term D Γ)
    (sameArity : left.arity = right.arity)
    (hLeft : IsEligible alphabet parameters left)
    (hRight : IsEligible alphabet parameters right)
    (hEnabled :
      RAOperator.union ∈
        parameters.enabledRAOperators)
    (hOutput :
      left.arity ≤ parameters.maxOutputArity)
    (hCost :
      1 + left.raCost + right.raCost ≤
        parameters.maxRAOps) :
    IsEligible alphabet parameters
      (Term.union left right sameArity)
| difference
    (left right : Term D Γ)
    (sameArity : left.arity = right.arity)
    (hLeft : IsEligible alphabet parameters left)
    (hRight : IsEligible alphabet parameters right)
    (hEnabled :
      RAOperator.difference ∈
        parameters.enabledRAOperators)
    (hOutput :
      left.arity ≤ parameters.maxOutputArity)
    (hCost :
      1 + left.raCost + right.raCost ≤
        parameters.maxRAOps) :
    IsEligible alphabet parameters
      (Term.difference left right sameArity)

/-
  Every eligible term respects the structural-cost bound.
-/
theorem IsEligible.raCost_le
    {alphabet : Alphabet D Γ}
    {parameters : Parameters}
    {term : Term D Γ}
    (hEligible : term.IsEligible alphabet parameters) :
    term.raCost ≤ parameters.maxRAOps := by
  induction hEligible <;> simp_all

/- Every base-eligible term belongs to the full grammar. -/
theorem isEligible_of_isBaseEligible
    (term : Term D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (hEligible :
      term.IsBaseEligible alphabet parameters) :
    term.IsEligible alphabet parameters := by
  rcases hEligible with hTop | hEmpty | hRelation |
      hSingleton
  · rw [hTop.2]
    exact .top hTop.1
  · rcases hEmpty with
      ⟨hEnabled, arity, hArity, rfl⟩
    exact .empty arity hEnabled hArity
  · rcases hRelation with
      ⟨hEnabled, relation, hRelation, rfl⟩
    exact .relation relation hEnabled hRelation
  · rcases hSingleton with
      ⟨hEnabled, constant, hConstant, rfl⟩
    exact .singleton constant hEnabled hConstant

/-
  At structural cost zero, the full grammar contains only
  enabled base terms.
-/
theorem isBaseEligible_of_isEligible_of_maxRAOps_eq_zero
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (hMaxCost : parameters.maxRAOps = 0)
    {term : Term D Γ}
    (hEligible : term.IsEligible alphabet parameters) :
    term.IsBaseEligible alphabet parameters := by
  induction hEligible with
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
  | selection _ _ _ _ _ _ hCost =>
      omega
  | projection _ _ _ _ _ _ hCost =>
      omega
  | product _ _ _ _ _ _ hCost =>
      omega
  | union _ _ _ _ _ _ _ hCost =>
      omega
  | difference _ _ _ _ _ _ _ hCost =>
      omega

/- Full and base term eligibility agree at cost zero. -/
theorem isEligible_iff_isBaseEligible_of_maxRAOps_eq_zero
    (term : Term D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (hMaxCost : parameters.maxRAOps = 0) :
    term.IsEligible alphabet parameters ↔
      term.IsBaseEligible alphabet parameters :=
  ⟨isBaseEligible_of_isEligible_of_maxRAOps_eq_zero
      alphabet parameters hMaxCost,
    isEligible_of_isBaseEligible
      term alphabet parameters⟩

end Term

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Full Atom, Literal, and Clause Eligibility
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  An atom is eligible when it is an enabled comparison of
  two equal-arity terms from the full bounded grammar.
-/
def Atom.IsEligible
    (atom : Atom D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Prop :=
  ∃ kind,
    kind ∈ parameters.enabledAtomKinds ∧
      ∃ left,
        left.IsEligible alphabet parameters ∧
          ∃ right,
            right.IsEligible alphabet parameters ∧
              ∃ sameArity :
                  left.arity = right.arity,
                atom =
                  Atom.ofTerms kind left right
                    sameArity

/- A literal has an enabled sign and an eligible atom. -/
def Literal.IsEligible
    (literal : Literal D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Prop :=
  literal.sign ∈ parameters.enabledLiteralSigns ∧
    literal.atom.IsEligible alphabet parameters

/-
  A full-slice literal list is width-bounded and contains
  only eligible literals. Normalization remains separate.
-/
def LiteralList.IsEligible
    (literalList : LiteralList D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Prop :=
  literalList.length ≤ parameters.maxClauseWidth ∧
    ∀ literal ∈ literalList,
      literal.IsEligible alphabet parameters

/- Base-eligible atoms are eligible in the full grammar. -/
theorem Atom.isEligible_of_isBaseEligible
    (atom : Atom D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (hEligible :
      atom.IsBaseEligible alphabet parameters) :
    atom.IsEligible alphabet parameters := by
  rcases hEligible with
    ⟨kind, hKind, left, hLeft, right, hRight,
      sameArity, hAtom⟩
  exact
    ⟨kind, hKind, left,
      Term.isEligible_of_isBaseEligible
        left alphabet parameters hLeft,
      right,
      Term.isEligible_of_isBaseEligible
        right alphabet parameters hRight,
      sameArity, hAtom⟩

namespace Atom

/- Full and base atom eligibility agree at RA cost zero. -/
theorem isEligible_iff_isBaseEligible_of_maxRAOps_eq_zero
    (atom : Atom D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (hMaxCost : parameters.maxRAOps = 0) :
    atom.IsEligible alphabet parameters ↔
      atom.IsBaseEligible alphabet parameters := by
  constructor
  · rintro
      ⟨kind, hKind, left, hLeft, right, hRight,
        sameArity, hAtom⟩
    exact
      ⟨kind, hKind, left,
        (
Term.isEligible_iff_isBaseEligible_of_maxRAOps_eq_zero
          left alphabet parameters hMaxCost).mp hLeft,
        right,
        (
Term.isEligible_iff_isBaseEligible_of_maxRAOps_eq_zero
          right alphabet parameters hMaxCost).mp hRight,
        sameArity, hAtom⟩
  · exact atom.isEligible_of_isBaseEligible
      alphabet parameters

end Atom

/-
  Base-eligible literals are eligible in the full grammar.
-/
theorem Literal.isEligible_of_isBaseEligible
    (literal : Literal D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (hEligible :
      literal.IsBaseEligible alphabet parameters) :
    literal.IsEligible alphabet parameters :=
  ⟨hEligible.1,
    literal.atom.isEligible_of_isBaseEligible
      alphabet parameters hEligible.2⟩

namespace Literal

/- Full and base literal eligibility agree at cost zero. -/
theorem isEligible_iff_isBaseEligible_of_maxRAOps_eq_zero
    (literal : Literal D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (hMaxCost : parameters.maxRAOps = 0) :
    literal.IsEligible alphabet parameters ↔
      literal.IsBaseEligible alphabet parameters := by
  simp only [Literal.IsEligible,
    Literal.IsBaseEligible]
  exact and_congr_right fun _ =>
Atom.isEligible_iff_isBaseEligible_of_maxRAOps_eq_zero
      literal.atom alphabet parameters hMaxCost

end Literal

/-
  Every base-eligible literal list is eligible in the full
  grammar under the same parameters.
-/
theorem LiteralList.isEligible_of_isBaseEligible
    (literalList : LiteralList D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (hEligible :
      literalList.IsBaseEligible alphabet parameters) :
    literalList.IsEligible alphabet parameters := by
  refine ⟨hEligible.1, ?_⟩
  intro literal hLiteral
  exact
    literal.isEligible_of_isBaseEligible
      alphabet parameters
      (hEligible.2 literal hLiteral)

namespace LiteralList

/-
  Full and base literal-list eligibility agree at RA cost
  zero.
-/
theorem isEligible_iff_isBaseEligible_of_maxRAOps_eq_zero
    (literalList : LiteralList D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (hMaxCost : parameters.maxRAOps = 0) :
    literalList.IsEligible alphabet parameters ↔
      literalList.IsBaseEligible alphabet parameters := by
  simp only [LiteralList.IsEligible,
    LiteralList.IsBaseEligible]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro literal
  apply forall_congr'
  intro _
  exact
Literal.isEligible_iff_isBaseEligible_of_maxRAOps_eq_zero
      literal alphabet parameters hMaxCost

end LiteralList

end DisjunctiveClause

end Synthesis

end Whiel
