-- Author: Jesse Comer
import Whiel.AssertExpr.Semantics

/-
  Schema-changing relation-name relabeling for finite
  quantifier-free assertions.

  A relabeling carries every source symbol to a target
  symbol of the same arity. Relational expressions and
  guards are translated structurally, and evaluation pulls
  target instances back along the same name map.
-/

------------------------------------------------------------
-- Schema Relabelings
------------------------------------------------------------

namespace UnnamedSchema

variable {A B : Type}
variable [RelationNames A] [RelationNames B]

/- An arity-preserving map between schema symbols. -/
structure Relabeling
    (source : UnnamedSchema A)
    (target : UnnamedSchema B) where
  name : A -> B
  maps : ∀ relation, relation ∈ source.syms ->
    name relation ∈ target.syms
  arity_eq : ∀ relation hSource,
    source.arity ⟨relation, hSource⟩ =
      target.arity
        ⟨name relation, maps relation hSource⟩

namespace Relabeling

/- Map one checked source symbol to the target schema. -/
def symbol
    {source : UnnamedSchema A}
    {target : UnnamedSchema B}
    (rho : Relabeling source target)
    (relation : source.syms) : target.syms :=
  ⟨rho.name relation.1,
    rho.maps relation.1 relation.2⟩

/- Checked symbols retain their arity. -/
theorem arity_symbol
    {source : UnnamedSchema A}
    {target : UnnamedSchema B}
    (rho : Relabeling source target)
    (relation : source.syms) :
    source.arity relation =
      target.arity (rho.symbol relation) :=
  rho.arity_eq relation.1 relation.2

/- A mapped raw name has the source arity lookup. -/
theorem arity?_name_of_mem
    {source : UnnamedSchema A}
    {target : UnnamedSchema B}
    (rho : Relabeling source target)
    (relation : A)
    (hSource : relation ∈ source.syms) :
    target.arity? (rho.name relation) =
      source.arity? relation := by
  unfold UnnamedSchema.arity?
  rw [dif_pos (rho.maps relation hSource),
    dif_pos hSource]
  exact congrArg some
    (rho.arity_eq relation hSource).symm

/- Compose arity-preserving schema relabelings. -/
def comp
    {C : Type}
    [RelationNames C]
    {source : UnnamedSchema A}
    {middle : UnnamedSchema B}
    {target : UnnamedSchema C}
    (outer : Relabeling middle target)
    (inner : Relabeling source middle) :
    Relabeling source target where
  name := fun relation =>
    outer.name (inner.name relation)
  maps := by
    intro relation hSource
    exact outer.maps (inner.name relation)
      (inner.maps relation hSource)
  arity_eq := by
    intro relation hSource
    exact (inner.arity_eq relation hSource).trans
      (outer.arity_eq (inner.name relation)
        (inner.maps relation hSource))

/- Relabelings are determined by their name maps. -/
theorem eq_of_name_eq
    {source : UnnamedSchema A}
    {target : UnnamedSchema B}
    {left right : Relabeling source target}
    (hName : ∀ relation,
      left.name relation = right.name relation) :
    left = right := by
  cases left with
  | mk leftName leftMaps leftArity =>
      cases right with
      | mk rightName rightMaps rightArity =>
          have hNames : leftName = rightName := by
            funext relation
            exact hName relation
          cases hNames
          rfl

end Relabeling
end UnnamedSchema

------------------------------------------------------------
-- Instance Pullback
------------------------------------------------------------

namespace Instance

variable {A B D : Type}
variable [RelationNames A] [RelationNames B] [Domain D]
variable {source : UnnamedSchema A}
variable {target : UnnamedSchema B}

/- Pull a target instance back along one relabeling. -/
def onRelabeling
    (rho : UnnamedSchema.Relabeling source target)
    (state : Instance D target) : Instance D source :=
  fun relation =>
    cast
      (congrArg (FinRelation D)
        (rho.arity_symbol relation).symm)
      (state (rho.symbol relation))

/- Lookup respects equality of checked symbols. -/
theorem cast_lookup_eq_of_eq
    {Gamma : UnnamedSchema A}
    (state : Instance D Gamma)
    {left right : Gamma.syms}
    (hEq : left = right) :
    cast
        (congrArg (FinRelation D)
          (congrArg Gamma.arity hEq))
        (state left) =
      state right := by
  cases hEq
  rfl

/- Pullback reverses relabeling composition. -/
theorem onRelabeling_comp
    {C : Type}
    [RelationNames C]
    {source : UnnamedSchema A}
    {middle : UnnamedSchema B}
    {target : UnnamedSchema C}
    (outer : UnnamedSchema.Relabeling middle target)
    (inner : UnnamedSchema.Relabeling source middle)
    (state : Instance D target) :
    onRelabeling (outer.comp inner) state =
      onRelabeling inner (onRelabeling outer state) := by
  apply Instance.ext
  intro relation
  unfold onRelabeling
  symm
  calc
    cast
          (congrArg (FinRelation D)
            (inner.arity_symbol relation).symm)
          (cast
            (congrArg (FinRelation D)
              (outer.arity_symbol
                (inner.symbol relation)).symm)
            (state
              (outer.symbol
                (inner.symbol relation)))) =
        cast
          (congrArg (FinRelation D)
            ((outer.arity_symbol
                (inner.symbol relation)).symm.trans
              (inner.arity_symbol relation).symm))
          (state
            (outer.symbol
              (inner.symbol relation))) := by
      exact FinRelation.cast_trans
        (outer.arity_symbol
          (inner.symbol relation)).symm
        (inner.arity_symbol relation).symm _
    _ =
        cast
          (congrArg (FinRelation D)
            ((outer.comp inner).arity_symbol
              relation).symm)
          (state ((outer.comp inner).symbol relation)) := by
      rfl

/- Pullbacks agree when their name maps agree. -/
theorem onRelabeling_eq_of_name_eq
    {source : UnnamedSchema A}
    {target : UnnamedSchema B}
    (left right :
      UnnamedSchema.Relabeling source target)
    (hName : ∀ relation,
      left.name relation = right.name relation)
    (state : Instance D target) :
    onRelabeling left state =
      onRelabeling right state := by
  have hRelabeling : left = right :=
    UnnamedSchema.Relabeling.eq_of_name_eq hName
  cases hRelabeling
  rfl

/- A same-schema pullback preserves a fixed symbol. -/
theorem onRelabeling_apply_of_name_eq
    {Gamma : UnnamedSchema A}
    (rho : UnnamedSchema.Relabeling Gamma Gamma)
    (state : Instance D Gamma)
    (relation : Gamma.syms)
    (hName : rho.name relation.1 = relation.1) :
    onRelabeling rho state relation =
      state relation := by
  unfold onRelabeling
  have hSymbol : rho.symbol relation = relation := by
    apply Subtype.ext
    exact hName
  calc
    cast
          (congrArg (FinRelation D)
            (rho.arity_symbol relation).symm)
          (state (rho.symbol relation)) =
        cast
          (congrArg (FinRelation D)
            (congrArg Gamma.arity hSymbol))
          (state (rho.symbol relation)) := by
      exact FinRelation.cast_proof_irrel
        (rho.arity_symbol relation).symm
        (congrArg Gamma.arity hSymbol) _
    _ = state relation :=
      cast_lookup_eq_of_eq state hSymbol

end Instance

------------------------------------------------------------
-- Relational-Expression Relabeling
------------------------------------------------------------

namespace RawRAExpr

variable {A B D : Type}
variable [RelationNames A] [RelationNames B] [Domain D]

/- Relabel every relation occurrence structurally. -/
def onRelabeling
    {source : UnnamedSchema A}
    {target : UnnamedSchema B}
    (rho : UnnamedSchema.Relabeling source target) :
    RawRAExpr A D -> RawRAExpr B D
| .top => .top
| .empty n => .empty n
| .rel relation => .rel (rho.name relation)
| .single value => .single value
| .select condition expr =>
    .select condition (onRelabeling rho expr)
| .proj indices expr =>
    .proj indices (onRelabeling rho expr)
| .prod left right =>
    .prod (onRelabeling rho left)
      (onRelabeling rho right)
| .union left right =>
    .union (onRelabeling rho left)
      (onRelabeling rho right)
| .diff left right =>
    .diff (onRelabeling rho left)
      (onRelabeling rho right)

/- Structural relabeling preserves inferred arity. -/
theorem arity?_onRelabeling
    {source : UnnamedSchema A}
    {target : UnnamedSchema B}
    (rho : UnnamedSchema.Relabeling source target)
    (expr : RawRAExpr A D)
    (hSymbols : expr.symbols ⊆ source.syms) :
    (expr.onRelabeling rho).arity? target =
      expr.arity? source := by
  induction expr with
  | top => rfl
  | empty _ => rfl
  | rel relation =>
      exact rho.arity?_name_of_mem relation
        (hSymbols (by simp [RawRAExpr.symbols]))
  | single _ => rfl
  | select condition expr ih =>
      simp only [onRelabeling, arity?]
      rw [ih (by simpa [symbols] using hSymbols)]
  | proj indices expr ih =>
      simp only [onRelabeling, arity?]
      rw [ih (by simpa [symbols] using hSymbols)]
  | prod left right ihLeft ihRight =>
      have hLeft : left.symbols ⊆ source.syms := by
        intro name hName
        exact hSymbols
          (Finset.mem_union_left _ hName)
      have hRight : right.symbols ⊆ source.syms := by
        intro name hName
        exact hSymbols
          (Finset.mem_union_right _ hName)
      simp only [onRelabeling, arity?]
      rw [ihLeft hLeft, ihRight hRight]
  | union left right ihLeft ihRight =>
      have hLeft : left.symbols ⊆ source.syms := by
        intro name hName
        exact hSymbols
          (Finset.mem_union_left _ hName)
      have hRight : right.symbols ⊆ source.syms := by
        intro name hName
        exact hSymbols
          (Finset.mem_union_right _ hName)
      simp only [onRelabeling, arity?]
      rw [ihLeft hLeft, ihRight hRight]
  | diff left right ihLeft ihRight =>
      have hLeft : left.symbols ⊆ source.syms := by
        intro name hName
        exact hSymbols
          (Finset.mem_union_left _ hName)
      have hRight : right.symbols ⊆ source.syms := by
        intro name hName
        exact hSymbols
          (Finset.mem_union_right _ hName)
      simp only [onRelabeling, arity?]
      rw [ihLeft hLeft, ihRight hRight]

/- Evaluation pulls back along the same relabeling. -/
theorem eval?_onRelabeling
    {source : UnnamedSchema A}
    {target : UnnamedSchema B}
    (rho : UnnamedSchema.Relabeling source target)
    (expr : RawRAExpr A D)
    (hSymbols : expr.symbols ⊆ source.syms)
    (state : Instance D target) :
    (expr.onRelabeling rho).eval? state =
      expr.eval?
        (Instance.onRelabeling rho state) := by
  induction expr with
  | top => rfl
  | empty _ => rfl
  | rel relation =>
      have hSource : relation ∈ source.syms :=
        hSymbols (by simp [symbols])
      have hTarget :
          rho.name relation ∈ target.syms :=
        rho.maps relation hSource
      simp only [onRelabeling, eval?,
        Instance.relation?, hSource, hTarget,
        dite_true]
      apply congrArg some
      apply Sigma.ext
        (rho.arity_eq relation hSource).symm
      simp [Instance.onRelabeling,
        UnnamedSchema.Relabeling.symbol]
  | single _ => rfl
  | select condition expr ih =>
      simp only [onRelabeling, eval?]
      rw [ih (by simpa [symbols] using hSymbols)]
  | proj indices expr ih =>
      simp only [onRelabeling, eval?]
      rw [ih (by simpa [symbols] using hSymbols)]
  | prod left right ihLeft ihRight =>
      have hLeft : left.symbols ⊆ source.syms := by
        intro name hName
        exact hSymbols
          (Finset.mem_union_left _ hName)
      have hRight : right.symbols ⊆ source.syms := by
        intro name hName
        exact hSymbols
          (Finset.mem_union_right _ hName)
      simp only [onRelabeling, eval?]
      rw [ihLeft hLeft, ihRight hRight]
  | union left right ihLeft ihRight =>
      have hLeft : left.symbols ⊆ source.syms := by
        intro name hName
        exact hSymbols
          (Finset.mem_union_left _ hName)
      have hRight : right.symbols ⊆ source.syms := by
        intro name hName
        exact hSymbols
          (Finset.mem_union_right _ hName)
      simp only [onRelabeling, eval?]
      rw [ihLeft hLeft, ihRight hRight]
  | diff left right ihLeft ihRight =>
      have hLeft : left.symbols ⊆ source.syms := by
        intro name hName
        exact hSymbols
          (Finset.mem_union_left _ hName)
      have hRight : right.symbols ⊆ source.syms := by
        intro name hName
        exact hSymbols
          (Finset.mem_union_right _ hName)
      simp only [onRelabeling, eval?]
      rw [ihLeft hLeft, ihRight hRight]

end RawRAExpr

namespace RAExpr

variable {A B D : Type}
variable [RelationNames A] [RelationNames B] [Domain D]
variable {source : UnnamedSchema A}
variable {target : UnnamedSchema B}
variable {n : Nat}

/- Relabel a well-typed relational expression. -/
def onRelabeling
    (rho : UnnamedSchema.Relabeling source target)
    (expr : RAExpr D source n) : RAExpr D target n where
  expr := expr.expr.onRelabeling rho
  wf := by
    rw [RawRAExpr.arity?_onRelabeling rho expr.expr
      expr.symbols_subset]
    exact expr.wf

/- Typed evaluation respects structural relabeling. -/
@[simp] theorem eval_onRelabeling
    (rho : UnnamedSchema.Relabeling source target)
    (expr : RAExpr D source n)
    (state : Instance D target) :
    (expr.onRelabeling rho).eval state =
      expr.eval
        (Instance.onRelabeling rho state) := by
  have hMapped := RAExpr.raw_eval?_eq_eval
    (expr.onRelabeling rho) state
  have hSource := RAExpr.raw_eval?_eq_eval expr
    (Instance.onRelabeling rho state)
  change
    (expr.expr.onRelabeling rho).eval? state = _
      at hMapped
  rw [RawRAExpr.eval?_onRelabeling rho expr.expr
      expr.symbols_subset,
    hSource] at hMapped
  injection hMapped with hSigma
  injection hSigma with _hAr hEval
  exact hEval.symm

end RAExpr

------------------------------------------------------------
-- Guard Relabeling
------------------------------------------------------------

namespace Whiel
namespace Guard

variable {A B D : Type}
variable [RelationNames A] [RelationNames B] [Domain D]
variable {source : UnnamedSchema A}
variable {target : UnnamedSchema B}

/- Relabel a guard through an arity-preserving map. -/
def onRelabeling
    (rho : UnnamedSchema.Relabeling source target) :
    Guard D source -> Guard D target
| .«true» => .«true»
| .«false» => .«false»
| .eq left right =>
    .eq (left.onRelabeling rho)
      (right.onRelabeling rho)
| .subset left right =>
    .subset (left.onRelabeling rho)
      (right.onRelabeling rho)
| .and left right =>
    .and (onRelabeling rho left)
      (onRelabeling rho right)
| .or left right =>
    .or (onRelabeling rho left)
      (onRelabeling rho right)
| .not formula =>
    .not (onRelabeling rho formula)

/- Guard evaluation pulls back along its relabeling. -/
@[simp] theorem eval_onRelabeling
    (rho : UnnamedSchema.Relabeling source target)
    (formula : Guard D source)
    (state : Instance D target) :
    (formula.onRelabeling rho).eval state ↔
      formula.eval
        (Instance.onRelabeling rho state) := by
  induction formula with
  | «true» => rfl
  | «false» => rfl
  | eq left right =>
      simp [onRelabeling, Guard.eval]
  | subset left right =>
      simp [onRelabeling, Guard.eval]
  | and left right ihLeft ihRight =>
      simp [onRelabeling, Guard.eval,
        ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [onRelabeling, Guard.eval,
        ihLeft, ihRight]
  | not formula ih =>
      simp [onRelabeling, Guard.eval, ih]

end Guard
end Whiel
