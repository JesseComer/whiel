-- Author: Jesse Comer
import Whiel.AssertExpr.Semantics
import Databases.UnnamedRA.Substitution

/-
  Relation-symbol substitution for Whiel assertions.

  Key definitions include:
    * `Whiel.QFAssertExpr.subst`
    * `Whiel.AssertExpr.substFree`
    * `Whiel.AssertExpr.FreeSubstSpec`

  Correctness is proven by:
    * `Whiel.QFAssertExpr.subst_eval`
    * `Whiel.AssertExpr.substFree_correct`
    * `Whiel.AssertExpr.substFree_eval_iff`
-/

------------------------------------------------------------
-- Quantifier-Free Assertion Substitution
------------------------------------------------------------

namespace Whiel

namespace QFAssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Δ : UnnamedSchema A}

/- Substitute an RA expression for a relation symbol. -/
def subst
    (φ : QFAssertExpr D Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    QFAssertExpr D Γ :=
  match φ with
  | .«true» => .«true»
  | .«false» => .«false»
  | .eq e₁ e₂ =>
      .eq (e₁.subst X eRep) (e₂.subst X eRep)
  | .subset e₁ e₂ =>
      .subset (e₁.subst X eRep) (e₂.subst X eRep)
  | .and φ ψ => .and (subst φ X eRep) (subst ψ X eRep)
  | .or φ ψ => .or (subst φ X eRep) (subst ψ X eRep)
  | .not φ => .not (subst φ X eRep)

/- Substitution is identity when the symbol is absent. -/
theorem subst_vacuous
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    (φ : QFAssertExpr D Γ) →
      X.1 ∉ φ.symbols →
        subst φ X eRep = φ
| .«true», _ => by
    rfl
| .«false», _ => by
    rfl
| .eq e₁ e₂, h => by
    have hPair :
        X.1 ∉ e₁.symbols ∧
          X.1 ∉ e₂.symbols := by
      simpa [QFAssertExpr.symbols, Guard.symbols] using h
    simp [subst, RAExpr.subst_vacuous X eRep e₁ hPair.1,
      RAExpr.subst_vacuous X eRep e₂ hPair.2]
| .subset e₁ e₂, h => by
    have hPair :
        X.1 ∉ e₁.symbols ∧
          X.1 ∉ e₂.symbols := by
      simpa [QFAssertExpr.symbols, Guard.symbols] using h
    simp [subst, RAExpr.subst_vacuous X eRep e₁ hPair.1,
      RAExpr.subst_vacuous X eRep e₂ hPair.2]
| .and φ ψ, h => by
    have hPair :
        X.1 ∉ φ.symbols ∧ X.1 ∉ ψ.symbols := by
      simpa [QFAssertExpr.symbols, Guard.symbols] using h
    simp [subst, subst_vacuous X eRep φ hPair.1,
      subst_vacuous X eRep ψ hPair.2]
| .or φ ψ, h => by
    have hPair :
        X.1 ∉ φ.symbols ∧ X.1 ∉ ψ.symbols := by
      simpa [QFAssertExpr.symbols, Guard.symbols] using h
    simp [subst, subst_vacuous X eRep φ hPair.1,
      subst_vacuous X eRep ψ hPair.2]
| .not φ, h => by
    simp [subst, subst_vacuous X eRep φ h]

/- QF substitution corresponds to one instance update. -/
theorem subst_eval
    (I : Instance D Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    (φ : QFAssertExpr D Γ) →
      (subst φ X eRep).eval I ↔
        φ.eval
          (Instance.update I X (eRep.eval I))
| .«true» => by
    rfl
| .«false» => by
    rfl
| .eq e₁ e₂ => by
    change
      (e₁.subst X eRep).eval I =
          (e₂.subst X eRep).eval I ↔
        e₁.eval
            (Instance.update I X (eRep.eval I)) =
          e₂.eval
            (Instance.update I X (eRep.eval I))
    rw [RAExpr.subst_eval e₁ I X eRep,
      RAExpr.subst_eval e₂ I X eRep]
| .subset e₁ e₂ => by
    change
      (e₁.subst X eRep).eval I ⊆
          (e₂.subst X eRep).eval I ↔
        e₁.eval
            (Instance.update I X (eRep.eval I)) ⊆
          e₂.eval
            (Instance.update I X (eRep.eval I))
    rw [RAExpr.subst_eval e₁ I X eRep,
      RAExpr.subst_eval e₂ I X eRep]
| .and φ ψ => by
    exact and_congr
      (subst_eval I X eRep φ)
      (subst_eval I X eRep ψ)
| .or φ ψ => by
    exact or_congr
      (subst_eval I X eRep φ)
      (subst_eval I X eRep ψ)
| .not φ => by
    exact not_congr (subst_eval I X eRep φ)

end QFAssertExpr

end Whiel

------------------------------------------------------------
-- Full Assertion Substitution
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Δ : UnnamedSchema A}

/- Correctness contract for free-symbol substitution. -/
def FreeSubstSpec
    (ψ φ : AssertExpr D Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) : Prop :=
  ∀ I : Instance D Γ,
    ψ.eval I ↔
      φ.eval
        (Instance.update I X (eRep.eval I))

/-
  Retype a substitution expression over an arbitrary
  extending schema, with output arity adjusted to the lifted
  target.
-/
def liftRA
    (hExt : Δ.extensionOf Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    RAExpr D Δ
      (Δ.arity (UnnamedSchema.symOfExtension hExt X)) :=
  RAExpr.castArity
    (UnnamedSchema.arity_eq_of_extensionOf hExt X)
    (eRep.onExtension hExt)

/- Substitute inside the full quantifier-free body. -/
def substFree
    (φ : AssertExpr D Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    AssertExpr D Γ :=
  {
    fullSchema := φ.fullSchema
    extendsFree := φ.extendsFree
    formula :=
      φ.formula.subst
        (UnnamedSchema.symOfExtension φ.extendsFree X)
        (liftRA φ.extendsFree X eRep)
  }

/- `substFree` leaves the quantified schema unchanged. -/
@[simp] theorem substFree_fullSchema
    (φ : AssertExpr D Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    (φ.substFree X eRep).fullSchema = φ.fullSchema :=
  rfl

/- `substFree` leaves the extension witness unchanged. -/
@[simp] theorem substFree_extendsFree
    (φ : AssertExpr D Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    (φ.substFree X eRep).extendsFree = φ.extendsFree :=
  rfl

private theorem reduct_eq_of_extends
    (hExt : Δ.extensionOf Γ)
    {I : Instance D Γ}
    {J : Instance D Δ}
    (hM : Instance.Extends hExt I J) :
    Instance.reduct hExt J = I := by
  apply Instance.ext
  intro X
  apply Finset.ext
  intro t
  rw [Instance.reduct_mem_iff]
  rw [hM (UnnamedSchema.symOfExtension hExt X) X.2]
  rw [Instance.relationOfExtension_mem_iff]
  have hCast :
      Tuple.castArity
          (UnnamedSchema.arity_eq_of_extension_mem hExt
            (UnnamedSchema.symOfExtension hExt X) X.2)
          (Tuple.toExtension hExt X t) = t := by
    let hAr := UnnamedSchema.arity_eq_of_extensionOf hExt X
    let hMem :=
      UnnamedSchema.arity_eq_of_extension_mem hExt
        (UnnamedSchema.symOfExtension hExt X) X.2
    change Tuple.castArity hMem (Tuple.castArity hAr t) = t
    rw [Tuple.castArity_proof_irrel hMem hAr.symm]
    exact Tuple.castArity_symm hAr t
  have hXEq :
      (⟨(UnnamedSchema.symOfExtension hExt X).1, X.2⟩ :
        Γ.syms) = X := by
    exact Subtype.ext rfl
  rw [hCast]
  cases hXEq
  rfl

private theorem liftRA_eval_eq_relationOfExtension
    (hExt : Δ.extensionOf Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X))
    {I : Instance D Γ}
    {J : Instance D Δ}
    (hM : Instance.Extends hExt I J) :
    (liftRA hExt X eRep).eval J =
      Instance.relationOfExtension hExt
        (Instance.update I X (eRep.eval I))
        (UnnamedSchema.symOfExtension hExt X)
        X.2 := by
  apply Finset.ext
  intro t
  unfold liftRA
  rw [RAExpr.mem_eval_castArity]
  letI : Fact (Δ.extensionOf Γ) := ⟨hExt⟩
  have hReduct : Instance.reduct hExt J = I :=
    reduct_eq_of_extends hExt hM
  have hEval :
      (eRep.onExtension hExt).eval J = eRep.eval I := by
    simpa [hReduct] using
      (RAExpr.reduct_property (e := eRep) J)
  rw [hEval]
  have hCast :
      Tuple.castArity
          (UnnamedSchema.arity_eq_of_extension_mem hExt
            (UnnamedSchema.symOfExtension hExt X) X.2)
          t =
      Tuple.castArity
          (UnnamedSchema.arity_eq_of_extensionOf
            hExt X).symm
          t := by
    apply Tuple.castArity_proof_irrel
  have hXEq :
      (⟨(UnnamedSchema.symOfExtension hExt X).1, X.2⟩ :
        Γ.syms) = X := by
    exact Subtype.ext rfl
  have hMem :=
    Instance.relationOfExtension_mem_iff hExt
      (Instance.update I X (eRep.eval I))
      (UnnamedSchema.symOfExtension hExt X) X.2 t
  calc
    Tuple.castArity
        (UnnamedSchema.arity_eq_of_extensionOf hExt X).symm
        t ∈ eRep.eval I
        ↔ Tuple.castArity
            (UnnamedSchema.arity_eq_of_extension_mem hExt
              (UnnamedSchema.symOfExtension hExt X)
              X.2) t ∈
          (Instance.update I X (eRep.eval I))
              ⟨(UnnamedSchema.symOfExtension hExt X).1,
                X.2⟩ := by
          rw [hCast]
          constructor
          · intro ht
            simpa [UnnamedSchema.symOfExtension,
              Instance.update_lookup_eq] using ht
          · intro ht
            simpa [UnnamedSchema.symOfExtension,
              Instance.update_lookup_eq] using ht
    _ ↔ t ∈
          Instance.relationOfExtension hExt
            (Instance.update I X (eRep.eval I))
            (UnnamedSchema.symOfExtension hExt X) X.2 :=
        hMem.symm

private theorem update_extends_update
    (hExt : Δ.extensionOf Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X))
    {I : Instance D Γ}
    {J : Instance D Δ}
    (hM : Instance.Extends hExt I J) :
    Instance.Extends hExt
      (Instance.update I X (eRep.eval I))
      (Instance.update J
        (UnnamedSchema.symOfExtension hExt X)
        ((liftRA hExt X eRep).eval J)) := by
  intro Y hY
  by_cases hRaw : Y.1 = X.1
  · have hYEq :
        Y = UnnamedSchema.symOfExtension hExt X := by
      exact Subtype.ext hRaw
    subst Y
    rw [Instance.update_lookup_eq]
    exact liftRA_eval_eq_relationOfExtension
      hExt X eRep hM
  · have hYNe :
        Y ≠ UnnamedSchema.symOfExtension hExt X := by
      intro hEq
      exact hRaw (congrArg Subtype.val hEq)
    have hBaseNe :
        (⟨Y.1, hY⟩ : Γ.syms) ≠ X := by
      intro hEq
      exact hRaw (congrArg Subtype.val hEq)
    rw [Instance.update_lookup_ne _ _ _ hYNe]
    rw [hM Y hY]
    apply Finset.ext
    intro t
    rw [Instance.relationOfExtension_mem_iff]
    rw [Instance.relationOfExtension_mem_iff]
    rw [Instance.update_lookup_ne _ X ⟨Y.1, hY⟩ hBaseNe]

private def replaceFree
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Γ)
    (K : Instance D Δ) :
    Instance D Δ := by
  intro Y
  by_cases hY : Y.1 ∈ Γ.syms
  · exact Instance.relationOfExtension hExt I Y hY
  · exact K Y

private theorem replaceFree_extends
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Γ)
    (K : Instance D Δ) :
    Instance.Extends hExt I (replaceFree hExt I K) := by
  intro Y hY
  simp [replaceFree, hY]

private theorem update_replaceFree_eq
    (hExt : Δ.extensionOf Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X))
    {I : Instance D Γ}
    {K : Instance D Δ}
    (hN :
      Instance.Extends hExt
        (Instance.update I X (eRep.eval I)) K) :
    Instance.update (replaceFree hExt I K)
        (UnnamedSchema.symOfExtension hExt X)
        ((liftRA hExt X eRep).eval
          (replaceFree hExt I K)) =
      K := by
  apply Instance.ext
  intro Y
  by_cases hY : Y.1 ∈ Γ.syms
  · by_cases hRaw : Y.1 = X.1
    · have hYEq :
          Y = UnnamedSchema.symOfExtension hExt X := by
        exact Subtype.ext hRaw
      subst Y
      rw [Instance.update_lookup_eq]
      rw [liftRA_eval_eq_relationOfExtension
        hExt X eRep (replaceFree_extends hExt I K)]
      exact
        (hN (UnnamedSchema.symOfExtension hExt X) X.2).symm
    · have hYNe :
          Y ≠ UnnamedSchema.symOfExtension hExt X := by
        intro hEq
        exact hRaw (congrArg Subtype.val hEq)
      have hBaseNe :
          (⟨Y.1, hY⟩ : Γ.syms) ≠ X := by
        intro hEq
        exact hRaw (congrArg Subtype.val hEq)
      rw [Instance.update_lookup_ne _ _ _ hYNe]
      unfold replaceFree
      simp only [hY, ↓reduceDIte]
      rw [hN Y hY]
      apply Finset.ext
      intro t
      rw [Instance.relationOfExtension_mem_iff]
      rw [Instance.relationOfExtension_mem_iff]
      rw [Instance.update_lookup_ne _ X
        ⟨Y.1, hY⟩ hBaseNe]
  · have hYNe :
        Y ≠ UnnamedSchema.symOfExtension hExt X := by
      intro hEq
      apply hY
      rw [congrArg Subtype.val hEq]
      exact X.2
    rw [Instance.update_lookup_ne _ _ _ hYNe]
    simp [replaceFree, hY]

/-
  `substFree` satisfies its semantic substitution contract.
-/
theorem substFree_correct
    (φ : AssertExpr D Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    FreeSubstSpec (φ.substFree X eRep) φ X eRep := by
  intro I
  constructor
  · rintro ⟨J, hM, hFormula⟩
    let Xfull := UnnamedSchema.symOfExtension
      φ.extendsFree X
    let eFull := liftRA φ.extendsFree X eRep
    have hFormulaUpdated :
        φ.formula.eval
          (Instance.update J Xfull (eFull.eval J)) := by
      exact
        (QFAssertExpr.subst_eval J Xfull eFull
          φ.formula).mp hFormula
    exact
      ⟨Instance.update J Xfull (eFull.eval J),
        update_extends_update φ.extendsFree X eRep hM,
        hFormulaUpdated⟩
  · rintro ⟨K, hN, hFormula⟩
    let J := replaceFree φ.extendsFree I K
    let Xfull := UnnamedSchema.symOfExtension
      φ.extendsFree X
    let eFull := liftRA φ.extendsFree X eRep
    have hM : Instance.Extends φ.extendsFree I J := by
      simpa [J] using replaceFree_extends φ.extendsFree I K
    have hUpdated :
        Instance.update J Xfull (eFull.eval J) =
          K := by
      simpa [J, Xfull, eFull] using
        update_replaceFree_eq φ.extendsFree X eRep hN
    have hFormulaUpdated :
        φ.formula.eval
          (Instance.update J Xfull (eFull.eval J)) := by
      rw [hUpdated]
      exact hFormula
    have hSubFormula :
        (φ.formula.subst
          Xfull eFull).eval J := by
      exact
        (QFAssertExpr.subst_eval J Xfull eFull
          φ.formula).mpr hFormulaUpdated
    exact ⟨J, hM, by simpa [substFree, Xfull, eFull] using
      hSubFormula⟩

/-
  Evaluation of `substFree` is evaluation after one update.
-/
theorem substFree_eval_iff
    (φ : AssertExpr D Γ)
    (I : Instance D Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    (φ.substFree X eRep).eval I ↔
      φ.eval (Instance.update I X (eRep.eval I)) :=
  substFree_correct φ X eRep I

end AssertExpr

end Whiel
