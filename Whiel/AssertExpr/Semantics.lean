-- Author: Jesse Comer
import Whiel.AssertExpr.Syntax
import Whiel.Guard.Semantics

/-
  Prop-valued semantics for Whiel assertions.

  Key declarations:
    * `QFAssertExpr.andList_eval_iff`
    * `QFAssertExpr.orList_eval_iff`
    * `AssertExpr.eval`
    * `AssertExpr.ofQF_eval_iff`
    * `AssertExpr.liftFull`
    * `AssertExpr.liftFull_eval_iff`
    * `AssertExpr.expansion_invariance`
-/

------------------------------------------------------------
-- Finite Quantifier-Free Assertion Evaluation
------------------------------------------------------------

namespace Whiel

namespace QFAssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Finite conjunction has pointwise truth. -/
@[simp] theorem andList_eval_iff
    (φs : List (QFAssertExpr D Γ))
    (I : Instance D Γ) :
    (andList φs).eval I ↔
      ∀ φ ∈ φs, φ.eval I := by
  induction φs with
  | nil =>
      simp [andList]
  | cons φ φs ih =>
      cases φs with
      | nil =>
          simp [andList]
      | cons ψ ψs =>
          simp [andList, ih]

/- Finite disjunction has existential truth. -/
@[simp] theorem orList_eval_iff
    (φs : List (QFAssertExpr D Γ))
    (I : Instance D Γ) :
    (orList φs).eval I ↔
      ∃ φ ∈ φs, φ.eval I := by
  induction φs with
  | nil =>
      simp [orList]
  | cons φ φs ih =>
      cases φs with
      | nil =>
          simp [orList]
      | cons ψ ψs =>
          simp [orList, ih]

end QFAssertExpr

end Whiel

------------------------------------------------------------
-- Assertion Evaluation
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Same-free-schema semantics of assertions by existential
  second-order expansion to the full schema.
-/
def eval
    (φ : AssertExpr D Γ)
    (I : Instance D Γ) : Prop :=
  ∃ J : Instance D φ.fullSchema,
    Instance.Extends φ.extendsFree I J ∧
      φ.formula.eval J

@[simp] theorem eval_iff
    (φ : AssertExpr D Γ)
    (I : Instance D Γ) :
    eval φ I ↔
      ∃ J : Instance D φ.fullSchema,
        Instance.Extends φ.extendsFree I J ∧
          φ.formula.eval J :=
  Iff.rfl

@[simp] theorem eval_self_iff
    (φ : AssertExpr D Γ)
    (I : Instance D Γ) :
    φ.eval I ↔ φ.eval I := by
  rfl

/- Reinterpret an assertion over a larger full schema. -/
def liftFull
    (φ : AssertExpr D Γ)
    {Θ : UnnamedSchema A}
    (hFull : Θ.extensionOf φ.fullSchema) :
    AssertExpr D Γ where
  fullSchema := Θ
  extendsFree :=
    UnnamedSchema.extensionOf_trans hFull φ.extendsFree
  formula := φ.formula.onExtension hFull

/-
  Changing only the proof of free-schema extension does
  not change truth.
-/
theorem eval_extendsFree_irrel
    {Δ : UnnamedSchema A}
    (h₁ h₂ : Δ.extensionOf Γ)
    (φ : QFAssertExpr D Δ)
    (I : Instance D Γ) :
    (AssertExpr.eval
      ({ fullSchema := Δ,
         extendsFree := h₁,
         formula := φ } : AssertExpr D Γ) I) ↔
    (AssertExpr.eval
      ({ fullSchema := Δ,
         extendsFree := h₂,
         formula := φ } : AssertExpr D Γ) I) := by
  have hEq : h₁ = h₂ := Subsingleton.elim h₁ h₂
  cases hEq
  rfl

/-
  Lifting an assertion to a larger full schema preserves
  truth.
-/
theorem liftFull_eval_iff
    (φ : AssertExpr D Γ)
    {Θ : UnnamedSchema A}
    (hFull : Θ.extensionOf φ.fullSchema)
    (I : Instance D Γ) :
    (φ.liftFull hFull).eval I ↔ φ.eval I := by
  let hComp :=
    UnnamedSchema.extensionOf_trans hFull φ.extendsFree
  constructor
  · rintro ⟨K, hN, hFormula⟩
    let J := Instance.reduct hFull K
    have hMExt : Instance.Extends φ.extendsFree I J := by
      apply Instance.extends_of_reduct_eq φ.extendsFree
      calc
        Instance.reduct φ.extendsFree J =
            Instance.reduct hComp K := by
              simpa [J, hComp] using
                Instance.reduct_trans hFull φ.extendsFree K
        _ = I :=
            Instance.reduct_eq_of_extends hComp hN
    have hFormulaM : φ.formula.eval J := by
      letI : Fact
          (Θ.extensionOf φ.fullSchema) := ⟨hFull⟩
      exact
        (Guard.onExtension_eval_reduct
          (Γ := Θ) (Δ := φ.fullSchema)
          φ.formula K J rfl).mp hFormula
    exact ⟨J, hMExt, hFormulaM⟩
  · rintro ⟨J, hM, hFormula⟩
    let K := Instance.expandEmpty hFull J
    have hNExt : Instance.Extends hComp I K := by
      apply Instance.extends_of_reduct_eq hComp
      calc
        Instance.reduct hComp K =
            Instance.reduct φ.extendsFree
              (Instance.reduct hFull K) := by
                simpa [hComp] using
                  (Instance.reduct_trans
                    hFull φ.extendsFree K).symm
        _ = Instance.reduct φ.extendsFree J := by
              simp [K, Instance.reduct_expandEmpty]
        _ = I :=
            Instance.reduct_eq_of_extends φ.extendsFree hM
    have hFormulaN :
        (φ.formula.onExtension hFull).eval K := by
      letI : Fact
          (Θ.extensionOf φ.fullSchema) := ⟨hFull⟩
      exact
        (Guard.onExtension_eval_reduct
          (Γ := Θ) (Δ := φ.fullSchema)
          φ.formula K J
          (by simp [K, Instance.reduct_expandEmpty])).mpr
          hFormula
    exact ⟨K, hNExt, hFormulaN⟩

end AssertExpr

end Whiel

------------------------------------------------------------
-- No-Bound Assertion Evaluation
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Reducing from the free schema to the full schema gives an
  extension witness for no-bound assertions.
-/
private theorem reduct_free_extends
    (φ : AssertExpr D Γ)
    (hNo : φ.NoBoundSymbols)
    (I : Instance D Γ) :
    Instance.Extends φ.extendsFree I
      (Instance.reduct (φ.free_extension_full hNo) I) := by
  apply Instance.extends_of_reduct_eq φ.extendsFree
  calc
    Instance.reduct φ.extendsFree
        (Instance.reduct (φ.free_extension_full hNo) I) =
      Instance.reduct
        (UnnamedSchema.extensionOf_trans
          (φ.free_extension_full hNo) φ.extendsFree)
        I := by
          simpa using
            Instance.reduct_trans
              (φ.free_extension_full hNo) φ.extendsFree I
    _ = Instance.reduct
        (UnnamedSchema.extensionOf_refl Γ) I := by
          have hEq :
              UnnamedSchema.extensionOf_trans
                  (φ.free_extension_full hNo)
                  φ.extendsFree =
                UnnamedSchema.extensionOf_refl Γ :=
            Subsingleton.elim _ _
          rw [hEq]
    _ = I := by
          exact Instance.reduct_refl I

/-
  Evaluation of a no-bound assertion is exactly evaluation
  of the retagged QF body.
-/
theorem toQF_eval_iff
    (φ : AssertExpr D Γ)
    (hNo : φ.NoBoundSymbols)
    (I : Instance D Γ) :
    (φ.toQF hNo).eval I ↔ φ.eval I := by
  let hBack := φ.free_extension_full hNo
  have hReduct :
      Instance.Extends φ.extendsFree I
        (Instance.reduct hBack I) :=
    reduct_free_extends φ hNo I
  have hRetag :
      (φ.formula.onExtension hBack).eval I ↔
        φ.formula.eval (Instance.reduct hBack I) := by
    letI :
        Fact (Γ.extensionOf φ.fullSchema) :=
      ⟨hBack⟩
    exact
      Guard.onExtension_eval_reduct
        (Γ := Γ) (Δ := φ.fullSchema)
        φ.formula I (Instance.reduct hBack I) rfl
  constructor
  · intro hQF
    exact
      ⟨Instance.reduct hBack I,
        hReduct, hRetag.mp hQF⟩
  · rintro ⟨J, hM, hFormula⟩
    have hMReduct :
        Instance.reduct hBack I = J := by
      have hI :
          I = Instance.reduct φ.extendsFree J :=
        (Instance.reduct_eq_of_extends
          φ.extendsFree hM).symm
      calc
        Instance.reduct hBack I =
            Instance.reduct hBack
              (Instance.reduct φ.extendsFree J) := by
              rw [hI]
        _ = Instance.reduct
              (UnnamedSchema.extensionOf_trans
                φ.extendsFree hBack)
              J := by
              simpa using
                Instance.reduct_trans
                  φ.extendsFree hBack J
        _ = Instance.reduct
              (UnnamedSchema.extensionOf_refl φ.fullSchema)
              J := by
              have hEq :
                  UnnamedSchema.extensionOf_trans
                      φ.extendsFree hBack =
                    UnnamedSchema.extensionOf_refl
                      φ.fullSchema :=
                Subsingleton.elim _ _
              rw [hEq]
        _ = J := by
              exact Instance.reduct_refl J
    exact hRetag.mpr (by simpa [hMReduct] using hFormula)

/-
  Evaluation of the proof-indexed QF conversion agrees
  with assertion evaluation.
-/
theorem toQFOfNoBound_eval_iff
    (φ : AssertExpr D Γ)
    (hNo : φ.NoBoundSymbols)
    (I : Instance D Γ) :
    (φ.toQFOfNoBound hNo).eval I ↔ φ.eval I := by
  exact φ.toQF_eval_iff hNo I

/- Viewing a QF assertion as full preserves evaluation. -/
theorem ofQF_eval_iff
    (φ : QFAssertExpr D Γ)
    (I : Instance D Γ) :
    (ofQF φ).eval I ↔ φ.eval I := by
  let hNo := ofQF_noBound φ
  have hOuter := toQF_eval_iff (ofQF φ) hNo I
  have hBody :
      ((ofQF φ).toQF hNo).eval I ↔ φ.eval I := by
    change (φ.onExtension _).eval I ↔ φ.eval I
    letI : Fact (Γ.extensionOf Γ) :=
      ⟨(ofQF φ).free_extension_full hNo⟩
    exact Guard.onExtension_eval_reduct
      φ I I (Instance.reduct_refl I)
  exact hOuter.symm.trans hBody

end AssertExpr

end Whiel

------------------------------------------------------------
-- Expansion Invariance and the Reduct Property
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private theorem relation?_reduct_eq
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Δ)
    (X : Γ.syms) :
    (Instance.reduct hExt I).relation? X.1 =
      I.relation? X.1 := by
  unfold Instance.relation? Instance.reduct
  simp [X.2, hExt.1 X.2,
    UnnamedSchema.arity_eq_of_extensionOf hExt X]

private theorem reducts_agreeOn_of_agreeOnRelations
    {Δ₁ Δ₂ : UnnamedSchema A}
    [hExt₁ : Fact (Δ₁.extensionOf Γ)]
    [hExt₂ : Fact (Δ₂.extensionOf Γ)]
    {I₁ : Instance D Δ₁}
    {I₂ : Instance D Δ₂}
    {S : Finset A}
    (hAgree : I₁.agreeOnRelations S I₂) :
    Instance.agreeOn S
      (Instance.reduct hExt₁.out I₁)
      (Instance.reduct hExt₂.out I₂) := by
  intro X hXS
  have hRel :
      (Instance.reduct hExt₁.out I₁).relation? X.1 =
        (Instance.reduct hExt₂.out I₂).relation?
          X.1 := by
    calc
      (Instance.reduct hExt₁.out I₁).relation? X.1
          = I₁.relation? X.1 :=
            relation?_reduct_eq hExt₁.out I₁ X
      _ = I₂.relation? X.1 := hAgree X.1 hXS
      _ =
          (Instance.reduct hExt₂.out I₂).relation?
            X.1 :=
            (relation?_reduct_eq hExt₂.out I₂ X).symm
  have hSome :
      some
          (⟨Γ.arity X,
            Instance.reduct hExt₁.out I₁ X⟩ :
            Sigma (FinRelation D)) =
        some
          ⟨Γ.arity X,
            Instance.reduct hExt₂.out I₂ X⟩ := by
    simpa [Instance.relation?, X.2] using hRel
  injection hSome with hSigma
  injection hSigma

/- Replace the free part of a full-schema witness by `I`. -/
private def witnessWithFreeInstance
    (φ : AssertExpr D Γ)
    (I : Instance D Γ)
    (K : Instance D φ.fullSchema) :
    Instance D φ.fullSchema := by
  intro X
  by_cases hX : X.1 ∈ Γ.syms
  · exact
      Instance.relationOfExtension φ.extendsFree I X hX
  · exact K X

/- The rebuilt witness extends the new free instance. -/
private lemma witnessWithFreeInstance_extends
    (φ : AssertExpr D Γ)
    (I : Instance D Γ)
    (K : Instance D φ.fullSchema) :
    Instance.Extends φ.extendsFree I
      (φ.witnessWithFreeInstance I K) := by
  intro X hX
  unfold witnessWithFreeInstance
  simp [hX]

/-
  Rebuilt witnesses preserve formula symbols under
  free-symbol agreement.
-/
private lemma witnessWithFreeInstance_agreeOn_formula
    (φ : AssertExpr D Γ)
    {S : Finset A}
    (hFree : φ.freeSymbols ⊆ S)
    {I J : Instance D Γ}
    (hAgree : Instance.agreeOn S I J)
    {K : Instance D φ.fullSchema}
    (hM : Instance.Extends φ.extendsFree I K) :
    Instance.agreeOn φ.formula.symbols K
      (φ.witnessWithFreeInstance J K) := by
  intro X hXFormula
  by_cases hXFree : X.1 ∈ Γ.syms
  · have hXS : X.1 ∈ S := by
      apply hFree
      simp [freeSymbols, formulaSymbols, hXFormula, hXFree]
    have hIJ :
        I ⟨X.1, hXFree⟩ =
          J ⟨X.1, hXFree⟩ :=
      hAgree ⟨X.1, hXFree⟩ hXS
    calc
      K X
          =
            Instance.relationOfExtension
              φ.extendsFree I X hXFree :=
            hM X hXFree
      _ =
          Instance.relationOfExtension
            φ.extendsFree J X hXFree := by
            simp [Instance.relationOfExtension, hIJ]
      _ = φ.witnessWithFreeInstance J K X := by
            unfold witnessWithFreeInstance
            simp [hXFree]
  · unfold witnessWithFreeInstance
    simp [hXFree]

private lemma eval_imp_of_agreeOn_freeSymbols
    (φ : AssertExpr D Γ)
    {S : Finset A}
    (hFree : φ.freeSymbols ⊆ S)
    {I J : Instance D Γ}
    (hAgree : Instance.agreeOn S I J) :
    φ.eval I → φ.eval J := by
  intro hEval
  rcases hEval with ⟨K, hMExt, hFormula⟩
  let K' := φ.witnessWithFreeInstance J K
  have hNExt : Instance.Extends φ.extendsFree J K' := by
    simpa [K'] using
      φ.witnessWithFreeInstance_extends J K
  have hAgreeFormula :
      Instance.agreeOn φ.formula.symbols K K' := by
    simpa [K'] using
      φ.witnessWithFreeInstance_agreeOn_formula
        hFree hAgree hMExt
  have hFormulaN : φ.formula.eval K' :=
    (Guard.eval_reduct_property
      φ.formula hAgreeFormula).mp hFormula
  exact ⟨K', hNExt, hFormulaN⟩

private theorem eval_expansion_invariance
    (φ : AssertExpr D Γ)
    {I J : Instance D Γ}
    (hAgree : Instance.agreeOn φ.freeSymbols I J) :
    φ.eval I ↔ φ.eval J := by
  constructor
  · exact φ.eval_imp_of_agreeOn_freeSymbols
      (by intro X hX; exact hX) hAgree
  · exact φ.eval_imp_of_agreeOn_freeSymbols
      (by intro X hX; exact hX)
      (Instance.agreeOn_symm hAgree)

/-
  Assertion truth is invariant across expansions that agree
  on the free relation symbols of the assertion.
-/
theorem expansion_invariance
    {Δ₁ Δ₂ : UnnamedSchema A}
    [hExt₁ : Fact (Δ₁.extensionOf Γ)]
    [hExt₂ : Fact (Δ₂.extensionOf Γ)]
    (φ : AssertExpr D Γ)
    {I₁ : Instance D Δ₁}
    {I₂ : Instance D Δ₂}
    (hAgree :
      I₁.agreeOnRelations φ.freeSymbols I₂) :
    φ.eval (Instance.reduct hExt₁.out I₁) ↔
      φ.eval (Instance.reduct hExt₂.out I₂) := by
  have hBaseAgree :
      Instance.agreeOn φ.freeSymbols
        (Instance.reduct hExt₁.out I₁)
        (Instance.reduct hExt₂.out I₂) :=
    reducts_agreeOn_of_agreeOnRelations hAgree
  exact φ.eval_expansion_invariance hBaseAgree

end AssertExpr

end Whiel
