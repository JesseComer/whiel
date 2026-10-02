-- Author: Jesse Comer
import Databases.RelCalc.AdomSemantics
import Mathlib.Data.Set.Finite.Basic

/-
  This file defines the semantic notions used to state
  domain-independent active-domain validity for RelCalc
  sentences.

  Key declarations include:
    * `RelCalc.Sentence.LocalAdomValid`
    * `RelCalc.Sentence.DomainIndependent`
    * `RelCalc.Sentence.AdomValid`
-/

------------------------------------------------------------
-- Fresh-Symbol Finite-Domain Padding
------------------------------------------------------------

namespace Instance

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Add a fresh unary relation interpreted as exactly `Q`. -/
private def addFreshUnary
    (I : Instance D Γ)
    (X : A)
    (hFresh : X ∉ Γ.syms)
    (Q : Finset D) :
    Instance D (Γ.insertFresh X 1 hFresh) :=
  let hExt :=
    UnnamedSchema.insertFresh_extensionOf
      Γ X 1 hFresh
  let Y := Γ.insertedSym X 1 hFresh
  let hArity :=
    UnnamedSchema.arity_insertedSym
      Γ X 1 hFresh
  Instance.update
    (Instance.expandEmpty hExt I)
    Y
    (cast
      (congrArg (FinRelation D) hArity.symm)
      (Tuple.allOver Q 1))

/- Reducing the fresh unary expansion recovers `I`. -/
private theorem reduct_addFreshUnary
    (I : Instance D Γ)
    (X : A)
    (hFresh : X ∉ Γ.syms)
    (Q : Finset D) :
    Instance.reduct
        (UnnamedSchema.insertFresh_extensionOf
          Γ X 1 hFresh)
        (I.addFreshUnary X hFresh Q) =
      I := by
  unfold addFreshUnary
  rw [Instance.reduct_update_of_not_mem]
  · exact Instance.reduct_expandEmpty
      (UnnamedSchema.insertFresh_extensionOf
        Γ X 1 hFresh) I
  · exact hFresh

/-
  The unary expansion adds exactly `Q` to the active
  domain.
-/
private theorem Adom_addFreshUnary
    (I : Instance D Γ)
    (X : A)
    (hFresh : X ∉ Γ.syms)
    (Q : Finset D) :
    (I.addFreshUnary X hFresh Q).Adom =
      I.Adom ∪ Q := by
  let Δ := Γ.insertFresh X 1 hFresh
  let hExt : Δ.extensionOf Γ :=
    UnnamedSchema.insertFresh_extensionOf
      Γ X 1 hFresh
  let Y : Δ.syms :=
    Γ.insertedSym X 1 hFresh
  let hArity : Δ.arity Y = 1 :=
    UnnamedSchema.arity_insertedSym
      Γ X 1 hFresh
  let J : Instance D Δ :=
    I.addFreshUnary X hFresh Q
  have hReduct : Instance.reduct hExt J = I := by
    exact reduct_addFreshUnary I X hFresh Q
  ext d
  constructor
  · intro hd
    rw [Instance.in_Adom_iff_in_Relation] at hd
    rcases hd with ⟨Z, t, ht, hdt⟩
    by_cases hZX : Z.1 = X
    · apply Finset.mem_union_right
      have hZY : Z = Y := by
        apply Subtype.ext
        exact hZX
      subst Z
      let u : Tuple D 1 :=
        Tuple.castArity hArity.symm t
      have htFresh :
          t ∈
            cast
              (congrArg (FinRelation D)
                hArity.symm)
              (Tuple.allOver Q 1) := by
        simpa [J, addFreshUnary, Y, hArity]
          using ht
      have hu : u ∈ Tuple.allOver Q 1 := by
        exact
          (FinRelation.mem_cast_iff
            hArity.symm (Tuple.allOver Q 1) t).mp
            htFresh
      have huOver : u.isTupleOver Q :=
        Tuple.isTupleOver_of_mem_allOver Q hu
      have huSingleton :
          u = Vector.singleton u[0] := by
        apply Vector.ext
        intro i hi
        have hiZero : i = 0 :=
          Nat.eq_zero_of_le_zero
            (Nat.le_of_lt_succ hi)
        subst i
        simp
      have hdu : d ∈ u.toList := by
        rw [show u.toList = t.toList by
          exact Tuple.castArity_toList
            hArity.symm t]
        exact List.mem_toFinset.mp hdt
      have hList : u.toList = [u[0]] := by
        rw [huSingleton]
        exact Vector.toList_singleton
      rw [hList] at hdu
      have hdEq : d = u[0] :=
        List.mem_singleton.mp hdu
      rw [hdEq]
      exact huOver (0 : Fin 1)
    · apply Finset.mem_union_left
      have hZOld : Z.1 ∈ Γ.syms := by
        have hZ := Z.2
        change Z.1 ∈ insert X Γ.syms at hZ
        exact (Finset.mem_insert.mp hZ).resolve_left hZX
      let Z₀ : Γ.syms := ⟨Z.1, hZOld⟩
      have hZY : Z ≠ Y := by
        intro hEq
        apply hZX
        exact congrArg Subtype.val hEq
      have htExpanded :
          t ∈ Instance.expandEmpty hExt I Z := by
        simpa [J, addFreshUnary, Y, hArity, hZY]
          using ht
      let t₀ : Tuple D (Γ.arity Z₀) :=
        Tuple.castArity
          (UnnamedSchema.arity_eq_of_extension_mem
            hExt Z hZOld)
          t
      have htI : t₀ ∈ I Z₀ := by
        exact
          (Instance.expandEmpty_mem_iff_of_mem
            hExt I Z hZOld t).mp htExpanded
      rw [Instance.in_Adom_iff_in_Relation]
      refine ⟨Z₀, t₀, htI, ?_⟩
      rw [show t₀.toList = t.toList by
        exact Tuple.castArity_toList
          (UnnamedSchema.arity_eq_of_extension_mem
            hExt Z hZOld) t]
      exact hdt
  · intro hd
    rw [Finset.mem_union] at hd
    rcases hd with hd | hd
    · have hInReduct :
          d ∈ (Instance.reduct hExt J).Adom := by
        simpa [hReduct] using hd
      exact Instance.Adom_reduct_subset
        hExt J hInReduct
    · rw [Instance.in_Adom_iff_in_Relation]
      let u : Tuple D 1 := Vector.singleton d
      let t : Tuple D (Δ.arity Y) :=
        Tuple.castArity hArity u
      have hu : u ∈ Tuple.allOver Q 1 := by
        apply Tuple.mem_allOver_of_isTupleOver
        intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simpa [u] using hd
      have htFresh :
          t ∈
            cast
              (congrArg (FinRelation D)
                hArity.symm)
              (Tuple.allOver Q 1) := by
        apply
          (FinRelation.mem_cast_iff
            hArity.symm (Tuple.allOver Q 1) t).mpr
        rw [show Tuple.castArity hArity.symm t = u by
          exact Tuple.castArity_symm hArity u]
        exact hu
      refine ⟨Y, t, ?_, ?_⟩
      · simpa [J, addFreshUnary, Y, hArity]
          using htFresh
      · change d ∈ t.toList.toFinset
        rw [show t.toList = u.toList by
          exact Tuple.castArity_toList hArity u]
        simp [u]

end Instance

------------------------------------------------------------
-- Finite Support For Arbitrary Quantifier Domains
------------------------------------------------------------

namespace Assign

variable {D : Type} [Domain D]

/-
  Two assignments have the same equality type over `V`,
  while agreeing pointwise whenever either value lies in
  the fixed support `S`.
-/
private def SameSupportType
    (S : Finset D)
    (V : Finset Var)
    (σ τ : Assign D) : Prop :=
  (∀ x ∈ V,
      (σ x ∈ S ∨ τ x ∈ S) → σ x = τ x) ∧
    ∀ x ∈ V, ∀ y ∈ V,
      (σ x = σ y ↔ τ x = τ y)

omit [Domain D] in
private theorem sameSupportType_symm
    {S : Finset D}
    {V : Finset Var}
    {σ τ : Assign D}
    (h : SameSupportType S V σ τ) :
    SameSupportType S V τ σ := by
  constructor
  · intro x hx hS
    exact (h.1 x hx hS.symm).symm
  · intro x hx y hy
    exact (h.2 x hx y hy).symm

omit [Domain D] in
private theorem sameSupportType_mono
    {S : Finset D}
    {V W : Finset Var}
    {σ τ : Assign D}
    (h : SameSupportType S W σ τ)
    (hVW : V ⊆ W) :
    SameSupportType S V σ τ := by
  constructor
  · intro x hx
    exact h.1 x (hVW hx)
  · intro x hx y hy
    exact h.2 x (hVW hx) y (hVW hy)

omit [Domain D] in
private theorem mapsInto_update
    {Q : Set D}
    {V : Finset Var}
    {σ : Assign D}
    {x : Var}
    {d : D}
    (hσ : MapsInto σ (V.erase x) Q)
    (hd : d ∈ Q) :
    MapsInto (update σ x d) V Q := by
  intro y hy
  by_cases hyx : y = x
  · subst y
    simpa [update] using hd
  · have hyErase : y ∈ V.erase x :=
      Finset.mem_erase.mpr ⟨hyx, hy⟩
    simpa [update, hyx] using hσ y hyErase

private theorem sameSupportType_update
    {S R : Finset D}
    {V : Finset Var}
    {σ τ : Assign D}
    {P : Set D}
    {x : Var}
    (hType : SameSupportType S V σ τ)
    (hτ : MapsInto τ V P)
    (hS : (↑S : Set D) ⊆ P)
    (hR : (↑R : Set D) ⊆ P)
    (hDisj : Disjoint R S)
    (hCard : V.card < R.card)
    (d : D) :
    ∃ e ∈ P,
      SameSupportType S (insert x V)
        (update σ x d) (update τ x e) := by
  by_cases hdS : d ∈ S
  · refine ⟨d, hS hdS, ?_⟩
    constructor
    · intro z hz hMem
      by_cases hzx : z = x
      · subst z
        simp [update]
      · have hzV :=
          (Finset.mem_insert.mp hz).resolve_left hzx
        have hMem' : σ z ∈ S ∨ τ z ∈ S := by
          simpa [update, hzx] using hMem
        simpa [update, hzx] using
          hType.1 z hzV hMem'
    · intro z hz w hw
      by_cases hzx : z = x
      · subst z
        by_cases hwx : w = x
        · subst w
          simp
        · have hwV :=
            (Finset.mem_insert.mp hw).resolve_left hwx
          simp only [update, if_pos, if_neg hwx]
          change d = σ w ↔ d = τ w
          constructor
          · intro hEq
            have hσS : σ w ∈ S := by
              rw [← hEq]
              exact hdS
            exact hEq.trans
              (hType.1 w hwV (Or.inl hσS))
          · intro hEq
            have hτS : τ w ∈ S := by
              rw [← hEq]
              exact hdS
            exact hEq.trans
              (hType.1 w hwV (Or.inr hτS)).symm
      · have hzV :=
          (Finset.mem_insert.mp hz).resolve_left hzx
        by_cases hwx : w = x
        · subst w
          simp only [update, if_pos, if_neg hzx]
          change σ z = d ↔ τ z = d
          constructor
          · intro hEq
            have hσS : σ z ∈ S := by
              rw [hEq]
              exact hdS
            exact (hType.1 z hzV
              (Or.inl hσS)).symm.trans hEq
          · intro hEq
            have hτS : τ z ∈ S := by
              rw [hEq]
              exact hdS
            exact (hType.1 z hzV
              (Or.inr hτS)).trans hEq
        · have hwV :=
            (Finset.mem_insert.mp hw).resolve_left hwx
          simpa [update, hzx, hwx] using
            hType.2 z hzV w hwV
  · by_cases hOld : ∃ y ∈ V, σ y = d
    · rcases hOld with ⟨y, hyV, hy⟩
      refine ⟨τ y, hτ y hyV, ?_⟩
      have hyNotS : τ y ∉ S := by
        intro hyS
        have hFix : σ y = τ y :=
          hType.1 y hyV (Or.inr hyS)
        have : d = τ y := hy.symm.trans hFix
        exact hdS (this ▸ hyS)
      constructor
      · intro z hz hMem
        by_cases hzx : z = x
        · subst z
          simp [update, hdS, hyNotS] at hMem
        · have hzV :=
            (Finset.mem_insert.mp hz).resolve_left hzx
          have hMem' : σ z ∈ S ∨ τ z ∈ S := by
            simpa [update, hzx] using hMem
          simpa [update, hzx] using
            hType.1 z hzV hMem'
      · intro z hz w hw
        by_cases hzx : z = x
        · subst z
          by_cases hwx : w = x
          · subst w
            simp
          · have hwV :=
              (Finset.mem_insert.mp hw).resolve_left hwx
            simp only [update, if_pos, if_neg hwx]
            change d = σ w ↔ τ y = τ w
            simpa [hy] using hType.2 y hyV w hwV
        · have hzV :=
            (Finset.mem_insert.mp hz).resolve_left hzx
          by_cases hwx : w = x
          · subst w
            simp only [update, if_pos, if_neg hzx]
            change σ z = d ↔ τ z = τ y
            simpa [hy] using hType.2 z hzV y hyV
          · have hwV :=
              (Finset.mem_insert.mp hw).resolve_left hwx
            simpa [update, hzx, hwx] using
              hType.2 z hzV w hwV
    · have hImageCard : (V.image τ).card < R.card :=
        lt_of_le_of_lt Finset.card_image_le hCard
      rcases Finset.exists_mem_notMem_of_card_lt_card
          hImageCard with ⟨e, heR, heFresh⟩
      refine ⟨e, hR heR, ?_⟩
      have heNotS : e ∉ S :=
        Finset.disjoint_left.mp hDisj heR
      constructor
      · intro z hz hMem
        by_cases hzx : z = x
        · subst z
          simp [update, hdS, heNotS] at hMem
        · have hzV :=
            (Finset.mem_insert.mp hz).resolve_left hzx
          have hMem' : σ z ∈ S ∨ τ z ∈ S := by
            simpa [update, hzx] using hMem
          simpa [update, hzx] using
            hType.1 z hzV hMem'
      · intro z hz w hw
        by_cases hzx : z = x
        · subst z
          by_cases hwx : w = x
          · subst w
            simp
          · have hwV :=
              (Finset.mem_insert.mp hw).resolve_left hwx
            have hσNe : d ≠ σ w := by
              intro hEq
              exact hOld ⟨w, hwV, hEq.symm⟩
            have hτNe : e ≠ τ w := by
              intro hEq
              exact heFresh
                (Finset.mem_image.mpr
                  ⟨w, hwV, hEq.symm⟩)
            simp only [update, if_pos, if_neg hwx]
            change d = σ w ↔ e = τ w
            exact iff_of_false hσNe hτNe
        · have hzV :=
            (Finset.mem_insert.mp hz).resolve_left hzx
          by_cases hwx : w = x
          · subst w
            have hσNe : σ z ≠ d := by
              intro hEq
              exact hOld ⟨z, hzV, hEq⟩
            have hτNe : τ z ≠ e := by
              intro hEq
              exact heFresh
                (Finset.mem_image.mpr
                  ⟨z, hzV, hEq⟩)
            simp only [update, if_pos, if_neg hzx]
            change σ z = d ↔ τ z = e
            exact iff_of_false hσNe hτNe
          · have hwV :=
              (Finset.mem_insert.mp hw).resolve_left hwx
            simpa [update, hzx, hwx] using
              hType.2 z hzV w hwV

end Assign

namespace RelTerm

variable {D : Type} [Domain D]

private theorem eval_eq_iff_of_sameSupportType
    {S : Finset D}
    {V : Finset Var}
    {σ τ : Assign D}
    (hType : Assign.SameSupportType S V σ τ)
    (t u : RelTerm D)
    (htV : t.vars ⊆ V)
    (huV : u.vars ⊆ V)
    (htS : t.constants ⊆ S)
    (huS : u.constants ⊆ S) :
    (t.eval σ = u.eval σ ↔
      t.eval τ = u.eval τ) := by
  cases t with
  | var x =>
      have hxV : x ∈ V :=
        htV (by simp [RelTerm.vars])
      cases u with
      | var y =>
          have hyV : y ∈ V :=
            huV (by simp [RelTerm.vars])
          exact hType.2 x hxV y hyV
      | const d =>
          have hdS : d ∈ S :=
            huS (by simp [RelTerm.constants])
          change (σ x = d ↔ τ x = d)
          constructor
          · intro hEq
            have hσS : σ x ∈ S := by
              rw [hEq]
              exact hdS
            exact (hType.1 x hxV
              (Or.inl hσS)).symm.trans hEq
          · intro hEq
            have hτS : τ x ∈ S := by
              rw [hEq]
              exact hdS
            exact (hType.1 x hxV
              (Or.inr hτS)).trans hEq
  | const d =>
      have hdS : d ∈ S :=
        htS (by simp [RelTerm.constants])
      cases u with
      | var y =>
          have hyV : y ∈ V :=
            huV (by simp [RelTerm.vars])
          change (d = σ y ↔ d = τ y)
          constructor
          · intro hEq
            have hσS : σ y ∈ S := by
              rw [← hEq]
              exact hdS
            exact hEq.trans
              (hType.1 y hyV (Or.inl hσS))
          · intro hEq
            have hτS : τ y ∈ S := by
              rw [← hEq]
              exact hdS
            exact hEq.trans
              (hType.1 y hyV (Or.inr hτS)).symm
      | const e =>
          rfl

end RelTerm

namespace RelAtom

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private theorem evalTuple_eq_of_sat_sameSupportType
    {S : Finset D}
    {σ τ : Assign D}
    (a : RelAtom D Γ)
    (I : Instance D Γ)
    (hType : Assign.SameSupportType S a.vars σ τ)
    (hAdom : I.Adom ⊆ S)
    (hSat : a.Sat I σ) :
    a.evalTuple σ = a.evalTuple τ := by
  have hOver :
      (a.evalTuple σ).isTupleOver I.Adom := by
    apply I.isTupleOver_Adom_of_mem
    exact hSat
  apply Vector.ext
  intro i hi
  let j : Fin (Γ.arity a.rel) := ⟨i, hi⟩
  have hEval (ρ : Assign D) :
      (a.evalTuple ρ)[i] =
        (a.args.get j).eval ρ := by
    simp [RelAtom.evalTuple,
      RelTerm.evalVector, Vector.getElem_ofFn, j]
  change
    (a.evalTuple σ)[i] =
      (a.evalTuple τ)[i]
  cases hTerm : a.args[i] with
  | var x =>
      have hGet :
          a.args.get j = RelTerm.var x := by
        change a.args[i] = RelTerm.var x
        exact hTerm
      have hx : x ∈ a.vars := by
        apply RelTerm.mem_tupleVars_of_mem_get_vars
          (i := j)
        simp [hGet, RelTerm.vars]
      have hxS : σ x ∈ S := by
        apply hAdom
        have hCoord := hOver j
        change (a.evalTuple σ)[i] ∈ I.Adom at hCoord
        rw [hEval σ, hGet] at hCoord
        exact hCoord
      have hEq := hType.1 x hx (Or.inl hxS)
      rw [hEval σ, hEval τ, hGet]
      exact hEq
  | const d =>
      have hGet :
          a.args.get j = RelTerm.const d := by
        change a.args[i] = RelTerm.const d
        exact hTerm
      rw [hEval σ, hEval τ, hGet]
      rfl

private theorem sat_iff_of_sameSupportType
    {S : Finset D}
    {σ τ : Assign D}
    (a : RelAtom D Γ)
    (I : Instance D Γ)
    (hType : Assign.SameSupportType S a.vars σ τ)
    (hAdom : I.Adom ⊆ S) :
    (a.Sat I σ ↔ a.Sat I τ) := by
  constructor
  · intro hSat
    have hEval := evalTuple_eq_of_sat_sameSupportType
      a I hType hAdom hSat
    change a.evalTuple τ ∈ I a.rel
    rw [← hEval]
    exact hSat
  · intro hSat
    have hEval := evalTuple_eq_of_sat_sameSupportType
      a I (Assign.sameSupportType_symm hType)
      hAdom hSat
    change a.evalTuple σ ∈ I a.rel
    rw [← hEval]
    exact hSat

end RelAtom

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private theorem arbitraryAssignSatIn_iff_of_sameSupportType
    {S R : Finset D}
    {W : Finset Var}
    {Q P : Set D}
    (hS_Q : (↑S : Set D) ⊆ Q)
    (hS_P : (↑S : Set D) ⊆ P)
    (hR_Q : (↑R : Set D) ⊆ Q)
    (hR_P : (↑R : Set D) ⊆ P)
    (hDisj : Disjoint R S)
    (hCard : R.card = W.card)
    (φ : Formula D Γ)
    (I : Instance D Γ)
    {σ τ : Assign D}
    (hVars : φ.allVars ⊆ W)
    (hConsts : φ.constants ⊆ S)
    (hAdom : I.Adom ⊆ S)
    (hσ : Assign.MapsInto σ φ.freeVars Q)
    (hτ : Assign.MapsInto τ φ.freeVars P)
    (hType : Assign.SameSupportType S φ.freeVars σ τ) :
    (φ.ArbitraryAssignSatIn Q I σ ↔
      φ.ArbitraryAssignSatIn P I τ) := by
  induction φ generalizing σ τ with
  | top =>
      simp [ArbitraryAssignSatIn]
  | bot =>
      simp [ArbitraryAssignSatIn]
  | eq t u =>
      apply RelTerm.eval_eq_iff_of_sameSupportType hType
      · intro x hx
        exact Finset.mem_union.mpr (Or.inl hx)
      · intro x hx
        exact Finset.mem_union.mpr (Or.inr hx)
      · intro d hd
        exact hConsts (Finset.mem_union.mpr (Or.inl hd))
      · intro d hd
        exact hConsts (Finset.mem_union.mpr (Or.inr hd))
  | rel a =>
      exact RelAtom.sat_iff_of_sameSupportType
        a I hType hAdom
  | and φ ψ ihφ ihψ =>
      have hφ := ihφ
        (fun x hx => hVars
          (Finset.mem_union.mpr (Or.inl hx)))
        (fun d hd => hConsts
          (Finset.mem_union.mpr (Or.inl hd)))
        (fun x hx => hσ x
          (Finset.mem_union.mpr (Or.inl hx)))
        (fun x hx => hτ x
          (Finset.mem_union.mpr (Or.inl hx)))
        (Assign.sameSupportType_mono hType
          (fun x hx =>
            Finset.mem_union.mpr (Or.inl hx)))
      have hψ := ihψ
        (fun x hx => hVars
          (Finset.mem_union.mpr (Or.inr hx)))
        (fun d hd => hConsts
          (Finset.mem_union.mpr (Or.inr hd)))
        (fun x hx => hσ x
          (Finset.mem_union.mpr (Or.inr hx)))
        (fun x hx => hτ x
          (Finset.mem_union.mpr (Or.inr hx)))
        (Assign.sameSupportType_mono hType
          (fun x hx =>
            Finset.mem_union.mpr (Or.inr hx)))
      exact and_congr hφ hψ
  | or φ ψ ihφ ihψ =>
      have hφ := ihφ
        (fun x hx => hVars
          (Finset.mem_union.mpr (Or.inl hx)))
        (fun d hd => hConsts
          (Finset.mem_union.mpr (Or.inl hd)))
        (fun x hx => hσ x
          (Finset.mem_union.mpr (Or.inl hx)))
        (fun x hx => hτ x
          (Finset.mem_union.mpr (Or.inl hx)))
        (Assign.sameSupportType_mono hType
          (fun x hx =>
            Finset.mem_union.mpr (Or.inl hx)))
      have hψ := ihψ
        (fun x hx => hVars
          (Finset.mem_union.mpr (Or.inr hx)))
        (fun d hd => hConsts
          (Finset.mem_union.mpr (Or.inr hd)))
        (fun x hx => hσ x
          (Finset.mem_union.mpr (Or.inr hx)))
        (fun x hx => hτ x
          (Finset.mem_union.mpr (Or.inr hx)))
        (Assign.sameSupportType_mono hType
          (fun x hx =>
            Finset.mem_union.mpr (Or.inr hx)))
      exact or_congr hφ hψ
  | not φ ih =>
      have hφ := ih hVars hConsts hσ hτ hType
      exact not_congr hφ
  | imp φ ψ ihφ ihψ =>
      have hφ := ihφ
        (fun x hx => hVars
          (Finset.mem_union.mpr (Or.inl hx)))
        (fun d hd => hConsts
          (Finset.mem_union.mpr (Or.inl hd)))
        (fun x hx => hσ x
          (Finset.mem_union.mpr (Or.inl hx)))
        (fun x hx => hτ x
          (Finset.mem_union.mpr (Or.inl hx)))
        (Assign.sameSupportType_mono hType
          (fun x hx =>
            Finset.mem_union.mpr (Or.inl hx)))
      have hψ := ihψ
        (fun x hx => hVars
          (Finset.mem_union.mpr (Or.inr hx)))
        (fun d hd => hConsts
          (Finset.mem_union.mpr (Or.inr hd)))
        (fun x hx => hσ x
          (Finset.mem_union.mpr (Or.inr hx)))
        (fun x hx => hτ x
          (Finset.mem_union.mpr (Or.inr hx)))
        (Assign.sameSupportType_mono hType
          (fun x hx =>
            Finset.mem_union.mpr (Or.inr hx)))
      exact imp_congr hφ hψ
  | iff φ ψ ihφ ihψ =>
      have hφ := ihφ
        (fun x hx => hVars
          (Finset.mem_union.mpr (Or.inl hx)))
        (fun d hd => hConsts
          (Finset.mem_union.mpr (Or.inl hd)))
        (fun x hx => hσ x
          (Finset.mem_union.mpr (Or.inl hx)))
        (fun x hx => hτ x
          (Finset.mem_union.mpr (Or.inl hx)))
        (Assign.sameSupportType_mono hType
          (fun x hx =>
            Finset.mem_union.mpr (Or.inl hx)))
      have hψ := ihψ
        (fun x hx => hVars
          (Finset.mem_union.mpr (Or.inr hx)))
        (fun d hd => hConsts
          (Finset.mem_union.mpr (Or.inr hd)))
        (fun x hx => hσ x
          (Finset.mem_union.mpr (Or.inr hx)))
        (fun x hx => hτ x
          (Finset.mem_union.mpr (Or.inr hx)))
        (Assign.sameSupportType_mono hType
          (fun x hx =>
            Finset.mem_union.mpr (Or.inr hx)))
      exact iff_congr hφ hψ
  | forall_ x φ ih =>
      have hInsertVars :
          insert x φ.allVars ⊆ W := by
        simpa [allVars] using hVars
      have hxW : x ∈ W :=
        hInsertVars (Finset.mem_insert_self x φ.allVars)
      have hBodyVars : φ.allVars ⊆ W := by
        intro y hy
        exact hInsertVars (Finset.mem_insert_of_mem hy)
      have hBodyConsts : φ.constants ⊆ S := by
        simpa [constants] using hConsts
      have hEraseSubset :
          φ.freeVars.erase x ⊆ W.erase x := by
        intro y hy
        rcases Finset.mem_erase.mp hy with ⟨hyx, hyFree⟩
        exact Finset.mem_erase.mpr
          ⟨hyx, hBodyVars
            (Formula.freeVars_subset_allVars φ hyFree)⟩
      have hVCardW :
          (φ.freeVars.erase x).card < W.card :=
        lt_of_le_of_lt
          (Finset.card_le_card hEraseSubset)
          (Finset.card_erase_lt_of_mem hxW)
      have hVCardR :
          (φ.freeVars.erase x).card < R.card := by
        rw [hCard]
        exact hVCardW
      have hFreeSubset :
          φ.freeVars ⊆
            insert x (φ.freeVars.erase x) :=
        Finset.insert_erase_subset x φ.freeVars
      simp only [ArbitraryAssignSatIn]
      constructor
      · intro hAll e heP
        obtain ⟨d, hdQ, hExtSwap⟩ :=
          Assign.sameSupportType_update
            (S := S) (R := R)
            (V := φ.freeVars.erase x)
            (σ := τ) (τ := σ)
            (P := Q) (x := x)
            (Assign.sameSupportType_symm hType)
            hσ hS_Q hR_Q hDisj hVCardR e
        have hσ' :
            Assign.MapsInto
              (Assign.update σ x d) φ.freeVars Q :=
          Assign.mapsInto_update hσ hdQ
        have hτ' :
            Assign.MapsInto
              (Assign.update τ x e) φ.freeVars P :=
          Assign.mapsInto_update hτ heP
        have hType' :
            Assign.SameSupportType S φ.freeVars
              (Assign.update σ x d)
              (Assign.update τ x e) :=
          Assign.sameSupportType_mono
            (Assign.sameSupportType_symm hExtSwap)
            hFreeSubset
        exact
          (ih hBodyVars hBodyConsts
            hσ' hτ' hType').mp (hAll d hdQ)
      · intro hAll d hdQ
        obtain ⟨e, heP, hExt⟩ :=
          Assign.sameSupportType_update
            (S := S) (R := R)
            (V := φ.freeVars.erase x)
            (σ := σ) (τ := τ)
            (P := P) (x := x)
            hType hτ hS_P hR_P
            hDisj hVCardR d
        have hσ' :
            Assign.MapsInto
              (Assign.update σ x d) φ.freeVars Q :=
          Assign.mapsInto_update hσ hdQ
        have hτ' :
            Assign.MapsInto
              (Assign.update τ x e) φ.freeVars P :=
          Assign.mapsInto_update hτ heP
        have hType' :
            Assign.SameSupportType S φ.freeVars
              (Assign.update σ x d)
              (Assign.update τ x e) :=
          Assign.sameSupportType_mono hExt hFreeSubset
        exact
          (ih hBodyVars hBodyConsts
            hσ' hτ' hType').mpr (hAll e heP)
  | exists_ x φ ih =>
      have hInsertVars :
          insert x φ.allVars ⊆ W := by
        simpa [allVars] using hVars
      have hxW : x ∈ W :=
        hInsertVars (Finset.mem_insert_self x φ.allVars)
      have hBodyVars : φ.allVars ⊆ W := by
        intro y hy
        exact hInsertVars (Finset.mem_insert_of_mem hy)
      have hBodyConsts : φ.constants ⊆ S := by
        simpa [constants] using hConsts
      have hEraseSubset :
          φ.freeVars.erase x ⊆ W.erase x := by
        intro y hy
        rcases Finset.mem_erase.mp hy with ⟨hyx, hyFree⟩
        exact Finset.mem_erase.mpr
          ⟨hyx, hBodyVars
            (Formula.freeVars_subset_allVars φ hyFree)⟩
      have hVCardW :
          (φ.freeVars.erase x).card < W.card :=
        lt_of_le_of_lt
          (Finset.card_le_card hEraseSubset)
          (Finset.card_erase_lt_of_mem hxW)
      have hVCardR :
          (φ.freeVars.erase x).card < R.card := by
        rw [hCard]
        exact hVCardW
      have hFreeSubset :
          φ.freeVars ⊆
            insert x (φ.freeVars.erase x) :=
        Finset.insert_erase_subset x φ.freeVars
      simp only [ArbitraryAssignSatIn]
      constructor
      · rintro ⟨d, hdQ, hSat⟩
        obtain ⟨e, heP, hExt⟩ :=
          Assign.sameSupportType_update
            (S := S) (R := R)
            (V := φ.freeVars.erase x)
            (σ := σ) (τ := τ)
            (P := P) (x := x)
            hType hτ hS_P hR_P
            hDisj hVCardR d
        have hσ' :
            Assign.MapsInto
              (Assign.update σ x d) φ.freeVars Q :=
          Assign.mapsInto_update hσ hdQ
        have hτ' :
            Assign.MapsInto
              (Assign.update τ x e) φ.freeVars P :=
          Assign.mapsInto_update hτ heP
        have hType' :
            Assign.SameSupportType S φ.freeVars
              (Assign.update σ x d)
              (Assign.update τ x e) :=
          Assign.sameSupportType_mono hExt hFreeSubset
        exact ⟨e, heP,
          (ih hBodyVars hBodyConsts
            hσ' hτ' hType').mp hSat⟩
      · rintro ⟨e, heP, hSat⟩
        obtain ⟨d, hdQ, hExtSwap⟩ :=
          Assign.sameSupportType_update
            (S := S) (R := R)
            (V := φ.freeVars.erase x)
            (σ := τ) (τ := σ)
            (P := Q) (x := x)
            (Assign.sameSupportType_symm hType)
            hσ hS_Q hR_Q hDisj hVCardR e
        have hσ' :
            Assign.MapsInto
              (Assign.update σ x d) φ.freeVars Q :=
          Assign.mapsInto_update hσ hdQ
        have hτ' :
            Assign.MapsInto
              (Assign.update τ x e) φ.freeVars P :=
          Assign.mapsInto_update hτ heP
        have hType' :
            Assign.SameSupportType S φ.freeVars
              (Assign.update σ x d)
              (Assign.update τ x e) :=
          Assign.sameSupportType_mono
            (Assign.sameSupportType_symm hExtSwap)
            hFreeSubset
        exact ⟨d, hdQ,
          (ih hBodyVars hBodyConsts
            hσ' hτ' hType').mpr hSat⟩

end Formula

namespace Sentence

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private theorem satIn_iff_of_finite_representatives
    (φ : Sentence D Γ)
    (I : Instance D Γ)
    {S R : Finset D}
    {Q P : Set D}
    (hS_Q : (↑S : Set D) ⊆ Q)
    (hS_P : (↑S : Set D) ⊆ P)
    (hR_Q : (↑R : Set D) ⊆ Q)
    (hR_P : (↑R : Set D) ⊆ P)
    (hDisj : Disjoint R S)
    (hCard : R.card = φ.1.allVars.card)
    (hConsts : φ.constants ⊆ S)
    (hAdom : I.Adom ⊆ S) :
    (φ.SatIn I Q ↔ φ.SatIn I P) := by
  have hFree : φ.1.freeVars = ∅ := φ.2
  rw [Sentence.satIn_iff φ I Q default]
  rw [Sentence.satIn_iff φ I P default]
  have hRaw :=
    Formula.arbitraryAssignSatIn_iff_of_sameSupportType
      (S := S) (R := R) (W := φ.1.allVars)
      (Q := Q) (P := P)
      hS_Q hS_P hR_Q hR_P hDisj hCard
      φ.1 I (σ := default) (τ := default)
      (fun _ hx => hx) hConsts hAdom
      (by simp [hFree, Assign.MapsInto])
      (by simp [hFree, Assign.MapsInto])
      (by simp [hFree, Assign.SameSupportType])
  simpa [Formula.SatIn, hFree,
    Assign.MapsInto] using hRaw

/-
  A sentence cannot distinguish an arbitrary quantifier
  domain from a finite subdomain containing its full
  instance-and-constant support.
-/
theorem exists_finite_quantifierDomain_satIn_iff
    (φ : Sentence D Γ)
    (I : Instance D Γ)
    (Q : Set D)
    (hSupport :
      (↑(RelCalc.Adom φ.1 I) : Set D) ⊆ Q) :
    ∃ Q₀ : Finset D,
      RelCalc.Adom φ.1 I ⊆ Q₀ ∧
        (↑Q₀ : Set D) ⊆ Q ∧
        (φ.SatIn I Q ↔
          φ.SatIn I (↑Q₀ : Set D)) := by
  rcases Q.finite_or_infinite with hFinite | hInfinite
  · rcases hFinite.exists_finset with ⟨Q₀, hQ₀⟩
    refine ⟨Q₀, ?_, ?_, ?_⟩
    · intro d hd
      exact (hQ₀ d).mpr (hSupport hd)
    · intro d hd
      exact (hQ₀ d).mp hd
    · have hSet : (↑Q₀ : Set D) = Q := by
        ext d
        exact hQ₀ d
      rw [hSet]
  · let S : Finset D := RelCalc.Adom φ.1 I
    have hOutside :
        (Q \ (↑S : Set D)).Infinite :=
      hInfinite.diff S.finite_toSet
    rcases hOutside.exists_subset_card_eq
        φ.1.allVars.card with ⟨R, hRSub, hRCard⟩
    let Q₀ : Finset D := S ∪ R
    have hR_Q : (↑R : Set D) ⊆ Q := by
      intro d hd
      exact (hRSub hd).1
    have hR_S : Disjoint R S := by
      apply Finset.disjoint_left.mpr
      intro d hdR hdS
      exact (hRSub hdR).2 hdS
    refine ⟨Q₀, ?_, ?_, ?_⟩
    · intro d hd
      exact Finset.mem_union.mpr (Or.inl hd)
    · intro d hd
      rcases Finset.mem_union.mp hd with hdS | hdR
      · exact hSupport hdS
      · exact hR_Q hdR
    · apply satIn_iff_of_finite_representatives
        (φ := φ) (I := I)
        (S := S) (R := R)
        (Q := Q) (P := (↑Q₀ : Set D))
      · exact hSupport
      · intro d hd
        exact Finset.mem_union.mpr (Or.inl hd)
      · exact hR_Q
      · intro d hd
        exact Finset.mem_union.mpr (Or.inr hd)
      · exact hR_S
      · exact hRCard
      · intro d hd
        exact Finset.mem_union.mpr (Or.inr hd)
      · intro d hd
        exact Finset.mem_union.mpr (Or.inl hd)

end Sentence

end RelCalc

------------------------------------------------------------
-- Sentence Domain Independence And Validity
------------------------------------------------------------

namespace RelCalc

namespace Sentence

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Active-domain validity over instances of the exact
  schema.
-/
def LocalAdomValid
    (φ : Sentence D Γ) : Prop :=
  ∀ I : Instance D Γ,
    φ.SatIn I (Adom.toSet φ.1 I)

/-
  Satisfaction is invariant under arbitrary quantifier
  domain extensions of the formula active domain.
-/
def DomainIndependent
    (φ : Sentence D Γ) : Prop :=
  ∀ (I : Instance D Γ) (Q : Set D),
    Adom.toSet φ.1 I ⊆ Q →
      (φ.SatIn I (Adom.toSet φ.1 I) ↔
        φ.SatIn I Q)

/-
  Validity on every finite extension of the formula active
  domain.
-/
def FiniteExtensionValid
    (φ : Sentence D Γ) : Prop :=
  ∀ (I : Instance D Γ) (Q : Finset D),
    RelCalc.Adom φ.1 I ⊆ Q →
      φ.SatIn I (fun d => d ∈ Q)

/-
  Active-domain validity over every extension of the
  sentence schema. The sentence reads the reduct, while its
  quantifiers range over the larger instance active domain
  together with the sentence constants.
-/
def AdomValid
    (φ : Sentence D Γ) : Prop :=
  ∀ {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (J : Instance D Δ),
      φ.SatIn
        (Instance.reduct hExt J)
        (fun d => d ∈ J.Adom ∪ φ.constants)

/-
  Local validity and domain independence imply
  finite-extension validity.
-/
theorem finiteExtensionValid_of_local_and_di
    (φ : Sentence D Γ)
    (hLocal : φ.LocalAdomValid)
    (hDI : φ.DomainIndependent) :
    φ.FiniteExtensionValid := by
  intro I Q hSupport
  have hSubset : Adom.toSet φ.1 I ⊆
      (fun d => d ∈ Q) := by
    intro d hd
    exact hSupport hd
  exact (hDI I (fun d => d ∈ Q) hSubset).mp
    (hLocal I)

/-
  Finite-extension validity implies exact-schema local
  validity.
-/
theorem FiniteExtensionValid.localAdomValid
    {φ : Sentence D Γ}
    (hFinite : φ.FiniteExtensionValid) :
    φ.LocalAdomValid := by
  intro I
  exact hFinite I (RelCalc.Adom φ.1 I) (by
    intro d hd
    exact hd)

/-
  Strong schema-extension validity implies local validity.
-/
theorem AdomValid.localAdomValid
    {φ : Sentence D Γ}
    (hValid : φ.AdomValid) :
    φ.LocalAdomValid := by
  intro I
  have h :=
    hValid (UnnamedSchema.extensionOf_refl Γ) I
  rw [Instance.reduct_refl] at h
  exact h

/-
  With one fresh relation symbol, schema-extension validity
  covers every finite quantifier-domain extension.
-/
theorem finiteExtensionValid_of_adomValid
    (φ : Sentence D Γ)
    (hValid : φ.AdomValid)
    (hFresh : ∃ X : A, X ∉ Γ.syms) :
    φ.FiniteExtensionValid := by
  rcases hFresh with ⟨X, hX⟩
  intro I Q hSupport
  let Δ := Γ.insertFresh X 1 hX
  let hExt : Δ.extensionOf Γ :=
    UnnamedSchema.insertFresh_extensionOf
      Γ X 1 hX
  let J : Instance D Δ :=
    I.addFreshUnary X hX Q
  have hPadded := hValid hExt J
  have hReduct : Instance.reduct hExt J = I := by
    exact Instance.reduct_addFreshUnary I X hX Q
  have hDomain : J.Adom ∪ φ.constants = Q := by
    rw [show J.Adom = I.Adom ∪ Q by
      exact Instance.Adom_addFreshUnary I X hX Q]
    apply Finset.Subset.antisymm
    · intro d hd
      rcases Finset.mem_union.mp hd with hd | hd
      · rcases Finset.mem_union.mp hd with hd | hd
        · exact hSupport
            (Finset.mem_union_left _ hd)
        · exact hd
      · exact hSupport
          (Finset.mem_union_right _ hd)
    · intro d hd
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ hd)
  rw [hReduct, hDomain] at hPadded
  exact hPadded

/- Finite-extension validity covers schema extensions. -/
theorem adomValid_of_finiteExtensionValid
    (φ : Sentence D Γ)
    (hFinite : φ.FiniteExtensionValid) :
    φ.AdomValid := by
  intro Δ hExt J
  let I := Instance.reduct hExt J
  let Q := J.Adom ∪ φ.constants
  have hSupport : RelCalc.Adom φ.1 I ⊆ Q := by
    intro d hd
    rw [RelCalc.Adom] at hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact Finset.mem_union_left _
        (Instance.Adom_reduct_subset hExt J hd)
    · exact Finset.mem_union_right _ hd
  exact hFinite I Q hSupport

/-
  With one fresh relation symbol, schema-extension and
  finite-extension active-domain validity coincide.
-/
theorem adomValid_iff_finiteExtensionValid
    (φ : Sentence D Γ)
    (hFresh : ∃ X : A, X ∉ Γ.syms) :
    φ.AdomValid ↔ φ.FiniteExtensionValid := by
  constructor
  · intro hValid
    exact finiteExtensionValid_of_adomValid
      φ hValid hFresh
  · exact adomValid_of_finiteExtensionValid φ

/-
  Finite-extension validity implies arbitrary-set domain
  independence.
-/
theorem FiniteExtensionValid.domainIndependent
    {φ : Sentence D Γ}
    (hFinite : φ.FiniteExtensionValid) :
    φ.DomainIndependent := by
  intro I Q hSupport
  rcases exists_finite_quantifierDomain_satIn_iff
      φ I Q hSupport with
    ⟨Q₀, hSupportQ₀, _hQ₀Q, hEquiv⟩
  have hFiniteQ₀ := hFinite I Q₀ hSupportQ₀
  have hQ : φ.SatIn I Q := hEquiv.mpr hFiniteQ₀
  exact iff_of_true
    (hFinite.localAdomValid I) hQ

/-
  With one fresh relation symbol, schema-extension validity
  implies domain independence.
-/
theorem AdomValid.domainIndependent
    {φ : Sentence D Γ}
    (hValid : φ.AdomValid)
    (hFresh : ∃ X : A, X ∉ Γ.syms) :
    φ.DomainIndependent :=
  (finiteExtensionValid_of_adomValid
    φ hValid hFresh).domainIndependent

/-
  Finite-extension validity is exactly local active-domain
  validity together with domain independence.
-/
theorem finiteExtensionValid_iff_local_and_di
    (φ : Sentence D Γ) :
    φ.FiniteExtensionValid ↔
      φ.LocalAdomValid ∧ φ.DomainIndependent := by
  constructor
  · intro hFinite
    exact ⟨hFinite.localAdomValid,
      hFinite.domainIndependent⟩
  · rintro ⟨hLocal, hDI⟩
    exact
      finiteExtensionValid_of_local_and_di
        φ hLocal hDI

/-
  With one fresh relation symbol, active-domain validity is
  exactly local validity plus domain independence.
-/
theorem adomValid_iff_localAdomValid_and_domainIndependent
    (φ : Sentence D Γ)
    (hFresh : ∃ X : A, X ∉ Γ.syms) :
    φ.AdomValid ↔
      φ.LocalAdomValid ∧ φ.DomainIndependent := by
  rw [adomValid_iff_finiteExtensionValid φ hFresh]
  exact finiteExtensionValid_iff_local_and_di φ

end Sentence

end RelCalc
