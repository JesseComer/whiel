-- Author: Jesse Comer
import Databases.RelCalc.AdomSemantics
import Databases.RelCalc.BoundVariableRenaming
import Databases.RelCalc.TermSubstitution

/-
  This file defines relation-symbol substitution for
  RelCalc formulas.

  Key definitions include:
    * `RelCalc.Formula.substRelation`
    * `RelCalc.Formula.DefinesRelation`

  Correctness is proven by:
    * `RelCalc.Formula.freeVars_substRelation`
    * `RelCalc.Formula.arbitraryAssignSatIn_substRelation`
    * `RelCalc.Formula.satIn_substRelation`
    * `RelCalc.Formula.adomSat_substRelation`

  Term substitution into formulas lives in the term
  substitution file.
-/

------------------------------------------------------------
-- Relation Substitution Definitions
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Raw relation substitution without alpha-renaming. -/
private def substRelationRaw
    (φ : Formula D Γ)
    (X : Γ.syms)
    (xs : Vector Var (Γ.arity X))
    (θ : Formula D Γ) :
    Formula D Γ :=
  match φ with
  | .top => .top
  | .bot => .bot
  | .eq t₁ t₂ => .eq t₁ t₂
  | .rel a =>
      if hYX : a.rel = X then
        by
          subst hYX
          exact θ.substTerms
            (RelTerm.Substitution.ofVector xs a.args)
      else
        .rel a
  | .and φ ψ =>
      .and
        (substRelationRaw φ X xs θ)
        (substRelationRaw ψ X xs θ)
  | .or φ ψ =>
      .or
        (substRelationRaw φ X xs θ)
        (substRelationRaw ψ X xs θ)
  | .not φ =>
      .not (substRelationRaw φ X xs θ)
  | .imp φ ψ =>
      .imp
        (substRelationRaw φ X xs θ)
        (substRelationRaw ψ X xs θ)
  | .iff φ ψ =>
      .iff
        (substRelationRaw φ X xs θ)
        (substRelationRaw ψ X xs θ)
  | .forall_ x φ =>
      .forall_ x (substRelationRaw φ X xs θ)
  | .exists_ x φ =>
      .exists_ x (substRelationRaw φ X xs θ)

/- Relation substitution is capture-free in `φ`. -/
private def FreeForRelationSubst :
    Formula D Γ →
      (X : Γ.syms) →
      Vector Var (Γ.arity X) →
      Formula D Γ →
      Prop
| .top, _, _, _ => True
| .bot, _, _, _ => True
| .eq _ _, _, _, _ => True
| .rel a, X, xs, θ =>
    if hYX : a.rel = X then
      by
        subst hYX
        exact θ.FreeForTermSubstMap
          (RelTerm.Substitution.ofVector xs a.args)
    else
      True
| .and φ ψ, X, xs, θ =>
    FreeForRelationSubst φ X xs θ ∧
      FreeForRelationSubst ψ X xs θ
| .or φ ψ, X, xs, θ =>
    FreeForRelationSubst φ X xs θ ∧
      FreeForRelationSubst ψ X xs θ
| .not φ, X, xs, θ =>
    FreeForRelationSubst φ X xs θ
| .imp φ ψ, X, xs, θ =>
    FreeForRelationSubst φ X xs θ ∧
      FreeForRelationSubst ψ X xs θ
| .iff φ ψ, X, xs, θ =>
    FreeForRelationSubst φ X xs θ ∧
      FreeForRelationSubst ψ X xs θ
| .forall_ _ φ, X, xs, θ =>
    FreeForRelationSubst φ X xs θ
| .exists_ _ φ, X, xs, θ =>
    FreeForRelationSubst φ X xs θ

/- Capture-avoiding relation substitution. -/
def substRelation
    (φ : Formula D Γ)
    (X : Γ.syms)
    (xs : Vector Var (Γ.arity X))
    (θ : Formula D Γ) :
    Formula D Γ :=
  substRelationRaw φ X xs
    (θ.alphaRenameAvoiding φ.allVarList)

/- The relation supplied by a replacement formula. -/
def DefinesRelation
    {n : Nat}
    (Q : Set D)
    (I : Instance D Γ)
    (xs : Vector Var n)
    (θ : Formula D Γ)
    (R : FinRelation D n) :
    Prop :=
  ∀ t : Tuple D n,
    t ∈ R ↔
      ∃ σ : Assign D,
        Assign.Realizes σ xs t ∧
          Formula.ArbitraryAssignSatIn Q I σ θ

end Formula

end RelCalc

------------------------------------------------------------
-- Relation Substitution Structural Lemmas
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Vector substitutions introduce only tuple variables. -/
private lemma vars_ofVector_subset_tupleVars
    {n : Nat}
    {xs : Vector Var n}
    {ts : Vector (RelTerm D) n}
    {z y : Var}
    (hNoDup : xs.toList.Nodup)
    (hz : z ∈ xs.toList.toFinset)
    (hy :
      y ∈
        (RelTerm.Substitution.ofVector xs ts z).vars) :
    y ∈ RelTerm.tupleVars ts := by
  have hzList : z ∈ xs.toList := by
    simpa using hz
  rcases List.mem_iff_get.mp hzList with
    ⟨i, hi⟩
  let j : Fin n :=
    ⟨i.1, by
      simpa [Vector.length_toList] using i.2⟩
  have hVar : xs.get j = z := by
    change xs[i.1] = z
    have hCoord :
        xs.toList[i.1] = xs[i.1] :=
      Vector.getElem_toList i.2
    exact hCoord.symm.trans hi
  have hGet := RelTerm.Substitution.ofVector_get
    (D := D) (xs := xs) (ts := ts)
    hNoDup j
  have hTerm :
      RelTerm.Substitution.ofVector xs ts z = ts.get j := by
    simpa [hVar] using hGet
  exact (RelTerm.mem_tupleVars_iff
    (ts := ts) (x := y)).mpr
    ⟨j, by simpa [hTerm] using hy⟩

/-
  Bounded substitutions are capture-free for clean formulas.
-/
private lemma freeForTermSubstMap_of_bound_avoids
    (θ : Formula D Γ)
    (ρ : RelTerm.Substitution D)
    (avoid : List Var)
    (hClean : θ.IsAlphaClean)
    (hAvoid :
      ∀ y ∈ θ.boundVarList, y ∉ avoid)
    (hSub :
      ∀ z ∈ θ.freeVars,
        ∀ y ∈ (ρ z).vars, y ∈ avoid) :
    θ.FreeForTermSubstMap ρ := by
  induction θ generalizing ρ avoid with
  | top =>
      simp [FreeForTermSubstMap]
  | bot =>
      simp [FreeForTermSubstMap]
  | eq t u =>
      simp [FreeForTermSubstMap]
  | rel a =>
      simp [FreeForTermSubstMap]
  | and φ ψ ihφ ihψ =>
      constructor
      · apply ihφ
        · unfold IsAlphaClean at *
          constructor
          · simpa [boundVarList] using
              (List.nodup_append.mp hClean.1).1
          · intro y hy hFree
            exact hClean.2 y
              (by simp [boundVarList, hy])
              (by simp [freeVars, hFree])
        · intro y hy
          exact hAvoid y (by simp [boundVarList, hy])
        · intro z hz y hy
          exact hSub z (by simp [freeVars, hz]) y hy
      · apply ihψ
        · unfold IsAlphaClean at *
          constructor
          · simpa [boundVarList] using
              (List.nodup_append.mp hClean.1).2.1
          · intro y hy hFree
            exact hClean.2 y
              (by simp [boundVarList, hy])
              (by simp [freeVars, hFree])
        · intro y hy
          exact hAvoid y (by simp [boundVarList, hy])
        · intro z hz y hy
          exact hSub z (by simp [freeVars, hz]) y hy
  | or φ ψ ihφ ihψ =>
      constructor
      · apply ihφ
        · unfold IsAlphaClean at *
          constructor
          · simpa [boundVarList] using
              (List.nodup_append.mp hClean.1).1
          · intro y hy hFree
            exact hClean.2 y
              (by simp [boundVarList, hy])
              (by simp [freeVars, hFree])
        · intro y hy
          exact hAvoid y (by simp [boundVarList, hy])
        · intro z hz y hy
          exact hSub z (by simp [freeVars, hz]) y hy
      · apply ihψ
        · unfold IsAlphaClean at *
          constructor
          · simpa [boundVarList] using
              (List.nodup_append.mp hClean.1).2.1
          · intro y hy hFree
            exact hClean.2 y
              (by simp [boundVarList, hy])
              (by simp [freeVars, hFree])
        · intro y hy
          exact hAvoid y (by simp [boundVarList, hy])
        · intro z hz y hy
          exact hSub z (by simp [freeVars, hz]) y hy
  | not φ ih =>
      apply ih
      · exact hClean
      · exact hAvoid
      · exact hSub
  | imp φ ψ ihφ ihψ =>
      constructor
      · apply ihφ
        · unfold IsAlphaClean at *
          constructor
          · simpa [boundVarList] using
              (List.nodup_append.mp hClean.1).1
          · intro y hy hFree
            exact hClean.2 y
              (by simp [boundVarList, hy])
              (by simp [freeVars, hFree])
        · intro y hy
          exact hAvoid y (by simp [boundVarList, hy])
        · intro z hz y hy
          exact hSub z (by simp [freeVars, hz]) y hy
      · apply ihψ
        · unfold IsAlphaClean at *
          constructor
          · simpa [boundVarList] using
              (List.nodup_append.mp hClean.1).2.1
          · intro y hy hFree
            exact hClean.2 y
              (by simp [boundVarList, hy])
              (by simp [freeVars, hFree])
        · intro y hy
          exact hAvoid y (by simp [boundVarList, hy])
        · intro z hz y hy
          exact hSub z (by simp [freeVars, hz]) y hy
  | iff φ ψ ihφ ihψ =>
      constructor
      · apply ihφ
        · unfold IsAlphaClean at *
          constructor
          · simpa [boundVarList] using
              (List.nodup_append.mp hClean.1).1
          · intro y hy hFree
            exact hClean.2 y
              (by simp [boundVarList, hy])
              (by simp [freeVars, hFree])
        · intro y hy
          exact hAvoid y (by simp [boundVarList, hy])
        · intro z hz y hy
          exact hSub z (by simp [freeVars, hz]) y hy
      · apply ihψ
        · unfold IsAlphaClean at *
          constructor
          · simpa [boundVarList] using
              (List.nodup_append.mp hClean.1).2.1
          · intro y hy hFree
            exact hClean.2 y
              (by simp [boundVarList, hy])
              (by simp [freeVars, hFree])
        · intro y hy
          exact hAvoid y (by simp [boundVarList, hy])
        · intro z hz y hy
          exact hSub z (by simp [freeVars, hz]) y hy
  | forall_ x φ ih =>
      constructor
      · intro z hz hx
        have hxAvoid := hSub z
          (by simpa [freeVars] using hz) x hx
        exact hAvoid x
          (by simp [boundVarList])
          hxAvoid
      · apply ih
          (ρ := RelTerm.Substitution.update ρ x (.var x))
          (avoid := x :: avoid)
        · unfold IsAlphaClean at *
          constructor
          · exact (List.nodup_cons.mp hClean.1).2
          · intro y hy hFree
            have hyx : y ≠ x := by
              intro h
              subst h
              exact (List.nodup_cons.mp hClean.1).1 hy
            exact hClean.2 y
              (by simp [boundVarList, hy])
              (by
                simp [freeVars, Finset.mem_erase,
                  hyx, hFree])
        · intro y hy hyMem
          have hyMem' : y = x ∨ y ∈ avoid := by
            simpa using hyMem
          rcases hyMem' with hyx | hyAvoid
          · subst hyx
            exact (List.nodup_cons.mp hClean.1).1 hy
          · exact hAvoid y
              (by simp [boundVarList, hy])
              hyAvoid
        · intro z hz y hy
          by_cases hzx : z = x
          · have hyEq : y = x := by
              simpa [RelTerm.Substitution.update, hzx,
                RelTerm.vars] using hy
            subst hyEq
            simp
          · have hzOuter :
                z ∈ (Formula.forall_ x φ).freeVars := by
              simp [freeVars, Finset.mem_erase, hzx, hz]
            have hyAvoid := hSub z hzOuter y (by
              simpa [RelTerm.Substitution.update, hzx]
                using hy)
            exact List.mem_cons_of_mem _ hyAvoid
  | exists_ x φ ih =>
      constructor
      · intro z hz hx
        have hxAvoid := hSub z
          (by simpa [freeVars] using hz) x hx
        exact hAvoid x
          (by simp [boundVarList])
          hxAvoid
      · apply ih
          (ρ := RelTerm.Substitution.update ρ x (.var x))
          (avoid := x :: avoid)
        · unfold IsAlphaClean at *
          constructor
          · exact (List.nodup_cons.mp hClean.1).2
          · intro y hy hFree
            have hyx : y ≠ x := by
              intro h
              subst h
              exact (List.nodup_cons.mp hClean.1).1 hy
            exact hClean.2 y
              (by simp [boundVarList, hy])
              (by
                simp [freeVars, Finset.mem_erase,
                  hyx, hFree])
        · intro y hy hyMem
          have hyMem' : y = x ∨ y ∈ avoid := by
            simpa using hyMem
          rcases hyMem' with hyx | hyAvoid
          · subst hyx
            exact (List.nodup_cons.mp hClean.1).1 hy
          · exact hAvoid y
              (by simp [boundVarList, hy])
              hyAvoid
        · intro z hz y hy
          by_cases hzx : z = x
          · have hyEq : y = x := by
              simpa [RelTerm.Substitution.update, hzx,
                RelTerm.vars] using hy
            subst hyEq
            simp
          · have hzOuter :
                z ∈ (Formula.exists_ x φ).freeVars := by
              simp [freeVars, Finset.mem_erase, hzx, hz]
            have hyAvoid := hSub z hzOuter y (by
              simpa [RelTerm.Substitution.update, hzx]
                using hy)
            exact List.mem_cons_of_mem _ hyAvoid

/- Relation substitution is free after avoiding renaming. -/
private lemma freeForRelationSubst_of_bound_avoids
    (φ : Formula D Γ)
    (X : Γ.syms)
    (xs : Vector Var (Γ.arity X))
    (θ : Formula D Γ)
    (hNoDup : xs.toList.Nodup)
    (hθFree : θ.freeVars = xs.toList.toFinset)
    (hClean : θ.IsAlphaClean)
    (hAvoid :
      ∀ y ∈ θ.boundVarList, y ∉ φ.allVarList) :
    φ.FreeForRelationSubst X xs θ := by
  induction φ with
  | top =>
      simp [FreeForRelationSubst]
  | bot =>
      simp [FreeForRelationSubst]
  | eq t u =>
      simp [FreeForRelationSubst]
  | rel a =>
      by_cases hYX : a.rel = X
      · subst hYX
        rw [FreeForRelationSubst]
        simp only [↓reduceDIte]
        apply freeForTermSubstMap_of_bound_avoids
          (θ := θ)
          (ρ := RelTerm.Substitution.ofVector xs a.args)
          (avoid := (Formula.rel a).allVarList)
        · exact hClean
        · exact hAvoid
        · intro z hz y hy
          have hzXs : z ∈ xs.toList.toFinset := by
            simpa [hθFree] using hz
          have hyTuple :
              y ∈ RelTerm.tupleVars a.args :=
            vars_ofVector_subset_tupleVars
              (D := D) hNoDup hzXs hy
          exact Formula.mem_allVarList_of_mem_allVars
            (by simpa [allVars] using hyTuple)
      · simp [FreeForRelationSubst, hYX]
  | and φ ψ ihφ ihψ =>
      constructor
      · apply ihφ
        intro y hy hMem
        exact hAvoid y hy
          (by simp [allVarList, hMem])
      · apply ihψ
        intro y hy hMem
        exact hAvoid y hy
          (by simp [allVarList, hMem])
  | or φ ψ ihφ ihψ =>
      constructor
      · apply ihφ
        intro y hy hMem
        exact hAvoid y hy
          (by simp [allVarList, hMem])
      · apply ihψ
        intro y hy hMem
        exact hAvoid y hy
          (by simp [allVarList, hMem])
  | not φ ih =>
      apply ih
      intro y hy hMem
      exact hAvoid y hy
        (by simpa [allVarList] using hMem)
  | imp φ ψ ihφ ihψ =>
      constructor
      · apply ihφ
        intro y hy hMem
        exact hAvoid y hy
          (by simp [allVarList, hMem])
      · apply ihψ
        intro y hy hMem
        exact hAvoid y hy
          (by simp [allVarList, hMem])
  | iff φ ψ ihφ ihψ =>
      constructor
      · apply ihφ
        intro y hy hMem
        exact hAvoid y hy
          (by simp [allVarList, hMem])
      · apply ihψ
        intro y hy hMem
        exact hAvoid y hy
          (by simp [allVarList, hMem])
  | forall_ x φ ih =>
      apply ih
      intro y hy hMem
      exact hAvoid y hy
        (by simp [allVarList, hMem])
  | exists_ x φ ih =>
      apply ih
      intro y hy hMem
      exact hAvoid y hy
        (by simp [allVarList, hMem])

/- Relation substitution preserves free variables. -/
private lemma freeVars_substRelationRaw
    (φ : Formula D Γ)
    (X : Γ.syms)
    (xs : Vector Var (Γ.arity X))
    (θ : Formula D Γ)
    (hNoDup : xs.toList.Nodup)
    (hθFree : θ.freeVars = xs.toList.toFinset)
    (hFree : φ.FreeForRelationSubst X xs θ) :
    (substRelationRaw φ X xs θ).freeVars =
      φ.freeVars := by
  induction φ with
  | top =>
      simp [substRelationRaw, freeVars]
  | bot =>
      simp [substRelationRaw, freeVars]
  | eq t₁ t₂ =>
      simp [substRelationRaw, freeVars]
  | rel a =>
      by_cases hYX : a.rel = X
      · subst hYX
        have hBody :
            θ.FreeForTermSubstMap
              (RelTerm.Substitution.ofVector xs a.args) := by
          simpa [FreeForRelationSubst] using hFree
        have hSub :=
          freeVars_substTerms
            θ
            (RelTerm.Substitution.ofVector xs a.args)
            hBody
        have hVars :
            RelTerm.Substitution.varsOn
                (RelTerm.Substitution.ofVector xs a.args)
                θ.freeVars =
              RelTerm.tupleVars a.args := by
          rw [hθFree]
          exact RelTerm.Substitution.varsOn_ofVector
            (D := D) (xs := xs)
            (ts := a.args) hNoDup
        simpa [substRelationRaw, freeVars] using
          hSub.trans hVars
      · simp [substRelationRaw, freeVars, hYX]
  | and φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substRelationRaw, freeVars,
        ihφ hφ, ihψ hψ]
  | or φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substRelationRaw, freeVars,
        ihφ hφ, ihψ hψ]
  | not φ ih =>
      simp [substRelationRaw, freeVars, ih hFree]
  | imp φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substRelationRaw, freeVars,
        ihφ hφ, ihψ hψ]
  | iff φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substRelationRaw, freeVars,
        ihφ hφ, ihψ hψ]
  | forall_ x φ ih =>
      simp [substRelationRaw, freeVars, ih hFree]
  | exists_ x φ ih =>
      simp [substRelationRaw, freeVars, ih hFree]

end Formula

end RelCalc

------------------------------------------------------------
-- Substitution Properties
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Relation substitution preserves recursive truth. -/
private theorem arbitraryAssignSatIn_substRelationRaw
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    {X : Γ.syms}
    {xs : Vector Var (Γ.arity X)}
    {θ : Formula D Γ}
    {R : FinRelation D (Γ.arity X)}
    (φ : Formula D Γ)
    (hNoDup : xs.toList.Nodup)
    (hθFree : θ.freeVars = xs.toList.toFinset)
    (hFree : φ.FreeForRelationSubst X xs θ)
    (hDef : DefinesRelation Q I xs θ R) :
    Formula.ArbitraryAssignSatIn Q I σ
        (substRelationRaw φ X xs θ) ↔
      Formula.ArbitraryAssignSatIn Q
        (Instance.update I X R) σ φ := by
  induction φ generalizing σ with
  | top =>
      simp [substRelationRaw, Formula.ArbitraryAssignSatIn]
  | bot =>
      simp [substRelationRaw, Formula.ArbitraryAssignSatIn]
  | eq t₁ t₂ =>
      simp [substRelationRaw, Formula.ArbitraryAssignSatIn]
  | rel a =>
      by_cases hYX : a.rel = X
      · subst hYX
        have hBody :
            θ.FreeForTermSubstMap
              (RelTerm.Substitution.ofVector xs a.args) := by
          simpa [FreeForRelationSubst] using hFree
        have hSub :=
          arbitraryAssignSatIn_substTerms
            (Q := Q) (I := I) (σ := σ)
            θ
            (RelTerm.Substitution.ofVector xs a.args)
            hBody
        have hReal :
            Assign.Realizes
              (RelTerm.Substitution.eval
                (RelTerm.Substitution.ofVector xs a.args) σ)
              xs
              (RelAtom.evalTuple σ a) :=
          RelTerm.Substitution.eval_ofVector_realizes
            (D := D) (σ := σ)
            (xs := xs) (ts := a.args)
            hNoDup
        have hEquiv :
            Formula.ArbitraryAssignSatIn Q I
                (RelTerm.Substitution.eval
                  (RelTerm.Substitution.ofVector xs a.args) σ)
                θ ↔
              RelAtom.evalTuple σ a ∈ R := by
          constructor
          · intro hSat
            exact (hDef (RelAtom.evalTuple σ a)).mpr
              ⟨RelTerm.Substitution.eval
                (RelTerm.Substitution.ofVector xs a.args) σ,
                hReal, hSat⟩
          · intro hMem
            rcases
                (hDef (RelAtom.evalTuple σ a)).mp hMem with
              ⟨τ, hτReal, hτSat⟩
            have hAgreeOut :
                Assign.AgreeOn τ
                  (RelTerm.Substitution.eval
                    (RelTerm.Substitution.ofVector xs a.args)
                    σ)
                  xs.toList.toFinset :=
              Assign.agreeOn_of_realizes
                hτReal hReal
            have hAgree :
                Assign.AgreeOn τ
                  (RelTerm.Substitution.eval
                    (RelTerm.Substitution.ofVector xs a.args)
                    σ)
                  θ.freeVars := by
              intro z hz
              exact hAgreeOut z
                (by simpa [hθFree] using hz)
            exact
              (holdsIn_eq_of_agreeOn_freeVars
                (Q := Q) (I := I)
                (φ := θ) hAgree).mp hτSat
        simpa [substRelationRaw,
          Formula.ArbitraryAssignSatIn, RelAtom.Sat,
          RelAtom.evalFact, RelFact.Mem] using hSub.trans hEquiv
      · simp [substRelationRaw, hYX,
          Formula.ArbitraryAssignSatIn, RelAtom.Sat,
          RelAtom.evalFact, RelFact.Mem]
  | and φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substRelationRaw, Formula.ArbitraryAssignSatIn,
        ihφ hφ, ihψ hψ]
  | or φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substRelationRaw, Formula.ArbitraryAssignSatIn,
        ihφ hφ, ihψ hψ]
  | not φ ih =>
      simp [substRelationRaw, Formula.ArbitraryAssignSatIn,
        ih hFree]
  | imp φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substRelationRaw, Formula.ArbitraryAssignSatIn,
        ihφ hφ, ihψ hψ]
  | iff φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substRelationRaw, Formula.ArbitraryAssignSatIn,
        ihφ hφ, ihψ hψ]
  | forall_ x φ ih =>
      constructor
      · intro hSat d hd
        exact (ih
          (σ := Assign.update σ x d)
          hFree).mp (hSat d hd)
      · intro hSat d hd
        exact (ih
          (σ := Assign.update σ x d)
          hFree).mpr (hSat d hd)
  | exists_ x φ ih =>
      constructor
      · rintro ⟨d, hd, hSat⟩
        exact ⟨d, hd,
          (ih
            (σ := Assign.update σ x d)
            hFree).mp hSat⟩
      · rintro ⟨d, hd, hSat⟩
        exact ⟨d, hd,
          (ih
            (σ := Assign.update σ x d)
            hFree).mpr hSat⟩

/- Satisfaction obeys relation substitution. -/
private theorem satIn_substRelationRaw
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    {X : Γ.syms}
    {xs : Vector Var (Γ.arity X)}
    {θ : Formula D Γ}
    {R : FinRelation D (Γ.arity X)}
    (φ : Formula D Γ)
    (hNoDup : xs.toList.Nodup)
    (hθFree : θ.freeVars = xs.toList.toFinset)
    (hFree : φ.FreeForRelationSubst X xs θ)
    (hDef : DefinesRelation Q I xs θ R) :
    (substRelationRaw φ X xs θ).SatIn I σ Q ↔
      φ.SatIn (Instance.update I X R) σ Q := by
  have hVars :=
    freeVars_substRelationRaw
      (φ := φ) (X := X) (xs := xs) (θ := θ)
      hNoDup hθFree hFree
  have hRaw :=
    arbitraryAssignSatIn_substRelationRaw
      (Q := Q) (I := I) (σ := σ)
      (X := X) (xs := xs) (θ := θ) (R := R)
      φ hNoDup hθFree hFree hDef
  constructor
  · rintro ⟨hMaps, hSat⟩
    exact ⟨by simpa [hVars] using hMaps,
      hRaw.mp hSat⟩
  · rintro ⟨hMaps, hSat⟩
    exact ⟨by simpa [hVars] using hMaps,
      hRaw.mpr hSat⟩

/- Adom satisfaction obeys relation substitution. -/
private theorem adomSat_substRelationRaw
    {I : Instance D Γ}
    {σ : Assign D}
    {X : Γ.syms}
    {xs : Vector Var (Γ.arity X)}
    {θ : Formula D Γ}
    {R : FinRelation D (Γ.arity X)}
    (φ : Formula D Γ)
    (hNoDup : xs.toList.Nodup)
    (hθFree : θ.freeVars = xs.toList.toFinset)
    (hFree : φ.FreeForRelationSubst X xs θ)
    (hDef :
      DefinesRelation
        (Adom.toSet (substRelationRaw φ X xs θ) I)
        I xs θ R) :
    (substRelationRaw φ X xs θ).AdomSat I σ ↔
      φ.SatIn (Instance.update I X R) σ
        (Adom.toSet (substRelationRaw φ X xs θ) I) := by
  simpa [Formula.AdomSat] using
    satIn_substRelationRaw
      (Q := Adom.toSet (substRelationRaw φ X xs θ) I)
      (I := I) (σ := σ)
      (X := X) (xs := xs) (θ := θ) (R := R)
      φ hNoDup hθFree hFree hDef

/- Alpha-renamed replacements are free for substitution. -/
private theorem freeForRelationSubst_alpha
    (φ : Formula D Γ)
    (X : Γ.syms)
    (xs : Vector Var (Γ.arity X))
    (θ : Formula D Γ)
    (hNoDup : xs.toList.Nodup)
    (hθFree : θ.freeVars = xs.toList.toFinset) :
    φ.FreeForRelationSubst X xs
      (θ.alphaRenameAvoiding φ.allVarList) := by
  apply freeForRelationSubst_of_bound_avoids
  · exact hNoDup
  · simpa [Formula.freeVars_alphaRenameAvoiding]
      using hθFree
  · exact Formula.alphaRenameAvoiding_isAlphaClean
      φ.allVarList θ
  · intro y hy
    exact Formula.boundVarList_alphaRenameAvoiding_avoids
      φ.allVarList θ hy

/- Replacement definitions survive alpha-renaming. -/
private theorem definesRelation_alphaRenameAvoiding
    {n : Nat}
    {Q : Set D}
    {I : Instance D Γ}
    {xs : Vector Var n}
    {θ : Formula D Γ}
    {R : FinRelation D n}
    (avoid : List Var)
    (hDef : DefinesRelation Q I xs θ R) :
    DefinesRelation Q I xs
      (θ.alphaRenameAvoiding avoid) R := by
  intro t
  constructor
  · intro ht
    rcases (hDef t).mp ht with
      ⟨σ, hReal, hSat⟩
    exact
      ⟨σ, hReal,
        (Formula.arbitraryAssignSatIn_alphaRenameAvoiding
          (Q := Q) (I := I) (σ := σ) avoid θ).mpr
          hSat⟩
  · rintro ⟨σ, hReal, hSat⟩
    exact (hDef t).mpr
      ⟨σ, hReal,
        (Formula.arbitraryAssignSatIn_alphaRenameAvoiding
          (Q := Q) (I := I) (σ := σ) avoid θ).mp
          hSat⟩

/- Relation substitution preserves free variables. -/
theorem freeVars_substRelation
    (φ : Formula D Γ)
    (X : Γ.syms)
    (xs : Vector Var (Γ.arity X))
    (θ : Formula D Γ)
    (hNoDup : xs.toList.Nodup)
    (hθFree : θ.freeVars = xs.toList.toFinset) :
    (φ.substRelation X xs θ).freeVars =
      φ.freeVars := by
  unfold substRelation
  apply freeVars_substRelationRaw
  · exact hNoDup
  · simpa [Formula.freeVars_alphaRenameAvoiding]
      using hθFree
  · exact freeForRelationSubst_alpha
      φ X xs θ hNoDup hθFree

/- Relation substitution preserves recursive truth. -/
theorem arbitraryAssignSatIn_substRelation
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    {X : Γ.syms}
    {xs : Vector Var (Γ.arity X)}
    {θ : Formula D Γ}
    {R : FinRelation D (Γ.arity X)}
    (φ : Formula D Γ)
    (hNoDup : xs.toList.Nodup)
    (hθFree : θ.freeVars = xs.toList.toFinset)
    (hDef : DefinesRelation Q I xs θ R) :
    Formula.ArbitraryAssignSatIn Q I σ
        (φ.substRelation X xs θ) ↔
      Formula.ArbitraryAssignSatIn Q
        (Instance.update I X R) σ φ := by
  unfold substRelation
  apply arbitraryAssignSatIn_substRelationRaw
  · exact hNoDup
  · simpa [Formula.freeVars_alphaRenameAvoiding]
      using hθFree
  · exact freeForRelationSubst_alpha
      φ X xs θ hNoDup hθFree
  · exact definesRelation_alphaRenameAvoiding
      φ.allVarList hDef

/- Satisfaction obeys relation substitution. -/
theorem satIn_substRelation
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    {X : Γ.syms}
    {xs : Vector Var (Γ.arity X)}
    {θ : Formula D Γ}
    {R : FinRelation D (Γ.arity X)}
    (φ : Formula D Γ)
    (hNoDup : xs.toList.Nodup)
    (hθFree : θ.freeVars = xs.toList.toFinset)
    (hDef : DefinesRelation Q I xs θ R) :
    (φ.substRelation X xs θ).SatIn I σ Q ↔
      φ.SatIn (Instance.update I X R) σ Q := by
  unfold substRelation
  apply satIn_substRelationRaw
  · exact hNoDup
  · simpa [Formula.freeVars_alphaRenameAvoiding]
      using hθFree
  · exact freeForRelationSubst_alpha
      φ X xs θ hNoDup hθFree
  · exact definesRelation_alphaRenameAvoiding
      φ.allVarList hDef

/- Adom satisfaction obeys relation substitution. -/
theorem adomSat_substRelation
    {I : Instance D Γ}
    {σ : Assign D}
    {X : Γ.syms}
    {xs : Vector Var (Γ.arity X)}
    {θ : Formula D Γ}
    {R : FinRelation D (Γ.arity X)}
    (φ : Formula D Γ)
    (hNoDup : xs.toList.Nodup)
    (hθFree : θ.freeVars = xs.toList.toFinset)
    (hDef :
      DefinesRelation
        (Adom.toSet (φ.substRelation X xs θ) I)
        I xs θ R) :
    (φ.substRelation X xs θ).AdomSat I σ ↔
      φ.SatIn (Instance.update I X R) σ
        (Adom.toSet (φ.substRelation X xs θ) I) := by
  unfold substRelation at hDef ⊢
  apply adomSat_substRelationRaw
  · exact hNoDup
  · simpa [Formula.freeVars_alphaRenameAvoiding]
      using hθFree
  · exact freeForRelationSubst_alpha
      φ X xs θ hNoDup hθFree
  · exact definesRelation_alphaRenameAvoiding
      φ.allVarList hDef

end Formula

end RelCalc
