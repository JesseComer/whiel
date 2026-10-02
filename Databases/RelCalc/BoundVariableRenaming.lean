-- Author: Jesse Comer
import Databases.RelCalc.TermSubstitution

/-
  This file defines recursive bound-variable renaming for
  relational calculus formulas.

  Key definitions include:
    * `RelCalc.Formula.alphaRenameAvoiding`
    * `RelCalc.Formula.alphaRename`
    * `RelCalc.Formula.IsAlphaClean`

  One-step alpha-conversion helpers include:
    * `RelCalc.Formula.renameForall`
    * `RelCalc.Formula.renameExists`

  Correctness is proven by:
    * `RelCalc.Formula.satIn_renameForall`
    * `RelCalc.Formula.satIn_renameExists`
    * `RelCalc.Formula.freeVars_alphaRenameAvoiding`
    * `RelCalc.Formula.alphaRenameAvoiding_isAlphaClean`
    * `RelCalc.Formula.satIn_alphaRenameAvoiding`
    * `RelCalc.Formula.alphaRename_isAlphaClean`
    * `RelCalc.Formula.satIn_alphaRename`
-/

------------------------------------------------------------
-- Recursive Alpha-Renaming
------------------------------------------------------------

namespace Assign

variable {D : Type}

/- Alpha updates agree when the new name is fresh. -/
private theorem alpha_update_agreeOn
    (σ : Assign D)
    {S : Finset Var}
    {x y : Var}
    {d : D}
    (hFresh : y ∉ S.erase x) :
    AgreeOn
      (update σ x d)
      (update (update σ y d) x d)
      S := by
  intro z hz
  by_cases hzx : z = x
  · subst hzx
    simp [update]
  · have hzErase : z ∈ S.erase x :=
      Finset.mem_erase.mpr ⟨hzx, hz⟩
    have hzy : z ≠ y := by
      intro h
      exact hFresh (by simpa [h] using hzErase)
    simp [update, hzx, hzy]

end Assign

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Bound variables in traversal order. -/
def boundVarList : Formula D Γ → List Var
| .top => []
| .bot => []
| .eq _ _ => []
| .rel _ => []
| .and φ ψ => φ.boundVarList ++ ψ.boundVarList
| .or φ ψ => φ.boundVarList ++ ψ.boundVarList
| .not φ => φ.boundVarList
| .imp φ ψ => φ.boundVarList ++ ψ.boundVarList
| .iff φ ψ => φ.boundVarList ++ ψ.boundVarList
| .forall_ x φ => x :: φ.boundVarList
| .exists_ x φ => x :: φ.boundVarList

/-
  Alpha-clean formulas have no bound-variable collisions.
-/
def IsAlphaClean
    (φ : Formula D Γ) : Prop :=
  φ.boundVarList.Nodup ∧
    ∀ x ∈ φ.boundVarList, x ∉ φ.freeVars

/- Largest variable in a list, defaulting to zero. -/
private def alphaMaxVarList : List Var → Nat
| [] => 0
| x :: xs => max x (alphaMaxVarList xs)

/- Rename the displayed universal binder. -/
def renameForall
    (x y : Var)
    (φ : Formula D Γ) :
    Formula D Γ :=
  Formula.forall_ y (φ.substTerm x (.var y))

/- Rename the displayed existential binder. -/
def renameExists
    (x y : Var)
    (φ : Formula D Γ) :
    Formula D Γ :=
  Formula.exists_ y (φ.substTerm x (.var y))

/- Recursively alpha-rename from a fresh-variable seed. -/
private def alphaRenameFrom :
    Nat → Formula D Γ → Nat × Formula D Γ
| n, .top => (n, .top)
| n, .bot => (n, .bot)
| n, .eq t u => (n, .eq t u)
| n, .rel a => (n, .rel a)
| n, .and φ ψ =>
    let rφ := alphaRenameFrom n φ
    let rψ := alphaRenameFrom rφ.1 ψ
    (rψ.1, .and rφ.2 rψ.2)
| n, .or φ ψ =>
    let rφ := alphaRenameFrom n φ
    let rψ := alphaRenameFrom rφ.1 ψ
    (rψ.1, .or rφ.2 rψ.2)
| n, .not φ =>
    let r := alphaRenameFrom n φ
    (r.1, .not r.2)
| n, .imp φ ψ =>
    let rφ := alphaRenameFrom n φ
    let rψ := alphaRenameFrom rφ.1 ψ
    (rψ.1, .imp rφ.2 rψ.2)
| n, .iff φ ψ =>
    let rφ := alphaRenameFrom n φ
    let rψ := alphaRenameFrom rφ.1 ψ
    (rψ.1, .iff rφ.2 rψ.2)
| n, .forall_ x φ =>
    let r := alphaRenameFrom n φ
    let y := r.1
    (y + 1, renameForall x y r.2)
| n, .exists_ x φ =>
    let r := alphaRenameFrom n φ
    let y := r.1
    (y + 1, renameExists x y r.2)

/- Recursively alpha-rename while avoiding variables. -/
def alphaRenameAvoiding
    (avoid : List Var)
    (φ : Formula D Γ) :
    Formula D Γ :=
  (alphaRenameFrom
    (alphaMaxVarList (avoid ++ φ.allVarList) + 1)
    φ).2

/- Recursively alpha-rename a formula. -/
def alphaRename
    (φ : Formula D Γ) :
    Formula D Γ :=
  φ.alphaRenameAvoiding []

end Formula

end RelCalc

------------------------------------------------------------
-- Freshness And Bound-Variable Helpers
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Members of `alphaMaxVarList` are bounded by it. -/
private theorem mem_alphaMaxVarList_le :
    ∀ {xs : List Var}
      {x : Var},
      x ∈ xs → x ≤ alphaMaxVarList xs
| [], _, hx =>
    by cases hx
| y :: ys, x, hx =>
    by
      have hcases : x = y ∨ x ∈ ys := by
        simpa using hx
      rcases hcases with hxy | hxTail
      · subst x
        exact le_max_left y (alphaMaxVarList ys)
      · exact le_max_of_le_right
          (mem_alphaMaxVarList_le hxTail)

/- Avoided variables are below the avoiding seed. -/
private theorem mem_avoid_lt_alphaSeed
    {avoid : List Var}
    {φ : Formula D Γ}
    {x : Var}
    (hx : x ∈ avoid) :
    x < alphaMaxVarList (avoid ++ φ.allVarList) + 1 := by
  exact Nat.lt_succ_of_le
    (mem_alphaMaxVarList_le
      (List.mem_append.mpr (Or.inl hx)))

/- Formula variables are below the avoiding seed. -/
private theorem mem_allVars_lt_alphaSeed
    {avoid : List Var}
    {φ : Formula D Γ}
    {x : Var}
    (hx : x ∈ φ.allVars) :
    x < alphaMaxVarList (avoid ++ φ.allVarList) + 1 := by
  exact Nat.lt_succ_of_le
    (mem_alphaMaxVarList_le
      (List.mem_append.mpr
        (Or.inr (φ.mem_allVarList_of_mem_allVars hx))))

/- Substitution preserves the list of bound variables. -/
private theorem boundVarList_substTerm
    (φ : Formula D Γ)
    (x : Var)
    (u : RelTerm D) :
    (φ.substTerm x u).boundVarList =
      φ.boundVarList := by
  induction φ with
  | top =>
      simp [Formula.substTerm, boundVarList]
  | bot =>
      simp [Formula.substTerm, boundVarList]
  | eq t v =>
      simp [Formula.substTerm, boundVarList]
  | rel a =>
      simp [Formula.substTerm, boundVarList]
  | and φ ψ ihφ ihψ =>
      simp [Formula.substTerm, boundVarList, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [Formula.substTerm, boundVarList, ihφ, ihψ]
  | not φ ih =>
      simp [Formula.substTerm, boundVarList, ih]
  | imp φ ψ ihφ ihψ =>
      simp [Formula.substTerm, boundVarList, ihφ, ihψ]
  | iff φ ψ ihφ ihψ =>
      simp [Formula.substTerm, boundVarList, ihφ, ihψ]
  | forall_ y φ ih =>
      by_cases hyx : y = x
      · simp [Formula.substTerm, boundVarList, hyx]
      · simp [Formula.substTerm, boundVarList, hyx, ih]
  | exists_ y φ ih =>
      by_cases hyx : y = x
      · simp [Formula.substTerm, boundVarList, hyx]
      · simp [Formula.substTerm, boundVarList, hyx, ih]

/- `allVars` is free variables plus bound variables. -/
private theorem mem_allVars_iff_free_or_bound
    {φ : Formula D Γ}
    {x : Var} :
    x ∈ φ.allVars ↔
      x ∈ φ.freeVars ∨ x ∈ φ.boundVarList := by
  induction φ with
  | top =>
      simp [allVars, freeVars, boundVarList]
  | bot =>
      simp [allVars, freeVars, boundVarList]
  | eq t u =>
      simp [allVars, freeVars, boundVarList]
  | rel a =>
      simp [allVars, freeVars, boundVarList]
  | and φ ψ ihφ ihψ =>
      simp [allVars, freeVars, boundVarList,
        ihφ, ihψ, or_left_comm, or_assoc]
  | or φ ψ ihφ ihψ =>
      simp [allVars, freeVars, boundVarList,
        ihφ, ihψ, or_left_comm, or_assoc]
  | not φ ih =>
      simp [allVars, freeVars, boundVarList, ih]
  | imp φ ψ ihφ ihψ =>
      simp [allVars, freeVars, boundVarList,
        ihφ, ihψ, or_left_comm, or_assoc]
  | iff φ ψ ihφ ihψ =>
      simp [allVars, freeVars, boundVarList,
        ihφ, ihψ, or_left_comm, or_assoc]
  | forall_ y φ ih =>
      by_cases hxy : x = y
      · subst hxy
        simp [allVars, freeVars, boundVarList]
      · simp [allVars, freeVars, boundVarList,
          ih, hxy, Finset.mem_erase]
  | exists_ y φ ih =>
      by_cases hxy : x = y
      · subst hxy
        simp [allVars, freeVars, boundVarList]
      · simp [allVars, freeVars, boundVarList,
          ih, hxy, Finset.mem_erase]

/- A variable outside `allVars` is substitution-fresh. -/
private theorem freeForTermSubst_var_of_not_mem_allVars
    (φ : Formula D Γ)
    (x y : Var)
    (hFresh : y ∉ φ.allVars) :
    φ.FreeForTermSubst x (.var y) := by
  induction φ with
  | top =>
      simp [FreeForTermSubst]
  | bot =>
      simp [FreeForTermSubst]
  | eq t u =>
      simp [FreeForTermSubst]
  | rel a =>
      simp [FreeForTermSubst]
  | and φ ψ ihφ ihψ =>
      constructor
      · exact ihφ (by
          intro hy
          exact hFresh (by simp [allVars, hy]))
      · exact ihψ (by
          intro hy
          exact hFresh (by simp [allVars, hy]))
  | or φ ψ ihφ ihψ =>
      constructor
      · exact ihφ (by
          intro hy
          exact hFresh (by simp [allVars, hy]))
      · exact ihψ (by
          intro hy
          exact hFresh (by simp [allVars, hy]))
  | not φ ih =>
      exact ih (by simpa [allVars] using hFresh)
  | imp φ ψ ihφ ihψ =>
      constructor
      · exact ihφ (by
          intro hy
          exact hFresh (by simp [allVars, hy]))
      · exact ihψ (by
          intro hy
          exact hFresh (by simp [allVars, hy]))
  | iff φ ψ ihφ ihψ =>
      constructor
      · exact ihφ (by
          intro hy
          exact hFresh (by simp [allVars, hy]))
      · exact ihψ (by
          intro hy
          exact hFresh (by simp [allVars, hy]))
  | forall_ z φ ih =>
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr
          ⟨by
            intro hzMem
            have hzy : z = y := by
              simpa only [RelTerm.vars, Finset.mem_singleton]
                using hzMem
            exact hFresh (by simp [allVars, hzy]),
          ih (by
            intro hy
            exact hFresh (by simp [allVars, hy]))⟩
  | exists_ z φ ih =>
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr
          ⟨by
            intro hzMem
            have hzy : z = y := by
              simpa only [RelTerm.vars, Finset.mem_singleton]
                using hzMem
            exact hFresh (by simp [allVars, hzy]),
          ih (by
            intro hy
            exact hFresh (by simp [allVars, hy]))⟩

/- A self-bound on `allVars` excludes the variable. -/
private theorem not_mem_freeVars_of_allVars_lt_self
    {φ : Formula D Γ}
    {x : Var}
    (hBound : ∀ z ∈ φ.allVars, z < x) :
    x ∉ φ.freeVars := by
  intro hx
  have hxAll : x ∈ φ.allVars :=
    φ.freeVars_subset_allVars hx
  exact Nat.lt_irrefl x (hBound x hxAll)

/-
  Appending separated fresh-variable ranges preserves nodup.
-/
private theorem nodup_append_of_ranges
    {xs ys : List Var}
    {m : Nat}
    (hxsN : xs.Nodup)
    (hysN : ys.Nodup)
    (hxs : ∀ x ∈ xs, x < m)
    (hys : ∀ y ∈ ys, m ≤ y) :
    (xs ++ ys).Nodup := by
  rw [List.nodup_append]
  exact
    ⟨hxsN, hysN, by
      intro x hx y hy hxy
      subst y
      exact (Nat.not_lt_of_ge (hys x hy)) (hxs x hx)⟩

/- The alpha-renaming state is monotone. -/
private theorem alphaRenameFrom_fst_ge
    (n : Nat)
    (φ : Formula D Γ) :
    n ≤ (alphaRenameFrom n φ).1 := by
  induction φ generalizing n with
  | top =>
      simp [alphaRenameFrom]
  | bot =>
      simp [alphaRenameFrom]
  | eq t u =>
      simp [alphaRenameFrom]
  | rel a =>
      simp [alphaRenameFrom]
  | and φ ψ ihφ ihψ =>
      exact le_trans (ihφ n)
        (ihψ (alphaRenameFrom n φ).1)
  | or φ ψ ihφ ihψ =>
      exact le_trans (ihφ n)
        (ihψ (alphaRenameFrom n φ).1)
  | not φ ih =>
      exact ih n
  | imp φ ψ ihφ ihψ =>
      exact le_trans (ihφ n)
        (ihψ (alphaRenameFrom n φ).1)
  | iff φ ψ ihφ ihψ =>
      exact le_trans (ihφ n)
        (ihψ (alphaRenameFrom n φ).1)
  | forall_ x φ ih =>
      exact Nat.le_succ_of_le (ih n)
  | exists_ x φ ih =>
      exact Nat.le_succ_of_le (ih n)

/- Alpha-renamed bound variables occupy a fresh range. -/
private theorem alphaRenameFrom_bound_range
    (n : Nat)
    (φ : Formula D Γ) :
    (alphaRenameFrom n φ).2.boundVarList.Nodup ∧
      ∀ x ∈ (alphaRenameFrom n φ).2.boundVarList,
        n ≤ x ∧ x < (alphaRenameFrom n φ).1 := by
  induction φ generalizing n with
  | top =>
      simp [alphaRenameFrom, boundVarList]
  | bot =>
      simp [alphaRenameFrom, boundVarList]
  | eq t u =>
      simp [alphaRenameFrom, boundVarList]
  | rel a =>
      simp [alphaRenameFrom, boundVarList]
  | and φ ψ ihφ ihψ =>
      let rφ := alphaRenameFrom n φ
      let rψ := alphaRenameFrom rφ.1 ψ
      have hφ := ihφ n
      have hψ := ihψ rφ.1
      have hN :
          (rφ.2.boundVarList ++
            rψ.2.boundVarList).Nodup :=
        nodup_append_of_ranges hφ.1 hψ.1
          (fun x hx => (hφ.2 x hx).2)
          (fun x hx => (hψ.2 x hx).1)
      constructor
      · simpa [alphaRenameFrom, boundVarList, rφ, rψ]
          using hN
      · intro x hx
        have hx' :
            x ∈ rφ.2.boundVarList ++
              rψ.2.boundVarList := by
          simpa [alphaRenameFrom, boundVarList, rφ, rψ]
            using hx
        rcases List.mem_append.mp hx' with hxφ | hxψ
        · exact
            ⟨(hφ.2 x hxφ).1,
              lt_of_lt_of_le (hφ.2 x hxφ).2
                (alphaRenameFrom_fst_ge rφ.1 ψ)⟩
        · exact
            ⟨le_trans (alphaRenameFrom_fst_ge n φ)
                (hψ.2 x hxψ).1,
              (hψ.2 x hxψ).2⟩
  | or φ ψ ihφ ihψ =>
      let rφ := alphaRenameFrom n φ
      let rψ := alphaRenameFrom rφ.1 ψ
      have hφ := ihφ n
      have hψ := ihψ rφ.1
      have hN :
          (rφ.2.boundVarList ++
            rψ.2.boundVarList).Nodup :=
        nodup_append_of_ranges hφ.1 hψ.1
          (fun x hx => (hφ.2 x hx).2)
          (fun x hx => (hψ.2 x hx).1)
      constructor
      · simpa [alphaRenameFrom, boundVarList, rφ, rψ]
          using hN
      · intro x hx
        have hx' :
            x ∈ rφ.2.boundVarList ++
              rψ.2.boundVarList := by
          simpa [alphaRenameFrom, boundVarList, rφ, rψ]
            using hx
        rcases List.mem_append.mp hx' with hxφ | hxψ
        · exact
            ⟨(hφ.2 x hxφ).1,
              lt_of_lt_of_le (hφ.2 x hxφ).2
                (alphaRenameFrom_fst_ge rφ.1 ψ)⟩
        · exact
            ⟨le_trans (alphaRenameFrom_fst_ge n φ)
                (hψ.2 x hxψ).1,
              (hψ.2 x hxψ).2⟩
  | not φ ih =>
      simpa [alphaRenameFrom, boundVarList] using ih n
  | imp φ ψ ihφ ihψ =>
      let rφ := alphaRenameFrom n φ
      let rψ := alphaRenameFrom rφ.1 ψ
      have hφ := ihφ n
      have hψ := ihψ rφ.1
      have hN :
          (rφ.2.boundVarList ++
            rψ.2.boundVarList).Nodup :=
        nodup_append_of_ranges hφ.1 hψ.1
          (fun x hx => (hφ.2 x hx).2)
          (fun x hx => (hψ.2 x hx).1)
      constructor
      · simpa [alphaRenameFrom, boundVarList, rφ, rψ]
          using hN
      · intro x hx
        have hx' :
            x ∈ rφ.2.boundVarList ++
              rψ.2.boundVarList := by
          simpa [alphaRenameFrom, boundVarList, rφ, rψ]
            using hx
        rcases List.mem_append.mp hx' with hxφ | hxψ
        · exact
            ⟨(hφ.2 x hxφ).1,
              lt_of_lt_of_le (hφ.2 x hxφ).2
                (alphaRenameFrom_fst_ge rφ.1 ψ)⟩
        · exact
            ⟨le_trans (alphaRenameFrom_fst_ge n φ)
                (hψ.2 x hxψ).1,
              (hψ.2 x hxψ).2⟩
  | iff φ ψ ihφ ihψ =>
      let rφ := alphaRenameFrom n φ
      let rψ := alphaRenameFrom rφ.1 ψ
      have hφ := ihφ n
      have hψ := ihψ rφ.1
      have hN :
          (rφ.2.boundVarList ++
            rψ.2.boundVarList).Nodup :=
        nodup_append_of_ranges hφ.1 hψ.1
          (fun x hx => (hφ.2 x hx).2)
          (fun x hx => (hψ.2 x hx).1)
      constructor
      · simpa [alphaRenameFrom, boundVarList, rφ, rψ]
          using hN
      · intro x hx
        have hx' :
            x ∈ rφ.2.boundVarList ++
              rψ.2.boundVarList := by
          simpa [alphaRenameFrom, boundVarList, rφ, rψ]
            using hx
        rcases List.mem_append.mp hx' with hxφ | hxψ
        · exact
            ⟨(hφ.2 x hxφ).1,
              lt_of_lt_of_le (hφ.2 x hxφ).2
                (alphaRenameFrom_fst_ge rφ.1 ψ)⟩
        · exact
            ⟨le_trans (alphaRenameFrom_fst_ge n φ)
                (hψ.2 x hxψ).1,
              (hψ.2 x hxψ).2⟩
  | forall_ y φ ih =>
      let r := alphaRenameFrom n φ
      have h := ih n
      have hNot : r.1 ∉ r.2.boundVarList := by
        intro hy
        exact Nat.lt_irrefl r.1 ((h.2 r.1 hy).2)
      constructor
      · simp [alphaRenameFrom, renameForall,
          boundVarList, boundVarList_substTerm,
          r, h.1, hNot]
      · intro x hx
        have hx' :
            x ∈ r.1 :: r.2.boundVarList := by
          simpa [alphaRenameFrom, renameForall,
            boundVarList, boundVarList_substTerm, r]
            using hx
        rcases List.mem_cons.mp hx' with rfl | hxBody
        · exact
            ⟨alphaRenameFrom_fst_ge n φ,
              Nat.lt_succ_self r.1⟩
        · exact
            ⟨(h.2 x hxBody).1,
              lt_trans (h.2 x hxBody).2
                (Nat.lt_succ_self r.1)⟩
  | exists_ y φ ih =>
      let r := alphaRenameFrom n φ
      have h := ih n
      have hNot : r.1 ∉ r.2.boundVarList := by
        intro hy
        exact Nat.lt_irrefl r.1 ((h.2 r.1 hy).2)
      constructor
      · simp [alphaRenameFrom, renameExists,
          boundVarList, boundVarList_substTerm,
          r, h.1, hNot]
      · intro x hx
        have hx' :
            x ∈ r.1 :: r.2.boundVarList := by
          simpa [alphaRenameFrom, renameExists,
            boundVarList, boundVarList_substTerm, r]
            using hx
        rcases List.mem_cons.mp hx' with rfl | hxBody
        · exact
            ⟨alphaRenameFrom_fst_ge n φ,
              Nat.lt_succ_self r.1⟩
        · exact
            ⟨(h.2 x hxBody).1,
              lt_trans (h.2 x hxBody).2
                (Nat.lt_succ_self r.1)⟩

end Formula

end RelCalc

------------------------------------------------------------
-- One-Step Alpha-Conversion Correctness
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Universal alpha conversion preserves free variables. -/
private theorem freeVars_renameForall
    (φ : Formula D Γ)
    (x y : Var)
    (hFree : φ.FreeForTermSubst x (.var y))
    (hFresh :
      y ∉ (Formula.forall_ x φ).freeVars) :
    (renameForall x y φ).freeVars =
      (Formula.forall_ x φ).freeVars := by
  have hSub :=
    freeVars_substTerm φ x (.var y) hFree
  have hFreshFree :
      y ≠ x → y ∉ φ.freeVars := by
    intro hyx hy
    exact hFresh
      (Finset.mem_erase.mpr ⟨hyx, hy⟩)
  ext z
  by_cases hzy : z = y
  · subst z
    have hLeft :
        y ∉ (renameForall x y φ).freeVars := by
      simp only [renameForall, freeVars,
        Finset.mem_erase, ne_eq, not_true_eq_false,
        false_and, not_false_eq_true]
    constructor
    · intro hy
      exact False.elim (hLeft hy)
    · intro hy
      exact False.elim (hFresh hy)
  · by_cases hx : x ∈ φ.freeVars
    · simp [renameForall, freeVars, hSub,
        RelTerm.vars, hzy, hx, Finset.mem_erase]
    · simp [renameForall, freeVars, hSub,
        hzy, hx, Finset.mem_erase]

/- Existential alpha conversion preserves free variables. -/
private theorem freeVars_renameExists
    (φ : Formula D Γ)
    (x y : Var)
    (hFree : φ.FreeForTermSubst x (.var y))
    (hFresh :
      y ∉ (Formula.exists_ x φ).freeVars) :
    (renameExists x y φ).freeVars =
      (Formula.exists_ x φ).freeVars := by
  have hSub :=
    freeVars_substTerm φ x (.var y) hFree
  have hFreshFree :
      y ≠ x → y ∉ φ.freeVars := by
    intro hyx hy
    exact hFresh
      (Finset.mem_erase.mpr ⟨hyx, hy⟩)
  ext z
  by_cases hzy : z = y
  · subst z
    have hLeft :
        y ∉ (renameExists x y φ).freeVars := by
      simp only [renameExists, freeVars,
        Finset.mem_erase, ne_eq, not_true_eq_false,
        false_and, not_false_eq_true]
    constructor
    · intro hy
      exact False.elim (hLeft hy)
    · intro hy
      exact False.elim (hFresh hy)
  · by_cases hx : x ∈ φ.freeVars
    · simp [renameExists, freeVars, hSub,
        RelTerm.vars, hzy, hx, Finset.mem_erase]
    · simp [renameExists, freeVars, hSub,
        hzy, hx, Finset.mem_erase]

/- Universal alpha conversion preserves recursive truth. -/
private theorem arbitraryAssignSatIn_renameForall
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    (φ : Formula D Γ)
    (x y : Var)
    (hFree : φ.FreeForTermSubst x (.var y))
    (hFresh :
      y ∉ (Formula.forall_ x φ).freeVars) :
    Formula.ArbitraryAssignSatIn Q I σ
        (Formula.forall_ x φ) ↔
      Formula.ArbitraryAssignSatIn Q I σ
        (renameForall x y φ) := by
  constructor
  · intro hSat d hd
    have hSimple :
        Formula.ArbitraryAssignSatIn Q I
          (Assign.update σ x d) φ :=
      hSat d hd
    have hAgree :
        Assign.AgreeOn
          (Assign.update σ x d)
          (Assign.update
            (Assign.update σ y d) x d)
          φ.freeVars :=
      Assign.alpha_update_agreeOn
        (σ := σ) (S := φ.freeVars)
        (x := x) (y := y) (d := d)
        hFresh
    have hMoved :
        Formula.ArbitraryAssignSatIn Q I
          (Assign.update
            (Assign.update σ y d) x d) φ :=
      (holdsIn_eq_of_agreeOn_freeVars
        (Q := Q) (I := I)
        (φ := φ) hAgree).mp hSimple
    have hSub :
        Formula.ArbitraryAssignSatIn Q I
          (Assign.update σ y d)
          (φ.substTerm x (.var y)) :=
      (arbitraryAssignSatIn_substTerm
        (Q := Q) (I := I)
        (σ := Assign.update σ y d)
        φ x (.var y) hFree).mpr
        (by simpa [RelTerm.eval, Assign.update] using hMoved)
    simpa [renameForall,
      Formula.ArbitraryAssignSatIn] using hSub
  · intro hSat d hd
    have hSub :
        Formula.ArbitraryAssignSatIn Q I
          (Assign.update σ y d)
          (φ.substTerm x (.var y)) :=
      hSat d hd
    have hMovedRaw :
        Formula.ArbitraryAssignSatIn Q I
          (Assign.update
            (Assign.update σ y d) x
            ((RelTerm.var y).eval
              (Assign.update σ y d))) φ :=
      (arbitraryAssignSatIn_substTerm
        (Q := Q) (I := I)
        (σ := Assign.update σ y d)
        φ x (.var y) hFree).mp hSub
    have hMoved :
        Formula.ArbitraryAssignSatIn Q I
          (Assign.update
            (Assign.update σ y d) x d) φ := by
      simpa [RelTerm.eval, Assign.update] using hMovedRaw
    have hAgree :
        Assign.AgreeOn
          (Assign.update σ x d)
          (Assign.update
            (Assign.update σ y d) x d)
          φ.freeVars :=
      Assign.alpha_update_agreeOn
        (σ := σ) (S := φ.freeVars)
        (x := x) (y := y) (d := d)
        hFresh
    exact
      (holdsIn_eq_of_agreeOn_freeVars
        (Q := Q) (I := I)
        (φ := φ) hAgree).mpr hMoved

/- Existential alpha preserves recursive truth. -/
private theorem arbitraryAssignSatIn_renameExists
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    (φ : Formula D Γ)
    (x y : Var)
    (hFree : φ.FreeForTermSubst x (.var y))
    (hFresh :
      y ∉ (Formula.exists_ x φ).freeVars) :
    Formula.ArbitraryAssignSatIn Q I σ
        (Formula.exists_ x φ) ↔
      Formula.ArbitraryAssignSatIn Q I σ
        (renameExists x y φ) := by
  constructor
  · rintro ⟨d, hd, hSimple⟩
    refine ⟨d, hd, ?_⟩
    have hAgree :
        Assign.AgreeOn
          (Assign.update σ x d)
          (Assign.update
            (Assign.update σ y d) x d)
          φ.freeVars :=
      Assign.alpha_update_agreeOn
        (σ := σ) (S := φ.freeVars)
        (x := x) (y := y) (d := d)
        hFresh
    have hMoved :
        Formula.ArbitraryAssignSatIn Q I
          (Assign.update
            (Assign.update σ y d) x d) φ :=
      (holdsIn_eq_of_agreeOn_freeVars
        (Q := Q) (I := I)
        (φ := φ) hAgree).mp hSimple
    have hSub :
        Formula.ArbitraryAssignSatIn Q I
          (Assign.update σ y d)
          (φ.substTerm x (.var y)) :=
      (arbitraryAssignSatIn_substTerm
        (Q := Q) (I := I)
        (σ := Assign.update σ y d)
        φ x (.var y) hFree).mpr
        (by simpa [RelTerm.eval, Assign.update] using hMoved)
    simpa [renameExists,
      Formula.ArbitraryAssignSatIn] using hSub
  · rintro ⟨d, hd, hSub⟩
    refine ⟨d, hd, ?_⟩
    have hMovedRaw :
        Formula.ArbitraryAssignSatIn Q I
          (Assign.update
            (Assign.update σ y d) x
            ((RelTerm.var y).eval
              (Assign.update σ y d))) φ :=
      (arbitraryAssignSatIn_substTerm
        (Q := Q) (I := I)
        (σ := Assign.update σ y d)
        φ x (.var y) hFree).mp hSub
    have hMoved :
        Formula.ArbitraryAssignSatIn Q I
          (Assign.update
            (Assign.update σ y d) x d) φ := by
      simpa [RelTerm.eval, Assign.update] using hMovedRaw
    have hAgree :
        Assign.AgreeOn
          (Assign.update σ x d)
          (Assign.update
            (Assign.update σ y d) x d)
          φ.freeVars :=
      Assign.alpha_update_agreeOn
        (σ := σ) (S := φ.freeVars)
        (x := x) (y := y) (d := d)
        hFresh
    exact
      (holdsIn_eq_of_agreeOn_freeVars
        (Q := Q) (I := I)
        (φ := φ) hAgree).mpr hMoved

/- Universal alpha conversion preserves public truth. -/
theorem satIn_renameForall
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    (φ : Formula D Γ)
    (x y : Var)
    (hFree : φ.FreeForTermSubst x (.var y))
    (hFresh :
      y ∉ (Formula.forall_ x φ).freeVars) :
    (Formula.forall_ x φ).SatIn I σ Q ↔
      (renameForall x y φ).SatIn I σ Q := by
  have hVars :=
    freeVars_renameForall φ x y hFree hFresh
  have hRaw :=
    arbitraryAssignSatIn_renameForall
      (Q := Q) (I := I) (σ := σ)
      φ x y hFree hFresh
  constructor
  · rintro ⟨hMaps, hSat⟩
    exact ⟨by simpa [hVars] using hMaps,
      hRaw.mp hSat⟩
  · rintro ⟨hMaps, hSat⟩
    exact ⟨by simpa [hVars] using hMaps,
      hRaw.mpr hSat⟩

/- Existential alpha conversion preserves public truth. -/
theorem satIn_renameExists
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    (φ : Formula D Γ)
    (x y : Var)
    (hFree : φ.FreeForTermSubst x (.var y))
    (hFresh :
      y ∉ (Formula.exists_ x φ).freeVars) :
    (Formula.exists_ x φ).SatIn I σ Q ↔
      (renameExists x y φ).SatIn I σ Q := by
  have hVars :=
    freeVars_renameExists φ x y hFree hFresh
  have hRaw :=
    arbitraryAssignSatIn_renameExists
      (Q := Q) (I := I) (σ := σ)
      φ x y hFree hFresh
  constructor
  · rintro ⟨hMaps, hSat⟩
    exact ⟨by simpa [hVars] using hMaps,
      hRaw.mp hSat⟩
  · rintro ⟨hMaps, hSat⟩
    exact ⟨by simpa [hVars] using hMaps,
      hRaw.mpr hSat⟩

end Formula

end RelCalc

------------------------------------------------------------
-- Recursive Alpha-Renaming Correctness
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Bound free and bound variables imply an `allVars` bound.
-/
private theorem allVars_lt_of_free_and_bound
    {φ : Formula D Γ}
    {n : Nat}
    (hFree : ∀ x ∈ φ.freeVars, x < n)
    (hBound : ∀ x ∈ φ.boundVarList, x < n) :
    ∀ x ∈ φ.allVars, x < n := by
  intro x hx
  rcases
      (mem_allVars_iff_free_or_bound
        (φ := φ) (x := x)).mp hx with hxFree | hxBound
  · exact hFree x hxFree
  · exact hBound x hxBound

/- Recursive alpha-renaming preserves free variables. -/
private theorem alphaRenameFrom_freeVars
    (n : Nat)
    (φ : Formula D Γ)
    (hAll : ∀ x ∈ φ.allVars, x < n) :
    (alphaRenameFrom n φ).2.freeVars =
      φ.freeVars := by
  induction φ generalizing n with
  | top =>
      simp [alphaRenameFrom, freeVars]
  | bot =>
      simp [alphaRenameFrom, freeVars]
  | eq t u =>
      simp [alphaRenameFrom, freeVars]
  | rel a =>
      simp [alphaRenameFrom, freeVars]
  | and φ ψ ihφ ihψ =>
      let rφ := alphaRenameFrom n φ
      have hφAll : ∀ x ∈ φ.allVars, x < n := by
        intro x hx
        exact hAll x (by simp [allVars, hx])
      have hψAll : ∀ x ∈ ψ.allVars, x < rφ.1 := by
        intro x hx
        exact lt_of_lt_of_le
          (hAll x (by simp [allVars, hx]))
          (alphaRenameFrom_fst_ge n φ)
      have hφ := ihφ n hφAll
      have hψ := ihψ rφ.1 hψAll
      simp [alphaRenameFrom, freeVars, rφ, hφ, hψ]
  | or φ ψ ihφ ihψ =>
      let rφ := alphaRenameFrom n φ
      have hφAll : ∀ x ∈ φ.allVars, x < n := by
        intro x hx
        exact hAll x (by simp [allVars, hx])
      have hψAll : ∀ x ∈ ψ.allVars, x < rφ.1 := by
        intro x hx
        exact lt_of_lt_of_le
          (hAll x (by simp [allVars, hx]))
          (alphaRenameFrom_fst_ge n φ)
      have hφ := ihφ n hφAll
      have hψ := ihψ rφ.1 hψAll
      simp [alphaRenameFrom, freeVars, rφ, hφ, hψ]
  | not φ ih =>
      have hφAll : ∀ x ∈ φ.allVars, x < n := by
        intro x hx
        exact hAll x (by simpa [allVars] using hx)
      simp [alphaRenameFrom, freeVars, ih n hφAll]
  | imp φ ψ ihφ ihψ =>
      let rφ := alphaRenameFrom n φ
      have hφAll : ∀ x ∈ φ.allVars, x < n := by
        intro x hx
        exact hAll x (by simp [allVars, hx])
      have hψAll : ∀ x ∈ ψ.allVars, x < rφ.1 := by
        intro x hx
        exact lt_of_lt_of_le
          (hAll x (by simp [allVars, hx]))
          (alphaRenameFrom_fst_ge n φ)
      have hφ := ihφ n hφAll
      have hψ := ihψ rφ.1 hψAll
      simp [alphaRenameFrom, freeVars, rφ, hφ, hψ]
  | iff φ ψ ihφ ihψ =>
      let rφ := alphaRenameFrom n φ
      have hφAll : ∀ x ∈ φ.allVars, x < n := by
        intro x hx
        exact hAll x (by simp [allVars, hx])
      have hψAll : ∀ x ∈ ψ.allVars, x < rφ.1 := by
        intro x hx
        exact lt_of_lt_of_le
          (hAll x (by simp [allVars, hx]))
          (alphaRenameFrom_fst_ge n φ)
      have hφ := ihφ n hφAll
      have hψ := ihψ rφ.1 hψAll
      simp [alphaRenameFrom, freeVars, rφ, hφ, hψ]
  | forall_ x φ ih =>
      let r := alphaRenameFrom n φ
      have hφAll : ∀ z ∈ φ.allVars, z < n := by
        intro z hz
        exact hAll z (by simp [allVars, hz])
      have hFree := ih n hφAll
      have hRange := alphaRenameFrom_bound_range n φ
      have hRenamedAll :
          ∀ z ∈ r.2.allVars, z < r.1 := by
        apply allVars_lt_of_free_and_bound
        · intro z hz
          have hzOrig : z ∈ φ.freeVars := by
            simpa [r, hFree] using hz
          exact lt_of_lt_of_le
            (hφAll z (φ.freeVars_subset_allVars hzOrig))
            (alphaRenameFrom_fst_ge n φ)
        · intro z hz
          exact (hRange.2 z (by simpa [r] using hz)).2
      have hNotAll : r.1 ∉ r.2.allVars := by
        intro hr
        exact Nat.lt_irrefl r.1 (hRenamedAll r.1 hr)
      have hSubFresh :
          r.2.FreeForTermSubst x (.var r.1) :=
        freeForTermSubst_var_of_not_mem_allVars
          r.2 x r.1 hNotAll
      have hFresh :
          r.1 ∉ (Formula.forall_ x r.2).freeVars := by
        intro hr
        exact not_mem_freeVars_of_allVars_lt_self
          hRenamedAll ((Finset.mem_erase.mp hr).2)
      have hRename :=
        freeVars_renameForall r.2 x r.1
          hSubFresh hFresh
      calc
        (alphaRenameFrom n
            (Formula.forall_ x φ)).2.freeVars
            = (renameForall x r.1 r.2).freeVars := by
                simp [alphaRenameFrom, r]
        _ = (Formula.forall_ x r.2).freeVars := hRename
        _ = (Formula.forall_ x φ).freeVars := by
              simp [freeVars, r, hFree]
  | exists_ x φ ih =>
      let r := alphaRenameFrom n φ
      have hφAll : ∀ z ∈ φ.allVars, z < n := by
        intro z hz
        exact hAll z (by simp [allVars, hz])
      have hFree := ih n hφAll
      have hRange := alphaRenameFrom_bound_range n φ
      have hRenamedAll :
          ∀ z ∈ r.2.allVars, z < r.1 := by
        apply allVars_lt_of_free_and_bound
        · intro z hz
          have hzOrig : z ∈ φ.freeVars := by
            simpa [r, hFree] using hz
          exact lt_of_lt_of_le
            (hφAll z (φ.freeVars_subset_allVars hzOrig))
            (alphaRenameFrom_fst_ge n φ)
        · intro z hz
          exact (hRange.2 z (by simpa [r] using hz)).2
      have hNotAll : r.1 ∉ r.2.allVars := by
        intro hr
        exact Nat.lt_irrefl r.1 (hRenamedAll r.1 hr)
      have hSubFresh :
          r.2.FreeForTermSubst x (.var r.1) :=
        freeForTermSubst_var_of_not_mem_allVars
          r.2 x r.1 hNotAll
      have hFresh :
          r.1 ∉ (Formula.exists_ x r.2).freeVars := by
        intro hr
        exact not_mem_freeVars_of_allVars_lt_self
          hRenamedAll ((Finset.mem_erase.mp hr).2)
      have hRename :=
        freeVars_renameExists r.2 x r.1
          hSubFresh hFresh
      calc
        (alphaRenameFrom n
            (Formula.exists_ x φ)).2.freeVars
            = (renameExists x r.1 r.2).freeVars := by
                simp [alphaRenameFrom, r]
        _ = (Formula.exists_ x r.2).freeVars := hRename
        _ = (Formula.exists_ x φ).freeVars := by
              simp [freeVars, r, hFree]

/-
  Recursive alpha-renaming bounds all generated variables.
-/
private theorem alphaRenameFrom_allVars_lt
    (n : Nat)
    (φ : Formula D Γ)
    (hAll : ∀ x ∈ φ.allVars, x < n) :
    ∀ x ∈ (alphaRenameFrom n φ).2.allVars,
      x < (alphaRenameFrom n φ).1 := by
  apply allVars_lt_of_free_and_bound
  · intro x hx
    have hFree :=
      alphaRenameFrom_freeVars n φ hAll
    have hxOrig : x ∈ φ.freeVars := by
      simpa [hFree] using hx
    exact lt_of_lt_of_le
      (hAll x (φ.freeVars_subset_allVars hxOrig))
      (alphaRenameFrom_fst_ge n φ)
  · intro x hx
    exact (alphaRenameFrom_bound_range n φ).2 x hx |>.2

/- Recursive alpha-renaming preserves recursive truth. -/
private theorem alphaRenameFrom_arbitraryAssignSatIn
    {Q : Set D}
    {I : Instance D Γ}
    (σ : Assign D)
    (n : Nat)
    (φ : Formula D Γ)
    (hAll : ∀ x ∈ φ.allVars, x < n) :
    Formula.ArbitraryAssignSatIn Q I σ
        (alphaRenameFrom n φ).2 ↔
      Formula.ArbitraryAssignSatIn Q I σ φ := by
  induction φ generalizing n σ with
  | top =>
      simp [alphaRenameFrom,
        Formula.ArbitraryAssignSatIn]
  | bot =>
      simp [alphaRenameFrom,
        Formula.ArbitraryAssignSatIn]
  | eq t u =>
      simp [alphaRenameFrom,
        Formula.ArbitraryAssignSatIn]
  | rel a =>
      simp [alphaRenameFrom,
        Formula.ArbitraryAssignSatIn]
  | and φ ψ ihφ ihψ =>
      let rφ := alphaRenameFrom n φ
      have hφAll : ∀ x ∈ φ.allVars, x < n := by
        intro x hx
        exact hAll x (by simp [allVars, hx])
      have hψAll : ∀ x ∈ ψ.allVars, x < rφ.1 := by
        intro x hx
        exact lt_of_lt_of_le
          (hAll x (by simp [allVars, hx]))
          (alphaRenameFrom_fst_ge n φ)
      have hφ := ihφ σ n hφAll
      have hψ := ihψ σ rφ.1 hψAll
      simp [alphaRenameFrom, Formula.ArbitraryAssignSatIn,
        rφ, hφ, hψ]
  | or φ ψ ihφ ihψ =>
      let rφ := alphaRenameFrom n φ
      have hφAll : ∀ x ∈ φ.allVars, x < n := by
        intro x hx
        exact hAll x (by simp [allVars, hx])
      have hψAll : ∀ x ∈ ψ.allVars, x < rφ.1 := by
        intro x hx
        exact lt_of_lt_of_le
          (hAll x (by simp [allVars, hx]))
          (alphaRenameFrom_fst_ge n φ)
      have hφ := ihφ σ n hφAll
      have hψ := ihψ σ rφ.1 hψAll
      simp [alphaRenameFrom, Formula.ArbitraryAssignSatIn,
        rφ, hφ, hψ]
  | not φ ih =>
      have hφAll : ∀ x ∈ φ.allVars, x < n := by
        intro x hx
        exact hAll x (by simpa [allVars] using hx)
      have hφ := ih σ n hφAll
      simp [alphaRenameFrom, Formula.ArbitraryAssignSatIn,
        hφ]
  | imp φ ψ ihφ ihψ =>
      let rφ := alphaRenameFrom n φ
      have hφAll : ∀ x ∈ φ.allVars, x < n := by
        intro x hx
        exact hAll x (by simp [allVars, hx])
      have hψAll : ∀ x ∈ ψ.allVars, x < rφ.1 := by
        intro x hx
        exact lt_of_lt_of_le
          (hAll x (by simp [allVars, hx]))
          (alphaRenameFrom_fst_ge n φ)
      have hφ := ihφ σ n hφAll
      have hψ := ihψ σ rφ.1 hψAll
      simp [alphaRenameFrom, Formula.ArbitraryAssignSatIn,
        rφ, hφ, hψ]
  | iff φ ψ ihφ ihψ =>
      let rφ := alphaRenameFrom n φ
      have hφAll : ∀ x ∈ φ.allVars, x < n := by
        intro x hx
        exact hAll x (by simp [allVars, hx])
      have hψAll : ∀ x ∈ ψ.allVars, x < rφ.1 := by
        intro x hx
        exact lt_of_lt_of_le
          (hAll x (by simp [allVars, hx]))
          (alphaRenameFrom_fst_ge n φ)
      have hφ := ihφ σ n hφAll
      have hψ := ihψ σ rφ.1 hψAll
      simp [alphaRenameFrom, Formula.ArbitraryAssignSatIn,
        rφ, hφ, hψ]
  | forall_ x φ ih =>
      let r := alphaRenameFrom n φ
      have hφAll : ∀ z ∈ φ.allVars, z < n := by
        intro z hz
        exact hAll z (by simp [allVars, hz])
      have hRenamedAll :
          ∀ z ∈ r.2.allVars, z < r.1 := by
        simpa [r] using
          alphaRenameFrom_allVars_lt n φ hφAll
      have hNotAll : r.1 ∉ r.2.allVars := by
        intro hr
        exact Nat.lt_irrefl r.1 (hRenamedAll r.1 hr)
      have hSubFresh :
          r.2.FreeForTermSubst x (.var r.1) :=
        freeForTermSubst_var_of_not_mem_allVars
          r.2 x r.1 hNotAll
      have hFresh :
          r.1 ∉ (Formula.forall_ x r.2).freeVars := by
        intro hr
        exact not_mem_freeVars_of_allVars_lt_self
          hRenamedAll ((Finset.mem_erase.mp hr).2)
      have hRename :=
        arbitraryAssignSatIn_renameForall
          (Q := Q) (I := I) (σ := σ)
          r.2 x r.1 hSubFresh hFresh
      constructor
      · intro hRenamed
        have hForallR : Formula.ArbitraryAssignSatIn Q I σ
            (Formula.forall_ x r.2) :=
          hRename.mpr (by
            simpa [alphaRenameFrom, r] using hRenamed)
        intro d hd
        exact
          (ih (Assign.update σ x d) n hφAll).mp
            (hForallR d hd)
      · intro hOrig
        have hForallR : Formula.ArbitraryAssignSatIn Q I σ
            (Formula.forall_ x r.2) := by
          intro d hd
          exact
            (ih (Assign.update σ x d) n hφAll).mpr
              (hOrig d hd)
        simpa [alphaRenameFrom, r] using
          hRename.mp hForallR
  | exists_ x φ ih =>
      let r := alphaRenameFrom n φ
      have hφAll : ∀ z ∈ φ.allVars, z < n := by
        intro z hz
        exact hAll z (by simp [allVars, hz])
      have hRenamedAll :
          ∀ z ∈ r.2.allVars, z < r.1 := by
        simpa [r] using
          alphaRenameFrom_allVars_lt n φ hφAll
      have hNotAll : r.1 ∉ r.2.allVars := by
        intro hr
        exact Nat.lt_irrefl r.1 (hRenamedAll r.1 hr)
      have hSubFresh :
          r.2.FreeForTermSubst x (.var r.1) :=
        freeForTermSubst_var_of_not_mem_allVars
          r.2 x r.1 hNotAll
      have hFresh :
          r.1 ∉ (Formula.exists_ x r.2).freeVars := by
        intro hr
        exact not_mem_freeVars_of_allVars_lt_self
          hRenamedAll ((Finset.mem_erase.mp hr).2)
      have hRename :=
        arbitraryAssignSatIn_renameExists
          (Q := Q) (I := I) (σ := σ)
          r.2 x r.1 hSubFresh hFresh
      constructor
      · intro hRenamed
        have hExistsR : Formula.ArbitraryAssignSatIn Q I σ
            (Formula.exists_ x r.2) :=
          hRename.mpr (by
            simpa [alphaRenameFrom, r] using hRenamed)
        rcases hExistsR with ⟨d, hd, hBody⟩
        exact
          ⟨d, hd,
            (ih (Assign.update σ x d) n hφAll).mp
              hBody⟩
      · rintro ⟨d, hd, hBody⟩
        have hExistsR : Formula.ArbitraryAssignSatIn Q I σ
            (Formula.exists_ x r.2) :=
          ⟨d, hd,
            (ih (Assign.update σ x d) n hφAll).mpr
              hBody⟩
        simpa [alphaRenameFrom, r] using
          hRename.mp hExistsR

/- Avoiding alpha-renaming preserves free variables. -/
theorem freeVars_alphaRenameAvoiding
    (avoid : List Var)
    (φ : Formula D Γ) :
    (φ.alphaRenameAvoiding avoid).freeVars =
      φ.freeVars := by
  unfold alphaRenameAvoiding
  exact alphaRenameFrom_freeVars
    (alphaMaxVarList (avoid ++ φ.allVarList) + 1)
    φ
    (fun x hx => mem_allVars_lt_alphaSeed hx)

/-
  Avoiding alpha-renaming produces an alpha-clean formula.
-/
theorem alphaRenameAvoiding_isAlphaClean
    (avoid : List Var)
    (φ : Formula D Γ) :
    (φ.alphaRenameAvoiding avoid).IsAlphaClean := by
  unfold alphaRenameAvoiding IsAlphaClean
  let n := alphaMaxVarList (avoid ++ φ.allVarList) + 1
  have hAll : ∀ x ∈ φ.allVars, x < n := by
    intro x hx
    exact mem_allVars_lt_alphaSeed hx
  have hRange := alphaRenameFrom_bound_range n φ
  have hFree := alphaRenameFrom_freeVars n φ hAll
  constructor
  · exact hRange.1
  · intro x hxBound hxFree
    have hxOrig : x ∈ φ.freeVars := by
      simpa [n, hFree] using hxFree
    have hxLt : x < n :=
      hAll x (φ.freeVars_subset_allVars hxOrig)
    exact
      (Nat.not_lt_of_ge (hRange.2 x hxBound).1) hxLt

/- Avoiding alpha-renaming avoids the supplied variables. -/
theorem boundVarList_alphaRenameAvoiding_avoids
    (avoid : List Var)
    (φ : Formula D Γ)
    {x : Var}
    (hx :
      x ∈ (φ.alphaRenameAvoiding avoid).boundVarList) :
    x ∉ avoid := by
  unfold alphaRenameAvoiding at hx
  let n := alphaMaxVarList (avoid ++ φ.allVarList) + 1
  have hRange := alphaRenameFrom_bound_range n φ
  have hxGe : n ≤ x :=
    (hRange.2 x hx).1
  intro hAvoid
  have hxLt : x < n :=
    mem_avoid_lt_alphaSeed hAvoid
  exact Nat.not_lt_of_ge hxGe hxLt

/- Avoiding alpha-renaming preserves recursive truth. -/
theorem arbitraryAssignSatIn_alphaRenameAvoiding
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    (avoid : List Var)
    (φ : Formula D Γ) :
    Formula.ArbitraryAssignSatIn Q I σ
        (φ.alphaRenameAvoiding avoid) ↔
      Formula.ArbitraryAssignSatIn Q I σ φ := by
  unfold alphaRenameAvoiding
  let n := alphaMaxVarList (avoid ++ φ.allVarList) + 1
  have hAll : ∀ x ∈ φ.allVars, x < n := by
    intro x hx
    exact mem_allVars_lt_alphaSeed hx
  exact alphaRenameFrom_arbitraryAssignSatIn
    (Q := Q) (I := I) σ n φ hAll

/- Avoiding alpha-renaming preserves satisfaction. -/
theorem satIn_alphaRenameAvoiding
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    (avoid : List Var)
    (φ : Formula D Γ) :
    (φ.alphaRenameAvoiding avoid).SatIn I σ Q ↔
      φ.SatIn I σ Q := by
  have hFree := freeVars_alphaRenameAvoiding avoid φ
  have hRaw :=
    arbitraryAssignSatIn_alphaRenameAvoiding
      (Q := Q) (I := I) (σ := σ) avoid φ
  constructor
  · rintro ⟨hMaps, hSat⟩
    exact
      ⟨by simpa [hFree] using hMaps,
        hRaw.mp hSat⟩
  · rintro ⟨hMaps, hSat⟩
    exact
      ⟨by simpa [hFree] using hMaps,
        hRaw.mpr hSat⟩

/- Recursive alpha-renaming preserves free variables. -/
theorem freeVars_alphaRename
    (φ : Formula D Γ) :
    φ.alphaRename.freeVars = φ.freeVars :=
  freeVars_alphaRenameAvoiding [] φ

/-
  Recursive alpha-renaming produces an alpha-clean formula.
-/
theorem alphaRename_isAlphaClean
    (φ : Formula D Γ) :
    φ.alphaRename.IsAlphaClean :=
  alphaRenameAvoiding_isAlphaClean [] φ

/- Recursive alpha-renaming preserves satisfaction. -/
theorem satIn_alphaRename
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    (φ : Formula D Γ) :
    φ.alphaRename.SatIn I σ Q ↔
      φ.SatIn I σ Q :=
  satIn_alphaRenameAvoiding [] φ

end Formula

end RelCalc
