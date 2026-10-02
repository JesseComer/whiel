-- Author: Jesse Comer
import Whiel.Cmd.Rewrites
import Whiel.Preprocess.Framed

/-
  The final clean of the generic Whiel preprocessor.

  Normalization ends by applying the repository's existing
  skip-removal, `Cmd.clean`, to the prefix, the body and the
  suffix of the framed loop the recursion returns. The
  operations place their sub-results' components verbatim,
  and a sub-result built from loop-free code contributes
  `skip` prefixes, `skip` bodies and `skip` suffixes, so
  those components carry sequencing `skip`s that mean
  nothing.

  What the construction asks of `Cmd.clean` is only that it
  change no run, preserve the assigned relations, and add no
  relation and no loop. It does more --- it right-associates
  the sequences it rebuilds and cleans the expressions and
  guards inside them --- and that is why the symbol
  statement below is an inclusion rather than an equality:
  cleaning a vacuous union or product deletes a factor, and
  with it the relations only that factor read.

  The clean removes only sequencing `skip`s. A `skip` that
  is a branch of a conditional stays, and must: the guarded
  product body says that a component whose guard is false
  stutters for this iteration, and a hoist's suffix `skip`
  says that one branch has nothing to close.

  Key definitions include:
    * `Whiel.Preprocess.Framed.clean`

  The main lemmas are:
    * `Whiel.Preprocess.symbols_clean_subset`
    * `Whiel.Preprocess.loopFree_clean`
    * `Whiel.Preprocess.Framed.bigStepEquiv_clean`
    * `Whiel.Preprocess.Framed.loopFreeParts_clean`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Cleaning Adds No Relation Symbol
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Merging one selection reads exactly what its argument
  reads: the merge either conjoins two selection conditions,
  which are not relations, or rebuilds the selection.
-/
theorem rawSymbols_mergeSelections_select
    (s : Sel D)
    (e : RawRAExpr A D) :
    (RawRAExpr.mergeSelections
        (.select s e : RawRAExpr A D)).symbols =
      e.mergeSelections.symbols := by
  rw [RawRAExpr.mergeSelections]
  cases h : e.mergeSelections with
  | top => rfl
  | empty n => rfl
  | rel X => rfl
  | single d => rfl
  | select t f => rfl
  | proj idxs f => rfl
  | prod f g => rfl
  | union f g => rfl
  | diff f g => rfl

/- Merging selections reads no new relation. -/
theorem rawSymbols_mergeSelections_subset
    (e : RawRAExpr A D) :
    e.mergeSelections.symbols ⊆ e.symbols := by
  induction e with
  | top => simp [RawRAExpr.mergeSelections]
  | empty n => simp [RawRAExpr.mergeSelections]
  | rel X => simp [RawRAExpr.mergeSelections]
  | single d => simp [RawRAExpr.mergeSelections]
  | select s e ih =>
      rw [rawSymbols_mergeSelections_select s e]
      simpa [RawRAExpr.symbols] using ih
  | proj idxs e ih =>
      simpa [RawRAExpr.mergeSelections,
        RawRAExpr.symbols] using ih
  | prod e₁ e₂ ih₁ ih₂ =>
      simp only [RawRAExpr.mergeSelections,
        RawRAExpr.symbols]
      exact Finset.union_subset_union ih₁ ih₂
  | union e₁ e₂ ih₁ ih₂ =>
      simp only [RawRAExpr.mergeSelections,
        RawRAExpr.symbols]
      exact Finset.union_subset_union ih₁ ih₂
  | diff e₁ e₂ ih₁ ih₂ =>
      simp only [RawRAExpr.mergeSelections,
        RawRAExpr.symbols]
      exact Finset.union_subset_union ih₁ ih₂

/- Product cleanup reads no new relation. -/
theorem rawSymbols_cleanVacuousProducts_subset
    (e : RawRAExpr A D) :
    e.cleanVacuousProducts.symbols ⊆ e.symbols := by
  induction e with
  | top => simp [RawRAExpr.cleanVacuousProducts]
  | empty n => simp [RawRAExpr.cleanVacuousProducts]
  | rel X => simp [RawRAExpr.cleanVacuousProducts]
  | single d => simp [RawRAExpr.cleanVacuousProducts]
  | select s e ih =>
      simpa [RawRAExpr.cleanVacuousProducts,
        RawRAExpr.symbols] using ih
  | proj idxs e ih =>
      simpa [RawRAExpr.cleanVacuousProducts,
        RawRAExpr.symbols] using ih
  | prod e₁ e₂ ih₁ ih₂ =>
      rw [RawRAExpr.cleanVacuousProducts]
      have hLeft :
          e₁.cleanVacuousProducts.symbols ⊆
            (RawRAExpr.prod e₁ e₂).symbols := by
        simp only [RawRAExpr.symbols]
        exact subset_trans ih₁ Finset.subset_union_left
      have hBoth :
          (RawRAExpr.prod e₁.cleanVacuousProducts
              e₂.cleanVacuousProducts).symbols ⊆
            (RawRAExpr.prod e₁ e₂).symbols := by
        simp only [RawRAExpr.symbols]
        exact Finset.union_subset_union ih₁ ih₂
      split
      · exact hLeft
      · exact hBoth
  | union e₁ e₂ ih₁ ih₂ =>
      simp only [RawRAExpr.cleanVacuousProducts,
        RawRAExpr.symbols]
      exact Finset.union_subset_union ih₁ ih₂
  | diff e₁ e₂ ih₁ ih₂ =>
      simp only [RawRAExpr.cleanVacuousProducts,
        RawRAExpr.symbols]
      exact Finset.union_subset_union ih₁ ih₂

/- Union cleanup reads no new relation. -/
theorem rawSymbols_cleanVacuousUnions_subset
    (e : RawRAExpr A D) :
    e.cleanVacuousUnions.symbols ⊆ e.symbols := by
  induction e with
  | top => simp [RawRAExpr.cleanVacuousUnions]
  | empty n => simp [RawRAExpr.cleanVacuousUnions]
  | rel X => simp [RawRAExpr.cleanVacuousUnions]
  | single d => simp [RawRAExpr.cleanVacuousUnions]
  | select s e ih =>
      simpa [RawRAExpr.cleanVacuousUnions,
        RawRAExpr.symbols] using ih
  | proj idxs e ih =>
      simpa [RawRAExpr.cleanVacuousUnions,
        RawRAExpr.symbols] using ih
  | prod e₁ e₂ ih₁ ih₂ =>
      simp only [RawRAExpr.cleanVacuousUnions,
        RawRAExpr.symbols]
      exact Finset.union_subset_union ih₁ ih₂
  | union e₁ e₂ ih₁ ih₂ =>
      rw [RawRAExpr.cleanVacuousUnions]
      have hLeft :
          e₁.cleanVacuousUnions.symbols ⊆
            (RawRAExpr.union e₁ e₂).symbols := by
        simp only [RawRAExpr.symbols]
        exact subset_trans ih₁ Finset.subset_union_left
      have hRight :
          e₂.cleanVacuousUnions.symbols ⊆
            (RawRAExpr.union e₁ e₂).symbols := by
        simp only [RawRAExpr.symbols]
        exact subset_trans ih₂ Finset.subset_union_right
      have hBoth :
          (RawRAExpr.union e₁.cleanVacuousUnions
              e₂.cleanVacuousUnions).symbols ⊆
            (RawRAExpr.union e₁ e₂).symbols := by
        simp only [RawRAExpr.symbols]
        exact Finset.union_subset_union ih₁ ih₂
      split
      · exact hRight
      · exact hLeft
      · exact hBoth
  | diff e₁ e₂ ih₁ ih₂ =>
      simp only [RawRAExpr.cleanVacuousUnions,
        RawRAExpr.symbols]
      exact Finset.union_subset_union ih₁ ih₂

/- Projection cleanup reads no new relation. -/
theorem rawSymbols_cleanVacuousProjections_subset
    (Γ : UnnamedSchema A)
    (e : RawRAExpr A D) :
    (e.cleanVacuousProjections Γ).symbols ⊆
      e.symbols := by
  induction e with
  | top => simp [RawRAExpr.cleanVacuousProjections]
  | empty n => simp [RawRAExpr.cleanVacuousProjections]
  | rel X => simp [RawRAExpr.cleanVacuousProjections]
  | single d => simp [RawRAExpr.cleanVacuousProjections]
  | select s e ih =>
      simpa [RawRAExpr.cleanVacuousProjections,
        RawRAExpr.symbols] using ih
  | proj idxs e ih =>
      rw [RawRAExpr.cleanVacuousProjections]
      have hInner :
          (RawRAExpr.proj idxs
              (e.cleanVacuousProjections Γ)).symbols ⊆
            (RawRAExpr.proj idxs e).symbols := by
        simpa [RawRAExpr.symbols] using ih
      have hBare :
          (e.cleanVacuousProjections Γ).symbols ⊆
            (RawRAExpr.proj idxs e).symbols := by
        simpa [RawRAExpr.symbols] using ih
      split
      · split
        · exact hBare
        · exact hInner
      · exact hInner
  | prod e₁ e₂ ih₁ ih₂ =>
      simp only [RawRAExpr.cleanVacuousProjections,
        RawRAExpr.symbols]
      exact Finset.union_subset_union ih₁ ih₂
  | union e₁ e₂ ih₁ ih₂ =>
      simp only [RawRAExpr.cleanVacuousProjections,
        RawRAExpr.symbols]
      exact Finset.union_subset_union ih₁ ih₂
  | diff e₁ e₂ ih₁ ih₂ =>
      simp only [RawRAExpr.cleanVacuousProjections,
        RawRAExpr.symbols]
      exact Finset.union_subset_union ih₁ ih₂

/- Cleaning an expression reads no new relation. -/
theorem raSymbols_clean_subset
    {n : Nat}
    (e : RAExpr D Γ n) :
    e.clean.symbols ⊆ e.symbols := by
  refine
    subset_trans
      (rawSymbols_mergeSelections_subset _) ?_
  refine
    subset_trans
      (rawSymbols_cleanVacuousProjections_subset Γ _) ?_
  refine
    subset_trans
      (rawSymbols_cleanVacuousUnions_subset _) ?_
  exact rawSymbols_cleanVacuousProducts_subset _

end Preprocess

end Whiel

------------------------------------------------------------
-- Cleaning A Guard And A Command
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Cleaning one conjunction reads no new relation. -/
theorem guardSymbols_cleanAnd_subset
    (φ ψ : Guard D Γ) :
    (Guard.cleanAnd φ ψ).symbols ⊆
      φ.symbols ∪ ψ.symbols := by
  cases φ <;> cases ψ <;>
    simp [Guard.cleanAnd, Guard.symbols]

/- Cleaning one disjunction reads no new relation. -/
theorem guardSymbols_cleanOr_subset
    (φ ψ : Guard D Γ) :
    (Guard.cleanOr φ ψ).symbols ⊆
      φ.symbols ∪ ψ.symbols := by
  cases φ <;> cases ψ <;>
    simp [Guard.cleanOr, Guard.symbols]

/- Cleaning one negation reads no new relation. -/
theorem guardSymbols_cleanNot_subset
    (φ : Guard D Γ) :
    (Guard.cleanNot φ).symbols ⊆ φ.symbols := by
  cases φ <;> simp [Guard.cleanNot, Guard.symbols]

/- Cleaning a guard reads no new relation. -/
theorem guardSymbols_clean_subset
    (G : Guard D Γ) :
    G.clean.symbols ⊆ G.symbols := by
  induction G with
  | «true» => simp [Guard.clean]
  | «false» => simp [Guard.clean]
  | eq e₁ e₂ =>
      simp only [Guard.clean, Guard.symbols]
      exact
        Finset.union_subset_union
          (raSymbols_clean_subset e₁)
          (raSymbols_clean_subset e₂)
  | subset e₁ e₂ =>
      simp only [Guard.clean, Guard.symbols]
      exact
        Finset.union_subset_union
          (raSymbols_clean_subset e₁)
          (raSymbols_clean_subset e₂)
  | and φ ψ ihφ ihψ =>
      refine
        subset_trans (guardSymbols_cleanAnd_subset _ _) ?_
      simp only [Guard.symbols]
      exact Finset.union_subset_union ihφ ihψ
  | or φ ψ ihφ ihψ =>
      refine
        subset_trans (guardSymbols_cleanOr_subset _ _) ?_
      simp only [Guard.symbols]
      exact Finset.union_subset_union ihφ ihψ
  | not φ ih =>
      refine
        subset_trans (guardSymbols_cleanNot_subset _) ?_
      simpa [Guard.symbols] using ih

/- Cleaning one sequence reads no new relation. -/
theorem symbols_cleanSeq_subset
    (C₁ C₂ : Cmd D Γ) :
    (Cmd.cleanSeq C₁ C₂).symbols ⊆
      C₁.symbols ∪ C₂.symbols := by
  induction C₁ generalizing C₂ with
  | skip =>
      simp [Cmd.cleanSeq, Cmd.symbols]
  | assign X e =>
      cases C₂ <;>
        simp [Cmd.cleanSeq, Cmd.symbols]
  | seq C₁₁ C₁₂ ih₁ ih₂ =>
      refine
        subset_trans (ih₁ (Cmd.cleanSeq C₁₂ C₂)) ?_
      refine
        Finset.union_subset ?_ ?_
      · intro X hX
        simp only [Cmd.symbols, Finset.mem_union]
        tauto
      · refine
          subset_trans (ih₂ C₂)
            (Finset.union_subset ?_ ?_)
        · intro X hX
          simp only [Cmd.symbols, Finset.mem_union]
          tauto
        · intro X hX
          simp only [Cmd.symbols, Finset.mem_union]
          tauto
  | ite G C₁₁ C₁₂ ih₁ ih₂ =>
      cases C₂ <;>
        simp [Cmd.cleanSeq, Cmd.symbols]
  | «while» G C₁ ih =>
      cases C₂ <;>
        simp [Cmd.cleanSeq, Cmd.symbols]

/- Cleaning a command reads no new relation. -/
theorem symbols_clean_subset
    (C : Cmd D Γ) :
    C.clean.symbols ⊆ C.symbols := by
  induction C with
  | skip => simp [Cmd.clean]
  | assign X e =>
      simp only [Cmd.clean, Cmd.symbols]
      exact
        Finset.union_subset_union (Finset.Subset.refl _)
          (raSymbols_clean_subset e)
  | seq C₁ C₂ ih₁ ih₂ =>
      refine
        subset_trans (symbols_cleanSeq_subset _ _) ?_
      simp only [Cmd.symbols]
      exact Finset.union_subset_union ih₁ ih₂
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp only [Cmd.clean, Cmd.symbols]
      exact
        Finset.union_subset_union
          (Finset.union_subset_union
            (guardSymbols_clean_subset G) ih₁)
          ih₂
  | «while» G C ih =>
      simp only [Cmd.clean, Cmd.symbols]
      exact
        Finset.union_subset_union
          (guardSymbols_clean_subset G) ih

end Preprocess

end Whiel

------------------------------------------------------------
-- Cleaning Adds No Loop
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Cleaning one sequence of loop-free code is loop-free. -/
theorem loopFree_cleanSeq
    {C₁ C₂ : Cmd D Γ}
    (h₁ : LoopFree C₁)
    (h₂ : LoopFree C₂) :
    LoopFree (Cmd.cleanSeq C₁ C₂) := by
  induction C₁ generalizing C₂ with
  | skip => simpa [Cmd.cleanSeq] using h₂
  | assign X e =>
      cases C₂ <;>
        simp_all [Cmd.cleanSeq, LoopFree, loops]
  | seq C₁₁ C₁₂ ih₁ ih₂ =>
      rcases (loopFree_seq_iff C₁₁ C₁₂).mp h₁ with
        ⟨hOne, hTwo⟩
      exact ih₁ hOne (ih₂ hTwo h₂)
  | ite G C₁₁ C₁₂ ih₁ ih₂ =>
      cases C₂ <;>
        simp_all [Cmd.cleanSeq, LoopFree, loops]
  | «while» G C₁ ih =>
      exact absurd h₁ (not_loopFree_while G C₁)

/- Cleaning loop-free code leaves it loop-free. -/
theorem loopFree_clean
    {C : Cmd D Γ}
    (hFree : LoopFree C) :
    LoopFree C.clean := by
  induction C with
  | skip => rfl
  | assign X e => rfl
  | seq C₁ C₂ ih₁ ih₂ =>
      rcases (loopFree_seq_iff C₁ C₂).mp hFree with
        ⟨h₁, h₂⟩
      exact loopFree_cleanSeq (ih₁ h₁) (ih₂ h₂)
  | ite G C₁ C₂ ih₁ ih₂ =>
      rcases (loopFree_ite_iff G C₁ C₂).mp hFree with
        ⟨h₁, h₂⟩
      exact
        (loopFree_ite_iff G.clean C₁.clean C₂.clean).mpr
          ⟨ih₁ h₁, ih₂ h₂⟩
  | «while» G C ih =>
      exact absurd hFree (not_loopFree_while G C)

end Preprocess

end Whiel

------------------------------------------------------------
-- The Final Clean Of A Framed Loop
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Replacing a loop body by an equirunning one changes no
  run of the loop. The guard is untouched, so only the body
  hypothesis is needed.
-/
theorem bigStep_while_congr_body
    {G : Guard D Γ}
    {B B' : Cmd D Γ}
    (hBody :
      ∀ I J : Instance D Γ,
        Cmd.BigStep B' I J → Cmd.BigStep B I J)
    {I J : Instance D Γ}
    (hStep : Cmd.BigStep (.«while» G B') I J) :
    Cmd.BigStep (.«while» G B) I J := by
  generalize hW :
      (Cmd.«while» G B' : Cmd D Γ) = W at hStep
  induction hStep generalizing B' with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | while_false hFalse =>
      cases hW
      exact Cmd.BigStep.while_false hFalse
  | while_true hEval hRun hLoop ihRun ihLoop =>
      cases hW
      exact
        Cmd.BigStep.while_true hEval (hBody _ _ hRun)
          (ihLoop hBody rfl)

namespace Framed

/-
  The final clean: `Cmd.clean` on the prefix, the body and
  the suffix. The guard is not a command and is left as the
  operations built it.
-/
def clean (L : Framed D Γ) : Framed D Γ where
  init := L.init.clean
  guard := L.guard
  body := L.body.clean
  close := L.close.clean

@[simp] theorem clean_init
    (L : Framed D Γ) :
    L.clean.init = L.init.clean :=
  rfl

@[simp] theorem clean_guard
    (L : Framed D Γ) :
    L.clean.guard = L.guard :=
  rfl

@[simp] theorem clean_body
    (L : Framed D Γ) :
    L.clean.body = L.body.clean :=
  rfl

@[simp] theorem clean_close
    (L : Framed D Γ) :
    L.clean.close = L.close.clean :=
  rfl

/- The clean changes no run of the unfolding. -/
theorem bigStepEquiv_clean
    (L : Framed D Γ) :
    Cmd.BigStepEquiv L.unfold L.clean.unfold := by
  intro I J
  simp only [unfold, clean, Cmd.bigStep_seq_iff]
  constructor
  · rintro ⟨K₁, hInit, K₂, hLoop, hClose⟩
    exact
      ⟨K₁,
        (Cmd.bigStep_clean_iff L.init I K₁).mpr hInit,
        K₂,
        bigStep_while_congr_body
          (fun a b h =>
            (Cmd.bigStep_clean_iff L.body a b).mpr h)
          hLoop,
        (Cmd.bigStep_clean_iff L.close K₂ J).mpr
          hClose⟩
  · rintro ⟨K₁, hInit, K₂, hLoop, hClose⟩
    exact
      ⟨K₁,
        (Cmd.bigStep_clean_iff L.init I K₁).mp hInit,
        K₂,
        bigStep_while_congr_body
          (fun a b h =>
            (Cmd.bigStep_clean_iff L.body a b).mp h)
          hLoop,
        (Cmd.bigStep_clean_iff L.close K₂ J).mp hClose⟩

/- The clean keeps the loop-free components loop-free. -/
theorem loopFreeParts_clean
    {L : Framed D Γ}
    (hParts : L.LoopFreeParts) :
    L.clean.LoopFreeParts :=
  ⟨loopFree_clean hParts.1, loopFree_clean hParts.2.1,
    loopFree_clean hParts.2.2⟩

/- The clean reads no new relation. -/
theorem symbols_unfold_clean_subset
    (L : Framed D Γ) :
    L.clean.unfold.symbols ⊆ L.unfold.symbols := by
  simp only [unfold, clean, Cmd.symbols]
  exact
    Finset.union_subset_union (symbols_clean_subset L.init)
      (Finset.union_subset_union
        (Finset.union_subset_union
          (Finset.Subset.refl _)
          (symbols_clean_subset L.body))
        (symbols_clean_subset L.close))

/- The clean assigns exactly the same relations. -/
@[simp] theorem assignedSymbols_unfold_clean
    (L : Framed D Γ) :
    L.clean.unfold.assignedSymbols =
      L.unfold.assignedSymbols := by
  simp only [unfold, clean, Cmd.assignedSymbols,
    Cmd.assignedSymbols_clean]

end Framed

end Preprocess

end Whiel
