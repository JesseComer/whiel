-- Author: Jesse Comer
import Whiel.Hoare.Preproc

/-
  Symbol bounds for substitution, strongest postconditions
  and weakest preconditions.

  Substitution, the quantifier-free strongest postcondition
  and the loop-free weakest precondition all introduce no
  relation name of their own: every name they produce
  already occurs in an argument. This module proves those
  bounds generically, for any relation-name carrier.

  The corresponding bound for a whole preprocessing result
  is deliberately absent. The generic preprocessor draws
  flag relations, so the preprocessed loop's symbols are
  bounded by the flag extension it lives over and not by the
  input triple's symbols; that bound is `Cmd.symbols_subset_syms`
  at the extended schema and needs no separate statement.

  Key theorems:
    * `RawRAExpr.symbols_subst_subset`
    * `RAExpr.symbols_subst_subset`
    * `QFAssertExpr.symbols_subst_subset`
    * `Guard.symbols_subset_syms`
    * `Cmd.symbols_subset_syms`
    * `Cmd.framedLoopParts?_symbols_subset`
    * `AssertExpr.spLoopFreeNoFresh?_formulaSymbols_subset`
    * `AssertExpr.wpLoopFree_formulaSymbols_subset`
-/

------------------------------------------------------------
-- Substitution Symbol Bounds
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type} [RelationNames A] [Domain D]

/- Substitution introduces only replacement symbols. -/
theorem symbols_subst_subset
    (x : A)
    (e' : RawRAExpr A D) :
    ∀ e : RawRAExpr A D,
      (e.subst x e').symbols ⊆ e.symbols ∪ e'.symbols
  | .top => by
      simp [subst, symbols]
  | .empty n => by
      simp [subst, symbols]
  | .rel y => by
      by_cases hy : y = x
      · simp [subst, hy]
      · simp [subst, hy]
  | .single d => by
      simp [subst, symbols]
  | .select φ e₁ => by
      simpa [subst, symbols] using
        symbols_subst_subset x e' e₁
  | .proj idxs e₁ => by
      simpa [subst, symbols] using
        symbols_subst_subset x e' e₁
  | .prod e₁ e₂ => by
      intro X hX
      simp only [subst, symbols, Finset.mem_union] at hX ⊢
      rcases hX with hX | hX
      · rcases Finset.mem_union.mp
            (symbols_subst_subset x e' e₁ hX) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Finset.mem_union.mp
            (symbols_subst_subset x e' e₂ hX) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | .union e₁ e₂ => by
      intro X hX
      simp only [subst, symbols, Finset.mem_union] at hX ⊢
      rcases hX with hX | hX
      · rcases Finset.mem_union.mp
            (symbols_subst_subset x e' e₁ hX) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Finset.mem_union.mp
            (symbols_subst_subset x e' e₂ hX) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | .diff e₁ e₂ => by
      intro X hX
      simp only [subst, symbols, Finset.mem_union] at hX ⊢
      rcases hX with hX | hX
      · rcases Finset.mem_union.mp
            (symbols_subst_subset x e' e₁ hX) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Finset.mem_union.mp
            (symbols_subst_subset x e' e₂ hX) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

end RawRAExpr

namespace RAExpr

variable {A D : Type} [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}

/- Typed substitution adds only replacement symbols. -/
theorem symbols_subst_subset
    {n : Nat}
    (e : RAExpr D Γ n)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    (e.subst X eRep).symbols ⊆
      e.symbols ∪ eRep.symbols :=
  RawRAExpr.symbols_subst_subset X.1 eRep.expr e.expr

/- Symbols of a relation-name expression. -/
theorem symbols_rel
    (X : Γ.syms) :
    (rel (D := D) X).symbols = {X.1} :=
  rfl

/- Retyping over an extension preserves symbols. -/
theorem symbols_onExtension
    {Δ : UnnamedSchema A} {n : Nat}
    (hExt : Δ.extensionOf Γ)
    (e : RAExpr D Γ n) :
    (e.onExtension hExt).symbols = e.symbols :=
  rfl

/- Arity transport preserves symbols. -/
theorem symbols_castArity
    {m n : Nat}
    (h : m = n)
    (e : RAExpr D Γ n) :
    (castArity h e).symbols = e.symbols :=
  rfl

end RAExpr

namespace Whiel

namespace QFAssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Substitution introduces only replacement symbols. -/
theorem symbols_subst_subset
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    (φ : QFAssertExpr D Γ) →
      (φ.subst X eRep).symbols ⊆
        φ.symbols ∪ eRep.symbols
  | .«true» => by
      simp [subst, Guard.symbols]
  | .«false» => by
      simp [subst, Guard.symbols]
  | .eq e₁ e₂ => by
      intro Y hY
      simp only [subst, Guard.symbols, Finset.mem_union]
        at hY ⊢
      rcases hY with hY | hY
      · rcases Finset.mem_union.mp
            (e₁.symbols_subst_subset X eRep hY) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Finset.mem_union.mp
            (e₂.symbols_subst_subset X eRep hY) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | .subset e₁ e₂ => by
      intro Y hY
      simp only [subst, Guard.symbols, Finset.mem_union]
        at hY ⊢
      rcases hY with hY | hY
      · rcases Finset.mem_union.mp
            (e₁.symbols_subst_subset X eRep hY) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Finset.mem_union.mp
            (e₂.symbols_subst_subset X eRep hY) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | .and φ ψ => by
      intro Y hY
      simp only [subst, Guard.symbols, Finset.mem_union]
        at hY ⊢
      rcases hY with hY | hY
      · rcases Finset.mem_union.mp
            (symbols_subst_subset X eRep φ hY) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Finset.mem_union.mp
            (symbols_subst_subset X eRep ψ hY) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | .or φ ψ => by
      intro Y hY
      simp only [subst, Guard.symbols, Finset.mem_union]
        at hY ⊢
      rcases hY with hY | hY
      · rcases Finset.mem_union.mp
            (symbols_subst_subset X eRep φ hY) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Finset.mem_union.mp
            (symbols_subst_subset X eRep ψ hY) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | .not φ => by
      intro Y hY
      simp only [subst, Guard.symbols] at hY ⊢
      exact symbols_subst_subset X eRep φ hY

end QFAssertExpr

end Whiel

------------------------------------------------------------
-- Schema Bounds Without a Name Supply
------------------------------------------------------------

namespace Whiel

namespace Guard

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Guards only mention names in their schema. -/
theorem symbols_subset_syms
    (G : Guard D Γ) :
    G.symbols ⊆ Γ.syms := by
  induction G with
  | «true» => simp [symbols]
  | «false» => simp [symbols]
  | eq e₁ e₂ =>
      simpa [symbols] using
        Finset.union_subset e₁.symbols_subset
          e₂.symbols_subset
  | subset e₁ e₂ =>
      simpa [symbols] using
        Finset.union_subset e₁.symbols_subset
          e₂.symbols_subset
  | and G H ihG ihH =>
      simpa [symbols] using Finset.union_subset ihG ihH
  | or G H ihG ihH =>
      simpa [symbols] using Finset.union_subset ihG ihH
  | not G ih =>
      simpa [symbols] using ih

end Guard

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Commands only mention names in their schema. -/
theorem symbols_subset_syms
    (C : Cmd D Γ) :
    C.symbols ⊆ Γ.syms := by
  induction C with
  | «skip» => simp [symbols]
  | assign X e =>
      simpa [symbols] using
        Finset.union_subset
          (Finset.singleton_subset_iff.mpr X.2)
          e.symbols_subset
  | seq C₁ C₂ ih₁ ih₂ =>
      simpa [symbols] using Finset.union_subset ih₁ ih₂
  | ite G C₁ C₂ ih₁ ih₂ =>
      simpa [symbols] using
        Finset.union_subset
          (Finset.union_subset G.symbols_subset_syms ih₁)
          ih₂
  | «while» G C ih =>
      simpa [symbols] using
        Finset.union_subset G.symbols_subset_syms ih

end Cmd

end Whiel

------------------------------------------------------------
-- Framed-Loop Component Symbols
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Sequenced-list symbols are the member symbols. -/
theorem mem_symbols_seqList
    (Cs : List (Cmd D Γ))
    (X : A) :
    X ∈ (seqList Cs).symbols ↔
      ∃ C ∈ Cs, X ∈ C.symbols := by
  induction Cs with
  | nil =>
      simp [seqList, symbols]
  | cons C Cs ih =>
      simp [seqList, symbols, ih]

/- Flattened members mention only source symbols. -/
theorem symbols_subset_of_mem_flattenSeq
    (C : Cmd D Γ) :
    ∀ C' ∈ C.flattenSeq, C'.symbols ⊆ C.symbols := by
  induction C with
  | skip =>
      intro C' hC'
      simp [flattenSeq] at hC'
  | assign X e =>
      intro C' hC'
      have hEq : C' = .assign X e := by
        simpa [flattenSeq] using hC'
      subst hEq
      exact Finset.Subset.refl _
  | seq C₁ C₂ ih₁ ih₂ =>
      intro C' hC'
      rcases List.mem_append.mp
          (by simpa [flattenSeq] using hC') with h | h
      · exact
          Finset.Subset.trans (ih₁ C' h)
            (by simp [symbols])
      · exact
          Finset.Subset.trans (ih₂ C' h)
            (by simp [symbols])
  | ite G C₁ C₂ ih₁ ih₂ =>
      intro C' hC'
      have hEq : C' = .ite G C₁ C₂ := by
        simpa [flattenSeq] using hC'
      subst hEq
      exact Finset.Subset.refl _
  | «while» G C ih =>
      intro C' hC'
      have hEq : C' = .while G C := by
        simpa [flattenSeq] using hC'
      subst hEq
      exact Finset.Subset.refl _

/-
  Every framed-loop component mentions only source
  symbols.
-/
theorem framedLoopParts?_symbols_subset
    {C : Cmd D Γ}
    {Init : Cmd D Γ}
    {G : Guard D Γ}
    {Body Close : Cmd D Γ}
    (h : C.framedLoopParts? = some (Init, G, Body, Close)) :
    Init.symbols ⊆ C.symbols ∧
      G.symbols ⊆ C.symbols ∧
        Body.symbols ⊆ C.symbols ∧
          Close.symbols ⊆ C.symbols := by
  unfold framedLoopParts? at h
  generalize hSplit :
    splitFramedLoopList? C.flattenSeq = splitOpt at h
  cases splitOpt with
  | none =>
      contradiction
  | some parts =>
      rcases parts with
        ⟨InitList, G₀, Body₀, CloseList⟩
      dsimp only at h
      split at h
      · split at h
        · split at h
          · cases h
            have hShape :=
              splitFramedLoopList?_sound hSplit
            have hMem :
                ∀ C' ∈ InitList ++
                    ((.while G Body : Cmd D Γ) ::
                      CloseList),
                  C'.symbols ⊆ C.symbols := by
              intro C' hC'
              rw [← hShape] at hC'
              exact symbols_subset_of_mem_flattenSeq
                C C' hC'
            have hLoop :
                (Cmd.while G Body).symbols ⊆
                  C.symbols :=
              hMem _ (by simp)
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro X hX
              rcases (mem_symbols_seqList InitList X).mp
                  hX with ⟨C', hC', hXC'⟩
              exact hMem C' (by simp [hC']) hXC'
            · intro X hX
              apply hLoop
              simp [symbols, hX]
            · intro X hX
              apply hLoop
              simp [symbols, hX]
            · intro X hX
              rcases (mem_symbols_seqList CloseList X).mp
                  hX with ⟨C', hC', hXC'⟩
              exact hMem C' (by simp [hC']) hXC'
          · contradiction
        · contradiction
      · contradiction

end Cmd

end Whiel

------------------------------------------------------------
-- Supply-Free SP Symbol Bounds
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Δ : UnnamedSchema A}

/- Lifted replacement expressions keep their symbols. -/
theorem symbols_liftRA
    (hExt : Δ.extensionOf Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    (liftRA hExt X eRep).symbols = eRep.symbols :=
  rfl

/- Guard conjunction adds exactly the guard symbols. -/
theorem symbols_formulaGuardAnd
    (hExt : Δ.extensionOf Γ)
    (φ : QFAssertExpr D Δ)
    (G : Guard D Γ) :
    (formulaGuardAnd hExt φ G).symbols =
      φ.symbols ∪ G.symbols := by
  simp [formulaGuardAnd, formulaAnd, Guard.symbols]

/-
  Negated-guard conjunction adds exactly the guard
  symbols.
-/
theorem symbols_formulaNotGuardAnd
    (hExt : Δ.extensionOf Γ)
    (φ : QFAssertExpr D Δ)
    (G : Guard D Γ) :
    (formulaNotGuardAnd hExt φ G).symbols =
      φ.symbols ∪ G.symbols := by
  simp [formulaNotGuardAnd, formulaAnd, Guard.symbols]

/-
  The supply-free SP formula mentions only precondition and
  command symbols.
-/
theorem spLoopFreeNoFreshFormula?_symbols_subset
    (hExt : Δ.extensionOf Γ) :
    (C : Cmd D Γ) →
      (hLoopFree : C.LoopFree) →
        (pre post : QFAssertExpr D Δ) →
          spLoopFreeNoFreshFormula? hExt C hLoopFree pre =
              some post →
            post.symbols ⊆ pre.symbols ∪ C.symbols
  | .skip, _, pre, post, h => by
      have hEq : pre = post := by
        simpa [spLoopFreeNoFreshFormula?] using h
      subst hEq
      exact Finset.subset_union_left
  | .assign X e, _, pre, post, h => by
      by_cases hOld :
          X.1 ∈ pre.symbols ∨ X.1 ∈ e.symbols
      · simp [spLoopFreeNoFreshFormula?, hOld] at h
      · have hEq :
            formulaAnd pre
                (QFAssertExpr.eq
                  (RAExpr.rel
                    (UnnamedSchema.symOfExtension hExt X))
                  (liftRA hExt X e)) = post := by
          simpa [spLoopFreeNoFreshFormula?, hOld] using h
        subst hEq
        intro Y hY
        simp only [formulaAnd, Guard.symbols,
          RAExpr.symbols_rel,
          UnnamedSchema.symOfExtension, Cmd.symbols,
          Finset.mem_union, Finset.mem_singleton]
          at hY ⊢
        tauto
  | .seq C₁ C₂, hLoopFree, pre, post, h => by
      rw [spLoopFreeNoFreshFormula?] at h
      simp only [Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      rcases h with ⟨middle, h₁, h₂⟩
      have ih₁ :=
        spLoopFreeNoFreshFormula?_symbols_subset hExt C₁
          hLoopFree.1 pre middle h₁
      have ih₂ :=
        spLoopFreeNoFreshFormula?_symbols_subset hExt C₂
          hLoopFree.2 middle post h₂
      intro Y hY
      simp only [Cmd.symbols, Finset.mem_union] at ⊢
      rcases Finset.mem_union.mp (ih₂ hY) with hM | hC₂
      · rcases Finset.mem_union.mp (ih₁ hM) with
          hP | hC₁
        · exact Or.inl hP
        · exact Or.inr (Or.inl hC₁)
      · exact Or.inr (Or.inr hC₂)
  | .ite G C₁ C₂, hLoopFree, pre, post, h => by
      rw [spLoopFreeNoFreshFormula?] at h
      simp only [Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at h
      rcases h with
        ⟨thenPost, hThen, elsePost, hElse, hPost⟩
      subst hPost
      have ih₁ :=
        spLoopFreeNoFreshFormula?_symbols_subset hExt C₁
          hLoopFree.1 _ thenPost hThen
      have ih₂ :=
        spLoopFreeNoFreshFormula?_symbols_subset hExt C₂
          hLoopFree.2 _ elsePost hElse
      rw [symbols_formulaGuardAnd] at ih₁
      rw [symbols_formulaNotGuardAnd] at ih₂
      intro Y hY
      simp only [formulaOr, Guard.symbols, Cmd.symbols,
        Finset.mem_union] at hY ⊢
      rcases hY with hY | hY
      · rcases Finset.mem_union.mp (ih₁ hY) with h | h
        · rcases Finset.mem_union.mp h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inl (Or.inr h))
      · rcases Finset.mem_union.mp (ih₂ hY) with h | h
        · rcases Finset.mem_union.mp h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr h)
  | .while _ _, hLoopFree, _, _, _ => by
      exact False.elim hLoopFree

/-
  Supply-free SP mentions only precondition and command
  symbols.
-/
theorem spLoopFreeNoFresh?_formulaSymbols_subset
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre post : AssertExpr D Γ)
    (h : spLoopFreeNoFresh? C hLoopFree pre = some post) :
    post.formulaSymbols ⊆
      pre.formulaSymbols ∪ C.symbols := by
  simp only [spLoopFreeNoFresh?, Option.map_eq_some_iff]
    at h
  rcases h with ⟨formula, hFormula, hPost⟩
  subst hPost
  exact
    spLoopFreeNoFreshFormula?_symbols_subset
      pre.extendsFree C hLoopFree pre.formula formula
      hFormula

end AssertExpr

end Whiel

------------------------------------------------------------
-- Loop-Free WP Symbol Bounds
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Δ : UnnamedSchema A}

/- Conditional WP symbols are guard and branch symbols. -/
theorem symbols_formulaIte
    (hExt : Δ.extensionOf Γ)
    (G : Guard D Γ)
    (thenFormula elseFormula : QFAssertExpr D Δ) :
    (formulaIte hExt G thenFormula elseFormula).symbols =
      G.symbols ∪ thenFormula.symbols ∪
        (G.symbols ∪ elseFormula.symbols) := by
  simp [formulaIte, formulaGuardImp, formulaNotGuardImp,
    formulaImp, QFAssertExpr.implies, Guard.implies,
    Guard.symbols]

/-
  The loop-free WP formula mentions only postcondition and
  command symbols.
-/
theorem wpLoopFreeFormula_symbols_subset
    (hExt : Δ.extensionOf Γ) :
    (C : Cmd D Γ) →
      (hLoopFree : C.LoopFree) →
        (post : QFAssertExpr D Δ) →
          (wpLoopFreeFormula hExt C hLoopFree
            post).symbols ⊆
              post.symbols ∪ C.symbols
  | .skip, _, post => by
      simp only [wpLoopFreeFormula]
      exact Finset.subset_union_left
  | .assign X e, _, post => by
      intro Y hY
      simp only [wpLoopFreeFormula] at hY
      have hSub := post.symbols_subst_subset
        (UnnamedSchema.symOfExtension hExt X)
        (liftRA hExt X e) hY
      simp only [symbols_liftRA, Cmd.symbols,
        Finset.mem_union] at hSub ⊢
      tauto
  | .seq C₁ C₂, hLoopFree, post => by
      have ih₂ :=
        wpLoopFreeFormula_symbols_subset hExt C₂
          hLoopFree.2 post
      have ih₁ :=
        wpLoopFreeFormula_symbols_subset hExt C₁
          hLoopFree.1
          (wpLoopFreeFormula hExt C₂ hLoopFree.2 post)
      intro Y hY
      simp only [wpLoopFreeFormula] at hY
      simp only [Cmd.symbols, Finset.mem_union]
      rcases Finset.mem_union.mp (ih₁ hY) with hM | hC₁
      · rcases Finset.mem_union.mp (ih₂ hM) with
          hP | hC₂
        · exact Or.inl hP
        · exact Or.inr (Or.inr hC₂)
      · exact Or.inr (Or.inl hC₁)
  | .ite G C₁ C₂, hLoopFree, post => by
      have ih₁ :=
        wpLoopFreeFormula_symbols_subset hExt C₁
          hLoopFree.1 post
      have ih₂ :=
        wpLoopFreeFormula_symbols_subset hExt C₂
          hLoopFree.2 post
      intro Y hY
      simp only [wpLoopFreeFormula, symbols_formulaIte,
        Finset.mem_union] at hY
      simp only [Cmd.symbols, Finset.mem_union]
      rcases hY with (hG | hThen) | (hG | hElse)
      · exact Or.inr (Or.inl (Or.inl hG))
      · rcases Finset.mem_union.mp (ih₁ hThen) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inl (Or.inl hG))
      · rcases Finset.mem_union.mp (ih₂ hElse) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
  | .while _ _, hLoopFree, _ => by
      exact False.elim hLoopFree

/-
  Loop-free WP mentions only postcondition and command
  symbols.
-/
theorem wpLoopFree_formulaSymbols_subset
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (post : AssertExpr D Γ) :
    (wpLoopFree C hLoopFree post).formulaSymbols ⊆
      post.formulaSymbols ∪ C.symbols :=
  wpLoopFreeFormula_symbols_subset post.extendsFree C
    hLoopFree post.formula

end AssertExpr

end Whiel
