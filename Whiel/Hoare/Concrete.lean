-- Author: Jesse Comer
import Whiel.AssertExpr.Substitution
import Whiel.AssertExpr.Entailment
import Whiel.Cmd.Rewrites.FramedLoop
import Whiel.Hoare.Abstract
import Whiel.RelationNames.NameSupply

/-
  Concrete Hoare connection for syntactic Whiel assertions.

  This file connects `AssertExpr` to the abstract Hoare
  development by interpreting syntactic assertions via
  `AssertExpr.eval`.

  Main constructions:
    * `instToAssertion`
    * `AssertExpr.wpAssign`
    * `AssertExpr.wpLoopFree`
    * `QFAssertExpr.wpLoopFree`
    * `AssertExpr.spAssign`
    * `AssertExpr.spLoopFree`
    * `loopOnlyInitVC`
    * `loopOnlyMaintVC`
    * `loopOnlyTermVC`

  Main correctness theorems:
    * `hoareValid_assertExpr_iff`
    * `hoareValid_assertExpr_eval_iff`
    * `AssertExpr.wpAssign_eval_iff`
    * `AssertExpr.wpLoopFree_eval_iff`
    * `QFAssertExpr.wpLoopFree_eval_iff`
    * `QFAssertExpr.wpLoopFree_mono`
    * `QFAssertExpr.wpLoopFree_andList_equiv`
    * `QFAssertExpr.wpLoopFree_orList_equiv`
    * `wpAssign_wpOf`
    * `wpLoopFree_valid`
    * `wpLoopFree_wpOf`
    * `hoareValid_iff_entails_wpLoopFree`
    * `AssertExpr.spAssign_eval_iff`
    * `AssertExpr.spLoopFree_eval_iff`
    * `AssertExpr.spLoopFree_eval_imp_fixed`
    * `spAssign_spOf`
    * `spLoopFree_valid`
    * `spLoopFree_spOf`
    * `hoareValid_iff_spLoopFree_entails`
    * `hoareValid_loopOnly_of_vcs`
    * `hoareValid_loopOnly_of_invariantVCs`
-/

------------------------------------------------------------
-- Assertion Interpretation
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Syntactic assertions interpret by their semantics. -/
instance instToAssertion :
    ToAssertion D Γ (AssertExpr D Γ) where
  toAssertion φ := fun I => φ.eval I

end AssertExpr

end Whiel

------------------------------------------------------------
-- Hoare Validity
------------------------------------------------------------

namespace Whiel

namespace Hoare

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Hoare validity for `AssertExpr`s is semantic Hoare
  validity after evaluating the assertions.
-/
@[simp] theorem hoareValid_assertExpr_iff
    (φ : AssertExpr D Γ)
    (C : Cmd D Γ)
    (ψ : AssertExpr D Γ) :
    HoareValid φ C ψ ↔
      HoareValid
        (φ.eval : Assertion D Γ)
        C
        (ψ.eval : Assertion D Γ) :=
  Iff.rfl

@[simp] theorem hoareValid_assertExpr_eval_iff
    (φ : AssertExpr D Γ)
    (C : Cmd D Γ)
    (ψ : AssertExpr D Γ) :
    HoareValid φ C ψ ↔
      ∀ I J : Instance D Γ,
        φ.eval I → Cmd.BigStep C I J → ψ.eval J :=
  Iff.rfl

end Hoare

end Whiel

-- Concrete WP Constructors
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Δ : UnnamedSchema A}

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

private theorem guard_onExtension_eval_of_extends
    (hExt : Δ.extensionOf Γ)
    (G : Guard D Γ)
    {I : Instance D Γ}
    {J : Instance D Δ}
    (hM : Instance.Extends hExt I J) :
    (G.onExtension hExt).eval J ↔ G.eval I := by
  letI : Fact (Δ.extensionOf Γ) := ⟨hExt⟩
  exact
    Guard.onExtension_eval_reduct
      (Γ := Δ) (Δ := Γ) G J I
      (reduct_eq_of_extends hExt hM)

private def formulaOverExtension
    (hExt : Δ.extensionOf Γ)
    (φ : QFAssertExpr D Δ) :
    AssertExpr D Γ where
  fullSchema := Δ
  extendsFree := hExt
  formula := φ

/- Implication between full-schema assertion formulas. -/
def formulaImp
    (φ ψ : QFAssertExpr D Δ) :
    QFAssertExpr D Δ :=
  QFAssertExpr.implies φ ψ

/- Implication from a lifted command guard. -/
def formulaGuardImp
    (hExt : Δ.extensionOf Γ)
    (G : Guard D Γ)
    (φ : QFAssertExpr D Δ) :
    QFAssertExpr D Δ :=
  formulaImp (G.onExtension hExt) φ

/-
  Implication from the negation of a lifted command
  guard.
-/
def formulaNotGuardImp
    (hExt : Δ.extensionOf Γ)
    (G : Guard D Γ)
    (φ : QFAssertExpr D Δ) :
    QFAssertExpr D Δ :=
  formulaImp (QFAssertExpr.not (G.onExtension hExt)) φ

/-
  The conditional WP formula combines both guarded
  branches.
-/
def formulaIte
    (hExt : Δ.extensionOf Γ)
    (G : Guard D Γ)
    (thenFormula elseFormula : QFAssertExpr D Δ) :
    QFAssertExpr D Δ :=
  QFAssertExpr.and
    (formulaGuardImp hExt G thenFormula)
    (formulaNotGuardImp hExt G elseFormula)

/- Weakest precondition for one assignment. -/
def wpAssign
    (post : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    AssertExpr D Γ :=
  post.substFree X e

/- Formula-level WP for loop-free commands. -/
def wpLoopFreeFormula
    (hExt : Δ.extensionOf Γ) :
    (C : Cmd D Γ) →
      C.LoopFree →
        QFAssertExpr D Δ →
          QFAssertExpr D Δ
| .skip, _, post =>
    post
| .assign X e, _, post =>
    post.subst
      (UnnamedSchema.symOfExtension hExt X)
      (liftRA hExt X e)
| .seq C₁ C₂, hLoopFree, post =>
    wpLoopFreeFormula hExt C₁ hLoopFree.1
      (wpLoopFreeFormula hExt C₂ hLoopFree.2 post)
| .ite G C₁ C₂, hLoopFree, post =>
    formulaIte hExt G
      (wpLoopFreeFormula hExt C₁ hLoopFree.1 post)
      (wpLoopFreeFormula hExt C₂ hLoopFree.2 post)
| .while _ _, hLoopFree, _ =>
    False.elim hLoopFree

/- Weakest precondition for a loop-free command. -/
def wpLoopFree
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (post : AssertExpr D Γ) :
    AssertExpr D Γ where
  fullSchema := post.fullSchema
  extendsFree := post.extendsFree
  formula :=
    wpLoopFreeFormula post.extendsFree C hLoopFree
      post.formula

/-
  A guarded branch formula has the expected implication
  semantics.
-/
theorem formulaIte_eval_iff
    (hExt : Δ.extensionOf Γ)
    (G : Guard D Γ)
    (thenFormula elseFormula : QFAssertExpr D Δ)
    (I : Instance D Γ) :
    (formulaOverExtension hExt
      (formulaIte hExt G thenFormula elseFormula)).eval
        I ↔
      (G.eval I →
        (formulaOverExtension hExt thenFormula).eval I) ∧
        (¬ G.eval I →
          (formulaOverExtension hExt elseFormula).eval
            I) := by
  constructor
  · intro hEval
    rcases hEval with ⟨J, hM, hFormula⟩
    have hGuard :
        (G.onExtension hExt).eval J ↔ G.eval I :=
      guard_onExtension_eval_of_extends hExt G hM
    constructor
    · intro hG
      refine ⟨J, hM, ?_⟩
      rcases hFormula with ⟨hThen, _hElse⟩
      rcases hThen with hNotGuard | hThen
      · exact False.elim (hNotGuard (hGuard.mpr hG))
      · exact hThen
    · intro hNotG
      refine ⟨J, hM, ?_⟩
      rcases hFormula with ⟨_hThen, hElse⟩
      rcases hElse with hNotNotGuard | hElse
      · exact False.elim (hNotNotGuard (by
          exact (not_congr hGuard).mpr hNotG))
      · exact hElse
  · intro hBranches
    by_cases hG : G.eval I
    · rcases hBranches.1 hG with ⟨J, hM, hThen⟩
      refine ⟨J, hM, ?_⟩
      have hGuard :
          (G.onExtension hExt).eval J ↔ G.eval I :=
        guard_onExtension_eval_of_extends hExt G hM
      constructor
      · exact Or.inr hThen
      · exact Or.inl (by
          intro hNotGuard
          exact hNotGuard (hGuard.mpr hG))
    · rcases hBranches.2 hG with ⟨J, hM, hElse⟩
      refine ⟨J, hM, ?_⟩
      have hGuard :
          (G.onExtension hExt).eval J ↔ G.eval I :=
        guard_onExtension_eval_of_extends hExt G hM
      constructor
      · exact Or.inl (by
          intro hGuardM
          exact hG (hGuard.mp hGuardM))
      · exact Or.inr hElse

end AssertExpr

end Whiel

------------------------------------------------------------
-- Concrete SP Constructors
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Δ : UnnamedSchema A}

/- Conjunction between full-schema assertion formulas. -/
def formulaAnd
    (φ ψ : QFAssertExpr D Δ) :
    QFAssertExpr D Δ :=
  QFAssertExpr.and φ ψ

/- Disjunction between full-schema assertion formulas. -/
def formulaOr
    (φ ψ : QFAssertExpr D Δ) :
    QFAssertExpr D Δ :=
  QFAssertExpr.or φ ψ

/-
  Conjoin an assertion formula with a lifted command
  guard.
-/
def formulaGuardAnd
    (hExt : Δ.extensionOf Γ)
    (φ : QFAssertExpr D Δ)
    (G : Guard D Γ) :
    QFAssertExpr D Δ :=
  formulaAnd φ (G.onExtension hExt)

/-
  Conjoin an assertion formula with a lifted negated
  command guard.
-/
def formulaNotGuardAnd
    (hExt : Δ.extensionOf Γ)
    (φ : QFAssertExpr D Δ)
    (G : Guard D Γ) :
    QFAssertExpr D Δ :=
  formulaAnd φ (QFAssertExpr.not (G.onExtension hExt))

/- Assertion conjunction with a command guard. -/
def andGuard
    (φ : AssertExpr D Γ)
    (G : Guard D Γ) :
    AssertExpr D Γ where
  fullSchema := φ.fullSchema
  extendsFree := φ.extendsFree
  formula := formulaGuardAnd φ.extendsFree φ.formula G

/- Assertion conjunction with a negated command guard. -/
def andNotGuard
    (φ : AssertExpr D Γ)
    (G : Guard D Γ) :
    AssertExpr D Γ where
  fullSchema := φ.fullSchema
  extendsFree := φ.extendsFree
  formula := formulaNotGuardAnd φ.extendsFree φ.formula G

/- Guard conjunction preserves absence of bound symbols. -/
theorem andGuard_noBoundSymbols
    (φ : AssertExpr D Γ)
    (G : Guard D Γ)
    (hφ : φ.NoBoundSymbols) :
    (andGuard φ G).NoBoundSymbols := by
  simpa [NoBoundSymbols, andGuard] using hφ

/-
  Negated-guard conjunction preserves absence of bound
  symbols.
-/
theorem andNotGuard_noBoundSymbols
    (φ : AssertExpr D Γ)
    (G : Guard D Γ)
    (hφ : φ.NoBoundSymbols) :
    (andNotGuard φ G).NoBoundSymbols := by
  simpa [NoBoundSymbols, andNotGuard] using hφ

/- Loop-free WP preserves absence of bound symbols. -/
theorem wpLoopFree_noBoundSymbols
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (post : AssertExpr D Γ)
    (hPost : post.NoBoundSymbols) :
    (wpLoopFree C hLoopFree post).NoBoundSymbols := by
  simpa [NoBoundSymbols, wpLoopFree] using hPost

/-
  Assignment SP needs an old relation exactly when old
  `X` is read.
-/
def spAssignNeedsOld
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) : Prop :=
  X.1 ∈ pre.formula.symbols ∨ X.1 ∈ e.symbols

instance
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    Decidable (spAssignNeedsOld pre X e) := by
  unfold spAssignNeedsOld
  infer_instance

/-
  Assignment SP formula when no old value of `X` is
  needed.
-/
def spAssignNoOldFormula
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    QFAssertExpr D pre.fullSchema :=
  let Xtarget :=
    UnnamedSchema.symOfExtension pre.extendsFree X
  formulaAnd pre.formula
    (QFAssertExpr.eq (RAExpr.rel Xtarget)
      (liftRA pre.extendsFree X e))

/-
  Supply-free SP formula used by preprocessing. It rejects
  exactly an assignment whose old target value is needed.
-/
def spLoopFreeNoFreshFormula? :
    (hExt : Δ.extensionOf Γ) ->
      (C : Cmd D Γ) ->
        C.LoopFree ->
          QFAssertExpr D Δ ->
            Option (QFAssertExpr D Δ)
| _, .skip, _, pre =>
    some pre
| hExt, .assign X e, _, pre =>
    if X.1 ∈ pre.symbols ∨ X.1 ∈ e.symbols then
      none
    else
      some
        (formulaAnd pre
          (QFAssertExpr.eq
            (RAExpr.rel
              (UnnamedSchema.symOfExtension hExt X))
            (liftRA hExt X e)))
| hExt, .seq C₁ C₂, hLoopFree, pre => do
    let middle <-
      spLoopFreeNoFreshFormula? hExt C₁
        hLoopFree.1 pre
    spLoopFreeNoFreshFormula? hExt C₂
      hLoopFree.2 middle
| hExt, .ite G C₁ C₂, hLoopFree, pre => do
    let thenPost <-
      spLoopFreeNoFreshFormula? hExt C₁
        hLoopFree.1 (formulaGuardAnd hExt pre G)
    let elsePost <-
      spLoopFreeNoFreshFormula? hExt C₂
        hLoopFree.2 (formulaNotGuardAnd hExt pre G)
    some (formulaOr thenPost elsePost)
| _, .while _ _, hLoopFree, _ =>
    False.elim hLoopFree

/- Supply-free SP for a loop-free command, when defined. -/
def spLoopFreeNoFresh?
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre : AssertExpr D Γ) :
    Option (AssertExpr D Γ) :=
  (spLoopFreeNoFreshFormula? pre.extendsFree C
    hLoopFree pre.formula).map fun formula =>
      { fullSchema := pre.fullSchema
        extendsFree := pre.extendsFree
        formula := formula }

end AssertExpr

end Whiel

------------------------------------------------------------
-- General SP Constructors with Fresh Names
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Fresh raw name used for the old value of an assigned
  relation.
-/
def spAssignOldName
    (pre : AssertExpr D Γ)
    (X : Γ.syms) : A :=
  RelationNameSupply.freshName X.1 pre.fullSchema.syms

/-
  The old-value name is fresh for the current full
  schema.
-/
theorem spAssignOldName_fresh
    (pre : AssertExpr D Γ)
    (X : Γ.syms) :
    spAssignOldName pre X ∉ pre.fullSchema.syms := by
  exact
    RelationNameSupply.freshName_fresh
      X.1 pre.fullSchema.syms

/- Full schema after adding one old-value relation. -/
def spAssignOldFullSchema
    (pre : AssertExpr D Γ)
    (X : Γ.syms) :
    UnnamedSchema A :=
  pre.fullSchema.insertFresh
    (spAssignOldName pre X)
    (Γ.arity X)
    (spAssignOldName_fresh pre X)

/- The old-value schema extends the previous full schema. -/
def spAssignOldExtFull
    (pre : AssertExpr D Γ)
    (X : Γ.syms) :
    (spAssignOldFullSchema pre X).extensionOf
      pre.fullSchema :=
  UnnamedSchema.insertFresh_extensionOf
    pre.fullSchema (spAssignOldName pre X) (Γ.arity X)
    (spAssignOldName_fresh pre X)

/-
  The old-value schema extends the assertion's free
  schema.
-/
def spAssignOldExtFree
    (pre : AssertExpr D Γ)
    (X : Γ.syms) :
    (spAssignOldFullSchema pre X).extensionOf Γ :=
  UnnamedSchema.extensionOf_trans
    (spAssignOldExtFull pre X)
    pre.extendsFree

/-
  The assigned free relation as a symbol of the
  old-value schema.
-/
def spAssignOldTarget
    (pre : AssertExpr D Γ)
    (X : Γ.syms) :
    (spAssignOldFullSchema pre X).syms :=
  UnnamedSchema.symOfExtension (spAssignOldExtFree pre X) X

/-
  The fresh old-value relation as a symbol of the
  old-value schema.
-/
def spAssignOldSymbol
    (pre : AssertExpr D Γ)
    (X : Γ.syms) :
    (spAssignOldFullSchema pre X).syms :=
  UnnamedSchema.insertedSym
    pre.fullSchema (spAssignOldName pre X) (Γ.arity X)
    (spAssignOldName_fresh pre X)

/-
  The old-value relation typed at the assigned
  relation's arity.
-/
def spAssignOldRel
    (pre : AssertExpr D Γ)
    (X : Γ.syms) :
    RAExpr D (spAssignOldFullSchema pre X)
      ((spAssignOldFullSchema pre X).arity
        (spAssignOldTarget pre X)) :=
  RAExpr.relAs
    (spAssignOldTarget pre X)
    (spAssignOldSymbol pre X)
    (by
      have hTarget :
          (spAssignOldFullSchema pre X).arity
              (spAssignOldTarget pre X) = Γ.arity X :=
        UnnamedSchema.arity_eq_of_extensionOf
          (spAssignOldExtFree pre X) X
      have hOld :
          (spAssignOldFullSchema pre X).arity
              (spAssignOldSymbol pre X) = Γ.arity X := by
        simp [spAssignOldSymbol, spAssignOldFullSchema]
      exact hTarget.trans hOld.symm)

/-
  Assignment SP formula when an old value of `X` is
  needed.
-/
def spAssignOldFormula
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    QFAssertExpr D (spAssignOldFullSchema pre X) :=
  let hFull := spAssignOldExtFull pre X
  let hFree := spAssignOldExtFree pre X
  let Xold := spAssignOldRel pre X
  let Xtarget := spAssignOldTarget pre X
  let preOld :=
    (pre.formula.onExtension hFull).subst Xtarget Xold
  let rhsOld :=
    (liftRA hFree X e).subst Xtarget Xold
  formulaAnd preOld
    (QFAssertExpr.eq (RAExpr.rel Xtarget) rhsOld)

/- Strongest postcondition for one assignment. -/
def spAssign
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    AssertExpr D Γ :=
  if _hNeed : spAssignNeedsOld pre X e then
    { fullSchema := spAssignOldFullSchema pre X
      extendsFree := spAssignOldExtFree pre X
      formula := spAssignOldFormula pre X e }
  else
    { fullSchema := pre.fullSchema
      extendsFree := pre.extendsFree
      formula := spAssignNoOldFormula pre X e }

/- Result of an SP computation, recording schema growth. -/
structure SPResult
    (pre : AssertExpr D Γ) where
  post : AssertExpr D Γ
  extendsFull : post.fullSchema.extensionOf pre.fullSchema

namespace SPResult

end SPResult

/- Assignment SP only grows the full schema. -/
def spAssignExtFull
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    (spAssign pre X e).fullSchema.extensionOf
      pre.fullSchema := by
  by_cases hNeed : spAssignNeedsOld pre X e
  · dsimp [spAssign]
    rw [if_pos hNeed]
    exact spAssignOldExtFull pre X
  · dsimp [spAssign]
    rw [if_neg hNeed]
    exact UnnamedSchema.extensionOf_refl pre.fullSchema

/- Assignment SP as an `SPResult`. -/
def spAssignResult
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    SPResult pre :=
  { post := spAssign pre X e
    extendsFull := spAssignExtFull pre X e }

/- Loop-free strongest postcondition as an `SPResult`. -/
def spLoopFreeResult :
    (C : Cmd D Γ) →
      C.LoopFree →
        (pre : AssertExpr D Γ) →
          SPResult pre
| .skip, _, pre =>
    { post := pre,
      extendsFull :=
        UnnamedSchema.extensionOf_refl pre.fullSchema }
| .assign X e, _, pre =>
    spAssignResult pre X e
| .seq C₁ C₂, hLoopFree, pre =>
    let r₁ := spLoopFreeResult C₁ hLoopFree.1 pre
    let r₂ := spLoopFreeResult C₂ hLoopFree.2 r₁.post
    { post := r₂.post,
      extendsFull :=
        UnnamedSchema.extensionOf_trans
          r₂.extendsFull r₁.extendsFull }
| .ite G C₁ C₂, hLoopFree, pre =>
    let preThen := andGuard pre G
    let preElse := andNotGuard pre G
    let rThen := spLoopFreeResult C₁ hLoopFree.1 preThen
    let hThenExt :
        rThen.post.fullSchema.extensionOf
          pre.fullSchema := by
      simpa [preThen, andGuard] using rThen.extendsFull
    let preElseLift := preElse.liftFull
      (by simpa [preElse, andNotGuard] using hThenExt)
    let rElse :=
      spLoopFreeResult C₂ hLoopFree.2 preElseLift
    let hElseExt :
        rElse.post.fullSchema.extensionOf
          rThen.post.fullSchema := by
      simpa [preElseLift, AssertExpr.liftFull] using
        rElse.extendsFull
    let thenLift := rThen.post.liftFull hElseExt
    { post :=
        { fullSchema := rElse.post.fullSchema,
          extendsFree := rElse.post.extendsFree,
          formula :=
            formulaOr
              thenLift.formula
              rElse.post.formula },
      extendsFull :=
        UnnamedSchema.extensionOf_trans
          hElseExt hThenExt }
| .while _ _, hLoopFree, _ =>
    False.elim hLoopFree

/- Strongest postcondition for loop-free commands. -/
def spLoopFree
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre : AssertExpr D Γ) :
    AssertExpr D Γ :=
  (spLoopFreeResult C hLoopFree pre).post

end AssertExpr

end Whiel

------------------------------------------------------------
-- Loop-Only Invariant VCs
------------------------------------------------------------

namespace Whiel

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Init obligation for a loop invariant. -/
def loopOnlyInitVC
    (pre inv : AssertExpr D Γ) :
    AssertExpr.Entailment D Γ where
  lhs := pre
  rhs := inv

/- Maintenance obligation for a loop invariant. -/
def loopOnlyMaintVC
    (inv : AssertExpr D Γ)
    (G : Guard D Γ)
    (Body : Cmd D Γ)
    (hBody : Body.LoopFree) :
    AssertExpr.Entailment D Γ where
  lhs := AssertExpr.andGuard inv G
  rhs := AssertExpr.wpLoopFree Body hBody inv

/- Termination obligation for a loop invariant. -/
def loopOnlyTermVC
    (inv post : AssertExpr D Γ)
    (G : Guard D Γ) :
    AssertExpr.Entailment D Γ where
  lhs := AssertExpr.andNotGuard inv G
  rhs := post

/- The init obligation is valid. -/
def loopOnlyInitValid
    (pre inv : AssertExpr D Γ) : Prop :=
  (loopOnlyInitVC pre inv).Valid

/- The maintenance obligation is valid. -/
def loopOnlyMaintValid
    (inv : AssertExpr D Γ)
    (G : Guard D Γ)
    (Body : Cmd D Γ)
    (hBody : Body.LoopFree) : Prop :=
  (loopOnlyMaintVC inv G Body hBody).Valid

/- The termination obligation is valid. -/
def loopOnlyTermValid
    (inv post : AssertExpr D Γ)
    (G : Guard D Γ) : Prop :=
  (loopOnlyTermVC inv post G).Valid

/-
  Maintenance validity for a command recognized as loop-
  only.
-/
def loopOnlyMaintValidOfCmd
    (inv : AssertExpr D Γ)
    (C : Cmd D Γ) : Prop :=
  match C.loopOnlyParts? with
  | some (G, Body) =>
      if hBody : Body.LoopFree then
        loopOnlyMaintValid inv G Body hBody
      else
        False
  | none =>
      False

/-
  Termination validity for a command recognized as loop-
  only.
-/
def loopOnlyTermValidOfCmd
    (inv post : AssertExpr D Γ)
    (C : Cmd D Γ) : Prop :=
  match C.loopOnlyParts? with
  | some (G, _Body) =>
      loopOnlyTermValid inv post G
  | none =>
      False

end Whiel

------------------------------------------------------------
-- Abstract WP Support
------------------------------------------------------------

namespace Whiel

namespace Hoare

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Assignment WP unfolds to the updated post-state. -/
@[simp] theorem wp_assign_iff
    (post : Assertion D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X))
    (I : Instance D Γ) :
    wp (.assign X e) post I ↔
      post (Instance.update I X (e.eval I)) := by
  constructor
  · intro h
    exact h (Instance.update I X (e.eval I))
      (Cmd.BigStep.assign I X e)
  · intro h J hStep
    have hJ :
        J = Instance.update I X (e.eval I) :=
      (Cmd.bigStep_assign_iff I J X e).mp hStep
    rw [hJ]
    exact h

/-
  Pointwise-equivalent postconditions have equivalent
  WPs.
-/
theorem wp_congr
    (C : Cmd D Γ)
    {post post' : Assertion D Γ}
    (hPost : ∀ I : Instance D Γ, post I ↔ post' I)
    (I : Instance D Γ) :
    wp C post I ↔ wp C post' I := by
  constructor
  · intro h J hStep
    exact (hPost J).mp (h J hStep)
  · intro h J hStep
    exact (hPost J).mpr (h J hStep)

/- Assignment SP unfolds to the existence of a pre-state. -/
@[simp] theorem sp_assign_iff
    (pre : Assertion D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X))
    (J : Instance D Γ) :
    sp (.assign X e) pre J ↔
      ∃ I : Instance D Γ,
        pre I ∧ J = Instance.update I X (e.eval I) := by
  constructor
  · rintro ⟨I, hPre, hStep⟩
    exact
      ⟨I, hPre,
        (Cmd.bigStep_assign_iff I J X e).mp hStep⟩
  · rintro ⟨I, hPre, hJ⟩
    refine ⟨I, hPre, ?_⟩
    simp [hJ, Cmd.BigStep.assign I X e]

/-
  Pointwise-equivalent preconditions have equivalent
  SPs.
-/
theorem sp_congr
    (C : Cmd D Γ)
    {pre pre' : Assertion D Γ}
    (hPre : ∀ I : Instance D Γ, pre I ↔ pre' I)
    (J : Instance D Γ) :
    sp C pre J ↔ sp C pre' J := by
  constructor
  · rintro ⟨I, hI, hStep⟩
    exact ⟨I, (hPre I).mp hI, hStep⟩
  · rintro ⟨I, hI, hStep⟩
    exact ⟨I, (hPre I).mpr hI, hStep⟩

end Hoare

end Whiel

------------------------------------------------------------
-- Concrete WP Correctness
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Assignment WP has the expected updated-state
  semantics.
-/
theorem wpAssign_eval_iff
    (post : AssertExpr D Γ)
    (I : Instance D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    (wpAssign post X e).eval I ↔
      post.eval (Instance.update I X (e.eval I)) :=
  substFree_eval_iff post I X e

/-
  Concrete loop-free WP matches the abstract semantic
  WP.
-/
theorem wpLoopFree_eval_iff
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (post : AssertExpr D Γ)
    (I : Instance D Γ) :
    (wpLoopFree C hLoopFree post).eval I ↔
      Hoare.wp C post.eval I := by
  induction C generalizing post I with
  | skip =>
      exact (Hoare.wp_skip_iff post.eval I).symm
  | assign X e =>
      change (wpAssign post X e).eval I ↔
        Hoare.wp (.assign X e) post.eval I
      rw [wpAssign_eval_iff, Hoare.wp_assign_iff]
  | seq C₁ C₂ ih₁ ih₂ =>
      rcases hLoopFree with ⟨hLoopFree₁, hLoopFree₂⟩
      calc
        (wpLoopFree (.seq C₁ C₂)
            ⟨hLoopFree₁, hLoopFree₂⟩ post).eval I
            ↔
          (wpLoopFree C₁ hLoopFree₁
            (wpLoopFree C₂ hLoopFree₂ post)).eval
            I := by
              rfl
        _ ↔
          Hoare.wp C₁
            (wpLoopFree C₂ hLoopFree₂ post).eval I :=
              ih₁ hLoopFree₁
                (wpLoopFree C₂ hLoopFree₂ post) I
        _ ↔
          Hoare.wp C₁ (Hoare.wp C₂ post.eval) I :=
              Hoare.wp_congr C₁
                (fun K => ih₂ hLoopFree₂ post K) I
        _ ↔
          Hoare.wp (.seq C₁ C₂) post.eval I :=
              (Hoare.wp_seq_iff C₁ C₂ post.eval I).symm
  | ite G C₁ C₂ ih₁ ih₂ =>
      rcases hLoopFree with ⟨hLoopFree₁, hLoopFree₂⟩
      calc
        (wpLoopFree (.ite G C₁ C₂)
            ⟨hLoopFree₁, hLoopFree₂⟩ post).eval I
            ↔
          (G.eval I →
            (wpLoopFree C₁ hLoopFree₁ post).eval I) ∧
            (¬ G.eval I →
              (wpLoopFree C₂ hLoopFree₂ post).eval
                I) := by
              simpa [wpLoopFree, wpLoopFreeFormula]
                using
                  formulaIte_eval_iff post.extendsFree G
                    (wpLoopFreeFormula post.extendsFree C₁
                      hLoopFree₁ post.formula)
                    (wpLoopFreeFormula post.extendsFree C₂
                      hLoopFree₂ post.formula) I
        _ ↔
          (G.eval I → Hoare.wp C₁ post.eval I) ∧
            (¬ G.eval I →
              Hoare.wp C₂ post.eval I) := by
              constructor
              · intro h
                exact
                  ⟨fun hG =>
                    (ih₁ hLoopFree₁ post I).mp (h.1 hG),
                   fun hNotG =>
                    (ih₂ hLoopFree₂ post I).mp
                      (h.2 hNotG)⟩
              · intro h
                exact
                  ⟨fun hG =>
                    (ih₁ hLoopFree₁ post I).mpr
                      (h.1 hG),
                   fun hNotG =>
                    (ih₂ hLoopFree₂ post I).mpr
                      (h.2 hNotG)⟩
        _ ↔
          Hoare.wp (.ite G C₁ C₂) post.eval I :=
              (Hoare.wp_ite_iff G C₁ C₂
                post.eval I).symm
  | «while» G C ih =>
      exact False.elim hLoopFree

end AssertExpr

------------------------------------------------------------
-- Quantifier-Free WP Interface
------------------------------------------------------------

namespace QFAssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Weakest precondition for a QF postcondition. -/
def wpLoopFree
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (post : QFAssertExpr D Γ) :
    QFAssertExpr D Γ :=
  AssertExpr.wpLoopFreeFormula
    (UnnamedSchema.extensionOf_refl Γ)
    C hLoopFree post

/- QF loop-free WP matches the abstract semantic WP. -/
theorem wpLoopFree_eval_iff
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (post : QFAssertExpr D Γ)
    (I : Instance D Γ) :
    (wpLoopFree C hLoopFree post).eval I ↔
      Hoare.wp C post.eval I := by
  calc
    (wpLoopFree C hLoopFree post).eval I ↔
        (AssertExpr.ofQF
          (wpLoopFree C hLoopFree post)).eval I :=
      (AssertExpr.ofQF_eval_iff
        (wpLoopFree C hLoopFree post) I).symm
    _ ↔
        (AssertExpr.wpLoopFree C hLoopFree
          (AssertExpr.ofQF post)).eval I := by
      rfl
    _ ↔
        Hoare.wp C
          (AssertExpr.ofQF post).eval I :=
      AssertExpr.wpLoopFree_eval_iff C hLoopFree
        (AssertExpr.ofQF post) I
    _ ↔ Hoare.wp C post.eval I :=
      Hoare.wp_congr C
        (fun J =>
          AssertExpr.ofQF_eval_iff post J) I

/- QF loop-free WP is monotone in its postcondition. -/
theorem wpLoopFree_mono
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    {post post' : QFAssertExpr D Γ}
    (hPost : post.entails post') :
    (wpLoopFree C hLoopFree post).entails
      (wpLoopFree C hLoopFree post') := by
  have hSemantic :
      Assertion.entails post.eval post'.eval := by
    intro I hEval
    exact hPost I hEval
  intro I hWp
  apply (wpLoopFree_eval_iff C hLoopFree post' I).mpr
  exact
    (Hoare.wp_mono C hSemantic) I
      ((wpLoopFree_eval_iff C hLoopFree post I).mp hWp)

/- QF WP commutes pointwise with finite-conjunction formation. -/
theorem wpLoopFree_andList_eval_iff
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (posts : List (QFAssertExpr D Γ))
    (I : Instance D Γ) :
    (wpLoopFree C hLoopFree (andList posts)).eval I ↔
      ∀ post ∈ posts,
        (wpLoopFree C hLoopFree post).eval I := by
  let postEvals := posts.map (fun post => post.eval)
  calc
    (wpLoopFree C hLoopFree (andList posts)).eval I ↔
        Hoare.wp C (andList posts).eval I :=
      wpLoopFree_eval_iff
        C hLoopFree (andList posts) I
    _ ↔ Hoare.wp C
          (Assertion.andList postEvals) I :=
      Hoare.wp_congr C (fun J => by
        simp [postEvals]) I
    _ ↔ ∀ postEval ∈ postEvals,
          Hoare.wp C postEval I :=
      Hoare.wp_andList_apply_iff C postEvals I
    _ ↔ ∀ post ∈ posts,
          (wpLoopFree C hLoopFree post).eval I := by
      constructor
      · intro h post hMem
        apply
          (wpLoopFree_eval_iff
            C hLoopFree post I).mpr
        exact h post.eval
          (List.mem_map.mpr ⟨post, hMem, rfl⟩)
      · intro h postEval hMem
        rcases List.mem_map.mp hMem with
          ⟨post, hPost, rfl⟩
        exact
          (wpLoopFree_eval_iff
            C hLoopFree post I).mp (h post hPost)

/-
  Computed WP commutes semantically with
  finite-conjunction formation.
-/
theorem wpLoopFree_andList_equiv
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (posts : List (QFAssertExpr D Γ)) :
    equiv
      (wpLoopFree C hLoopFree (andList posts))
      (andList (posts.map (wpLoopFree C hLoopFree))) := by
  constructor
  · intro I hWp
    apply
      (andList_eval_iff
        (posts.map (wpLoopFree C hLoopFree)) I).mpr
    intro candidate hMem
    rcases List.mem_map.mp hMem with
      ⟨post, hPost, rfl⟩
    exact
      (wpLoopFree_andList_eval_iff
        C hLoopFree posts I).mp hWp post hPost
  · intro I hWp
    apply
      (wpLoopFree_andList_eval_iff
        C hLoopFree posts I).mpr
    intro post hPost
    exact
      (andList_eval_iff
        (posts.map (wpLoopFree C hLoopFree)) I).mp
          hWp (wpLoopFree C hLoopFree post)
          (List.mem_map.mpr ⟨post, hPost, rfl⟩)

/- QF WP commutes pointwise with finite disjunction. -/
theorem wpLoopFree_orList_eval_iff
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (posts : List (QFAssertExpr D Γ))
    (I : Instance D Γ) :
    (wpLoopFree C hLoopFree (orList posts)).eval I ↔
      ∃ post ∈ posts,
        (wpLoopFree C hLoopFree post).eval I := by
  let postEvals := posts.map (fun post => post.eval)
  calc
    (wpLoopFree C hLoopFree (orList posts)).eval I ↔
        Hoare.wp C (orList posts).eval I :=
      wpLoopFree_eval_iff C hLoopFree (orList posts) I
    _ ↔ Hoare.wp C
          (Assertion.orList postEvals) I :=
      Hoare.wp_congr C (fun J => by
        simp [postEvals, Assertion.orList]) I
    _ ↔ ∃ postEval ∈ postEvals,
          Hoare.wp C postEval I :=
      Hoare.wp_orList_apply_iff C postEvals I
        (Cmd.BigStep.exists_of_loopFree
          C hLoopFree I)
    _ ↔ ∃ post ∈ posts,
          (wpLoopFree C hLoopFree post).eval I := by
      constructor
      · rintro ⟨postEval, hMem, hWp⟩
        rcases List.mem_map.mp hMem with
          ⟨post, hPost, rfl⟩
        exact
          ⟨post, hPost,
            (wpLoopFree_eval_iff
              C hLoopFree post I).mpr hWp⟩
      · rintro ⟨post, hPost, hWp⟩
        exact
          ⟨post.eval,
            List.mem_map.mpr ⟨post, hPost, rfl⟩,
            (wpLoopFree_eval_iff
              C hLoopFree post I).mp hWp⟩

/-
  Computed WP commutes semantically with
  finite-disjunction formation.
-/
theorem wpLoopFree_orList_equiv
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (posts : List (QFAssertExpr D Γ)) :
    equiv
      (wpLoopFree C hLoopFree (orList posts))
      (orList (posts.map (wpLoopFree C hLoopFree))) := by
  constructor
  · intro I hWp
    apply
      (orList_eval_iff
        (posts.map (wpLoopFree C hLoopFree)) I).mpr
    rcases
        (wpLoopFree_orList_eval_iff
          C hLoopFree posts I).mp hWp with
      ⟨post, hPost, hEval⟩
    exact
      ⟨wpLoopFree C hLoopFree post,
        List.mem_map.mpr ⟨post, hPost, rfl⟩,
        hEval⟩
  · intro I hWp
    apply
      (wpLoopFree_orList_eval_iff
        C hLoopFree posts I).mpr
    rcases
        (orList_eval_iff
          (posts.map (wpLoopFree C hLoopFree)) I).mp
          hWp with
      ⟨candidate, hMem, hEval⟩
    rcases List.mem_map.mp hMem with
      ⟨post, hPost, rfl⟩
    exact ⟨post, hPost, hEval⟩

end QFAssertExpr

namespace Hoare

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Assignment WP satisfies the weakest-precondition spec.
-/
theorem wpAssign_wpOf
    (post : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    Assertion.wpOf
      (AssertExpr.wpAssign post X e).eval
      (.assign X e)
      post.eval := by
  constructor
  · intro I J hPre hStep
    have hPost :
        post.eval (Instance.update I X (e.eval I)) :=
      (AssertExpr.wpAssign_eval_iff post I X e).mp hPre
    have hWp : wp (.assign X e) post.eval I :=
      (wp_assign_iff post.eval X e I).mpr hPost
    exact hWp J hStep
  · intro pre hValid I hPre
    have hWp : wp (.assign X e) post.eval I :=
      wp_weakest hValid I hPre
    have hPost :
        post.eval (Instance.update I X (e.eval I)) :=
      (wp_assign_iff post.eval X e I).mp hWp
    exact
      (AssertExpr.wpAssign_eval_iff post I X e).mpr hPost

/-
  The computed loop-free WP is a valid precondition.
-/
theorem wpLoopFree_valid
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (post : AssertExpr D Γ) :
    HoareValid
      (AssertExpr.wpLoopFree C hLoopFree post)
      C post := by
  intro I J hPre hStep
  have hWp : wp C post.eval I :=
    (AssertExpr.wpLoopFree_eval_iff
      C hLoopFree post I).mp hPre
  exact hWp J hStep

/-
  The computed loop-free WP satisfies the
  weakest-precondition spec.
-/
theorem wpLoopFree_wpOf
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (post : AssertExpr D Γ) :
    Assertion.wpOf
      (AssertExpr.wpLoopFree C hLoopFree post).eval
      C
      post.eval := by
  constructor
  · intro I J hPre hStep
    have hWp : wp C post.eval I :=
      (AssertExpr.wpLoopFree_eval_iff C hLoopFree post I).mp
        hPre
    exact hWp J hStep
  · intro pre hValid I hPre
    have hWp : wp C post.eval I :=
      wp_weakest hValid I hPre
    exact
      (AssertExpr.wpLoopFree_eval_iff
        C hLoopFree post I).mpr
        hWp

/-
  Hoare validity is entailment into the computed loop-free
  WP.
-/
theorem hoareValid_iff_entails_wpLoopFree
    (pre : Assertion D Γ)
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (post : AssertExpr D Γ) :
    HoareValid pre C post ↔
      Assertion.entails pre
        (AssertExpr.wpLoopFree C hLoopFree post).eval := by
  change HoareValid pre C (post.eval : Assertion D Γ) ↔
    Assertion.entails pre
      (AssertExpr.wpLoopFree C hLoopFree post).eval
  rw [hoareValid_iff_entails_wp]
  constructor
  · intro hEntails I hPre
    exact
      (AssertExpr.wpLoopFree_eval_iff
        C hLoopFree post I).mpr
        (hEntails I hPre)
  · intro hEntails I hPre
    exact
      (AssertExpr.wpLoopFree_eval_iff C hLoopFree post I).mp
        (hEntails I hPre)

end Hoare

end Whiel

------------------------------------------------------------
-- Concrete SP Proof Support
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Guard conjunction has the expected semantics. -/
theorem andGuard_eval_iff
    (pre : AssertExpr D Γ)
    (G : Guard D Γ)
    (I : Instance D Γ) :
    (andGuard pre G).eval I ↔
      pre.eval I ∧ G.eval I := by
  constructor
  · rintro ⟨J, hM, hFormula⟩
    have hGuard :
        (G.onExtension pre.extendsFree).eval J ↔
          G.eval I :=
      guard_onExtension_eval_of_extends pre.extendsFree G hM
    exact
      ⟨⟨J, hM, hFormula.1⟩,
        hGuard.mp hFormula.2⟩
  · rintro ⟨⟨J, hM, hPre⟩, hG⟩
    have hGuard :
        (G.onExtension pre.extendsFree).eval J ↔
          G.eval I :=
      guard_onExtension_eval_of_extends pre.extendsFree G hM
    exact ⟨J, hM, ⟨hPre, hGuard.mpr hG⟩⟩

/- Negated-guard conjunction has the expected semantics. -/
theorem andNotGuard_eval_iff
    (pre : AssertExpr D Γ)
    (G : Guard D Γ)
    (I : Instance D Γ) :
    (andNotGuard pre G).eval I ↔
      pre.eval I ∧ ¬ G.eval I := by
  constructor
  · rintro ⟨J, hM, hFormula⟩
    have hGuard :
        (G.onExtension pre.extendsFree).eval J ↔
          G.eval I :=
      guard_onExtension_eval_of_extends pre.extendsFree G hM
    exact
      ⟨⟨J, hM, hFormula.1⟩,
        fun hG => hFormula.2 (hGuard.mpr hG)⟩
  · rintro ⟨⟨J, hM, hPre⟩, hNotG⟩
    have hGuard :
        (G.onExtension pre.extendsFree).eval J ↔
          G.eval I :=
      guard_onExtension_eval_of_extends pre.extendsFree G hM
    exact
      ⟨J, hM,
        ⟨hPre, fun hGM => hNotG (hGuard.mp hGM)⟩⟩

/-
  Formula disjunction over one full schema has
  disjunctive semantics.
-/
theorem formulaOr_eval_iff
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (φ ψ : QFAssertExpr D Δ)
    (I : Instance D Γ) :
    (formulaOverExtension hExt (formulaOr φ ψ)).eval I ↔
      (formulaOverExtension hExt φ).eval I ∨
        (formulaOverExtension hExt ψ).eval I := by
  constructor
  · rintro ⟨J, hM, hFormula⟩
    cases hFormula with
    | inl hφ => exact Or.inl ⟨J, hM, hφ⟩
    | inr hψ => exact Or.inr ⟨J, hM, hψ⟩
  · intro h
    cases h with
    | inl hφ =>
        rcases hφ with ⟨J, hM, hFormula⟩
        exact ⟨J, hM, Or.inl hFormula⟩
    | inr hψ =>
        rcases hψ with ⟨J, hM, hFormula⟩
        exact ⟨J, hM, Or.inr hFormula⟩

/-
  Evaluating a relation expression reads the instance
  relation.
-/
theorem ra_eval_rel
    (X : Γ.syms)
    (I : Instance D Γ) :
    (RAExpr.rel X).eval I = I X := by
  have hSpec :=
    RAExpr.raw_eval?_eq_eval
      (RAExpr.rel X : RAExpr D Γ (Γ.arity X)) I
  have hRaw :
      (RAExpr.rel X : RAExpr D Γ (Γ.arity X)).expr.eval?
          (Γ := Γ) I =
        some ⟨Γ.arity X, I X⟩ := by
    simp [RAExpr.rel, RawRAExpr.eval?,
      Instance.relation?, X.2]
  rw [hRaw] at hSpec
  injection hSpec with hSigma
  injection hSigma with _ hRel
  exact hRel.symm

/-
  Lifted RA evaluation agrees with evaluation in the
  reduct.
-/
theorem liftRA_mem_eval_iff_of_extends
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X))
    {I : Instance D Γ}
    {J : Instance D Δ}
    (hM : Instance.Extends hExt I J)
    (t : Tuple D (Γ.arity X)) :
    Tuple.toExtension hExt X t ∈
        (liftRA hExt X e).eval J ↔
      t ∈ e.eval I := by
  have hMem :=
    RAExpr.mem_eval_castArity
      (UnnamedSchema.arity_eq_of_extensionOf hExt X)
      (e.onExtension hExt) J (Tuple.toExtension hExt X t)
  rw [show Tuple.toExtension hExt X t ∈
        (liftRA hExt X e).eval J ↔
          Tuple.castArity
            (UnnamedSchema.arity_eq_of_extensionOf
              hExt X).symm
            (Tuple.toExtension hExt X t) ∈
              (e.onExtension hExt).eval J by
        simpa [liftRA] using hMem]
  letI : Fact (Δ.extensionOf Γ) := ⟨hExt⟩
  have hReduct : Instance.reduct hExt J = I :=
    Instance.reduct_eq_of_extends hExt hM
  have hEval : (e.onExtension hExt).eval J = e.eval I := by
    simpa [hReduct] using RAExpr.reduct_property (e := e) J
  rw [hEval]
  have hCast :
      Tuple.castArity
          (UnnamedSchema.arity_eq_of_extensionOf
            hExt X).symm
          (Tuple.toExtension hExt X t) = t := by
    exact Tuple.castArity_symm
      (UnnamedSchema.arity_eq_of_extensionOf hExt X) t
  simp [hCast]

/-
  Lifted RA evaluation for tuples already typed in the
  extension.
-/
theorem liftRA_mem_eval_iff_of_extends_cast
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X))
    {I : Instance D Γ}
    {J : Instance D Δ}
    (hM : Instance.Extends hExt I J)
    (t : Tuple D
      (Δ.arity (UnnamedSchema.symOfExtension hExt X))) :
    t ∈ (liftRA hExt X e).eval J ↔
      Tuple.castArity
        (UnnamedSchema.arity_eq_of_extension_mem hExt
          (UnnamedSchema.symOfExtension hExt X) X.2) t ∈
        e.eval I := by
  let hOf := UnnamedSchema.arity_eq_of_extensionOf hExt X
  change
    t ∈ (RAExpr.castArity hOf
      (e.onExtension hExt)).eval J ↔
      Tuple.castArity
        (UnnamedSchema.arity_eq_of_extension_mem hExt
          (UnnamedSchema.symOfExtension hExt X) X.2) t ∈
        e.eval I
  letI : Fact (Δ.extensionOf Γ) := ⟨hExt⟩
  have hReduct : Instance.reduct hExt J = I :=
    Instance.reduct_eq_of_extends hExt hM
  have hEval : (e.onExtension hExt).eval J = e.eval I := by
    simpa [hReduct] using RAExpr.reduct_property (e := e) J
  have hTuple :
      Tuple.castArity hOf.symm t =
        Tuple.castArity
          (UnnamedSchema.arity_eq_of_extension_mem hExt
            (UnnamedSchema.symOfExtension hExt X)
            X.2) t := by
    apply Tuple.castArity_proof_irrel
  calc
    t ∈ (RAExpr.castArity hOf (e.onExtension hExt)).eval J
        ↔ Tuple.castArity hOf.symm t ∈
            (e.onExtension hExt).eval J :=
          RAExpr.mem_eval_castArity hOf
            (e.onExtension hExt) J t
    _ ↔ Tuple.castArity
          (UnnamedSchema.arity_eq_of_extension_mem hExt
            (UnnamedSchema.symOfExtension hExt X) X.2) t ∈
          e.eval I := by
          constructor
          · intro ht
            have ht' :
                Tuple.castArity hOf.symm t ∈
                  e.eval I := by
              simpa [hEval] using ht
            simpa [hTuple] using ht'
          · intro ht
            have ht' : Tuple.castArity
                (UnnamedSchema.arity_eq_of_extension_mem
                  hExt
                  (UnnamedSchema.symOfExtension hExt X)
                  X.2) t ∈
                (e.onExtension hExt).eval J := by
              simpa [hEval] using ht
            simpa [hTuple] using ht'

/- Lifted relation reads agree with the smaller instance. -/
theorem rel_symExt_mem_eval_iff_of_extends
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (X : Γ.syms)
    {I : Instance D Γ}
    {J : Instance D Δ}
    (hM : Instance.Extends hExt I J)
    (t : Tuple D (Γ.arity X)) :
    Tuple.toExtension hExt X t ∈
        (RAExpr.rel
          (UnnamedSchema.symOfExtension hExt X)).eval J ↔
      t ∈ I X := by
  rw [ra_eval_rel]
  rw [hM (UnnamedSchema.symOfExtension hExt X) X.2]
  have hMem :=
    Instance.relationOfExtension_mem_iff hExt I
      (UnnamedSchema.symOfExtension hExt X) X.2
      (Tuple.toExtension hExt X t)
  rw [show Tuple.toExtension hExt X t ∈
        Instance.relationOfExtension hExt I
          (UnnamedSchema.symOfExtension hExt X) X.2 ↔
          Tuple.castArity
            (UnnamedSchema.arity_eq_of_extension_mem hExt
              (UnnamedSchema.symOfExtension hExt X) X.2)
            (Tuple.toExtension hExt X t) ∈
              I ⟨(UnnamedSchema.symOfExtension hExt X).1,
                X.2⟩ by
        exact hMem]
  have hCast :
      Tuple.castArity
          (UnnamedSchema.arity_eq_of_extension_mem hExt
            (UnnamedSchema.symOfExtension hExt X) X.2)
          (Tuple.toExtension hExt X t) = t := by
    have h₁ :=
      UnnamedSchema.arity_eq_of_extension_mem hExt
        (UnnamedSchema.symOfExtension hExt X) X.2
    have h₂ :=
      UnnamedSchema.arity_eq_of_extensionOf hExt X
    change Tuple.castArity h₁ (Tuple.castArity h₂ t) = t
    rw [Tuple.castArity_proof_irrel h₁ h₂.symm]
    exact Tuple.castArity_symm h₂ t
  rw [hCast]
  change t ∈ I X ↔ t ∈ I X
  rfl

/-
  Lifted relation reads for tuples already typed in the
  extension.
-/
theorem rel_symExt_mem_eval_iff_of_extends_cast
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (X : Γ.syms)
    {I : Instance D Γ}
    {J : Instance D Δ}
    (hM : Instance.Extends hExt I J)
    (t : Tuple D
      (Δ.arity (UnnamedSchema.symOfExtension hExt X))) :
    t ∈ (RAExpr.rel
        (UnnamedSchema.symOfExtension hExt X)).eval J ↔
      Tuple.castArity
        (UnnamedSchema.arity_eq_of_extension_mem hExt
          (UnnamedSchema.symOfExtension hExt X) X.2) t ∈
        I X := by
  rw [ra_eval_rel]
  rw [hM (UnnamedSchema.symOfExtension hExt X) X.2]
  have hMem :=
    Instance.relationOfExtension_mem_iff hExt I
      (UnnamedSchema.symOfExtension hExt X) X.2 t
  rw [show t ∈
        Instance.relationOfExtension hExt I
          (UnnamedSchema.symOfExtension hExt X) X.2 ↔
        Tuple.castArity
          (UnnamedSchema.arity_eq_of_extension_mem hExt
            (UnnamedSchema.symOfExtension hExt X) X.2) t ∈
          I ⟨(UnnamedSchema.symOfExtension hExt X).1,
            X.2⟩ by
        exact hMem]
  change Tuple.castArity
        (UnnamedSchema.arity_eq_of_extension_mem hExt
          (UnnamedSchema.symOfExtension hExt X) X.2) t ∈
        I X ↔
      Tuple.castArity
        (UnnamedSchema.arity_eq_of_extension_mem hExt
          (UnnamedSchema.symOfExtension hExt X) X.2) t ∈
        I X
  rfl

/-
  Updating an unused relation symbol does not affect RA
  evaluation.
-/
theorem ra_eval_update_of_not_mem
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ)
    (X : Γ.syms)
    (R : FinRelation D (Γ.arity X))
    (hX : X.1 ∉ e.symbols) :
    e.eval (Instance.update I X R) = e.eval I := by
  letI : Fact (Γ.extensionOf e.supportSchema) :=
    ⟨e.extension_supportSchema⟩
  have hRelAgree :
      (Instance.update I X R).agreeOnRelations
        e.supportSchema.syms I := by
    intro Y hY
    have hYsym : Y ∈ e.symbols := by
      simpa using hY
    have hRawNe : Y ≠ X.1 := by
      intro hEq
      exact hX (by simpa [hEq] using hYsym)
    unfold Instance.relation?
    by_cases hYΓ : Y ∈ Γ.syms
    · have hNe : (⟨Y, hYΓ⟩ : Γ.syms) ≠ X := by
        intro hEq
        exact hRawNe (congrArg Subtype.val hEq)
      simp [hYΓ, Instance.update_lookup_ne, hNe]
    · simp [hYΓ]
  have hEval :=
    RAExpr.expansion_invariance
      (e := e)
      (I₁ := Instance.update I X R)
      (I₂ := I)
      (hRelAgree := hRelAgree)
  simpa [RAExpr.onExtension] using hEval

/-
  Updating an unused free relation symbol does not affect
  assertion truth.
-/
theorem eval_update_of_not_mem_formula
    (pre : AssertExpr D Γ)
    (I : Instance D Γ)
    (X : Γ.syms)
    (R : FinRelation D (Γ.arity X))
    (hX : X.1 ∉ pre.formula.symbols) :
    pre.eval (Instance.update I X R) ↔ pre.eval I := by
  have hRelAgree :
      (Instance.update I X R).agreeOnRelations
        pre.freeSymbols I := by
    intro Y hY
    have hYFormula : Y ∈ pre.formula.symbols := by
      have hY' := Finset.mem_inter.mp
        (by
          simpa [AssertExpr.freeSymbols,
            AssertExpr.formulaSymbols] using hY)
      exact hY'.1
    have hRawNe : Y ≠ X.1 := by
      intro hEq
      exact hX (by simpa [hEq] using hYFormula)
    unfold Instance.relation?
    by_cases hYΓ : Y ∈ Γ.syms
    · have hNe : (⟨Y, hYΓ⟩ : Γ.syms) ≠ X := by
        intro hEq
        exact hRawNe (congrArg Subtype.val hEq)
      simp [hYΓ, Instance.update_lookup_ne, hNe]
    · simp [hYΓ]
  have hInv :=
    AssertExpr.expansion_invariance
      (Δ₁ := Γ) (Δ₂ := Γ)
      (φ := pre)
      (I₁ := Instance.update I X R)
      (I₂ := I)
      hRelAgree
  simpa [Instance.reduct_refl] using hInv

/-
  Assignment SP without an old symbol has assignment
  semantics.
-/
theorem spAssignNoOld_eval_iff
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X))
    (J : Instance D Γ)
    (hNeed : ¬ spAssignNeedsOld pre X e) :
    ({ fullSchema := pre.fullSchema,
       extendsFree := pre.extendsFree,
       formula := spAssignNoOldFormula pre X e } :
        AssertExpr D Γ).eval J ↔
      Hoare.sp (.assign X e) pre.eval J := by
  have hPreNo : X.1 ∉ pre.formula.symbols := by
    intro h
    exact hNeed (Or.inl h)
  have hENo : X.1 ∉ e.symbols := by
    intro h
    exact hNeed (Or.inr h)
  constructor
  · rintro ⟨K, hM, hFormula⟩
    rcases hFormula with ⟨hPreFormula, hEqFormula⟩
    have hPreJ : pre.eval J := ⟨K, hM, hPreFormula⟩
    have hXEq : J X = e.eval J := by
      apply Finset.ext
      intro t
      calc
        t ∈ J X
            ↔ Tuple.toExtension pre.extendsFree X t ∈
                (RAExpr.rel
                  (UnnamedSchema.symOfExtension
                    pre.extendsFree X)).eval
                  K := by
              exact
                (rel_symExt_mem_eval_iff_of_extends
                  pre.extendsFree X hM t).symm
        _ ↔ Tuple.toExtension pre.extendsFree X t ∈
                (liftRA pre.extendsFree X e).eval K := by
              rw [hEqFormula]
        _ ↔ t ∈ e.eval J :=
              liftRA_mem_eval_iff_of_extends
                pre.extendsFree X e hM t
    have hUpdate : J = Instance.update J X (e.eval J) := by
      apply Instance.ext
      intro Y
      by_cases hYX : Y = X
      · subst Y
        simp [Instance.update_lookup_eq, hXEq]
      · simp [Instance.update_lookup_ne, hYX]
    rw [Hoare.sp_assign_iff]
    exact ⟨J, hPreJ, hUpdate⟩
  · rw [Hoare.sp_assign_iff]
    rintro ⟨I, hPreI, hJ⟩
    subst hJ
    have hPreUpd :
        pre.eval (Instance.update I X (e.eval I)) := by
      exact
        (eval_update_of_not_mem_formula
          pre I X (e.eval I) hPreNo).mpr hPreI
    rcases hPreUpd with ⟨K, hM, hPreFormula⟩
    refine ⟨K, hM, ?_⟩
    constructor
    · exact hPreFormula
    · apply Finset.ext
      intro t
      have hEvalNo :
          e.eval (Instance.update I X (e.eval I)) =
            e.eval I :=
        ra_eval_update_of_not_mem e I X (e.eval I) hENo
      calc
        t ∈
            (RAExpr.rel
              (UnnamedSchema.symOfExtension
                pre.extendsFree X)).eval K
            ↔ Tuple.castArity
                (UnnamedSchema.arity_eq_of_extension_mem
                  pre.extendsFree
                  (UnnamedSchema.symOfExtension
                    pre.extendsFree X) X.2) t ∈
                (Instance.update I X (e.eval I)) X :=
              rel_symExt_mem_eval_iff_of_extends_cast
                pre.extendsFree X
                hM t
        _ ↔ Tuple.castArity
                (UnnamedSchema.arity_eq_of_extension_mem
                  pre.extendsFree
                  (UnnamedSchema.symOfExtension
                    pre.extendsFree X) X.2) t ∈
                e.eval I := by
              simp [Instance.update_lookup_eq]
        _ ↔ Tuple.castArity
                (UnnamedSchema.arity_eq_of_extension_mem
                  pre.extendsFree
                  (UnnamedSchema.symOfExtension
                    pre.extendsFree X) X.2) t ∈
                e.eval
                  (Instance.update I X (e.eval I)) := by
              rw [hEvalNo]
        _ ↔ t ∈ (liftRA pre.extendsFree X e).eval K :=
              (liftRA_mem_eval_iff_of_extends_cast
                pre.extendsFree X e hM t).symm

/-
  A state satisfying an old-free assignment SP already
  satisfies the precondition and is fixed by the
  assignment.
-/
theorem spAssignNoOld_eval_imp_fixed
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X))
    (J : Instance D Γ)
    (_hNeed : ¬ spAssignNeedsOld pre X e)
    (hEval :
      ({ fullSchema := pre.fullSchema,
         extendsFree := pre.extendsFree,
         formula := spAssignNoOldFormula pre X e } :
          AssertExpr D Γ).eval J) :
    pre.eval J ∧ Cmd.BigStep (.assign X e) J J := by
  rcases hEval with ⟨K, hM, hFormula⟩
  rcases hFormula with ⟨hPreFormula, hEqFormula⟩
  have hPreJ : pre.eval J := ⟨K, hM, hPreFormula⟩
  have hXEq : J X = e.eval J := by
    apply Finset.ext
    intro t
    calc
      t ∈ J X
          ↔ Tuple.toExtension pre.extendsFree X t ∈
              (RAExpr.rel
                (UnnamedSchema.symOfExtension
                  pre.extendsFree X)).eval K := by
            exact
              (rel_symExt_mem_eval_iff_of_extends
                pre.extendsFree X hM t).symm
      _ ↔ Tuple.toExtension pre.extendsFree X t ∈
              (liftRA pre.extendsFree X e).eval K := by
            rw [hEqFormula]
      _ ↔ t ∈ e.eval J :=
            liftRA_mem_eval_iff_of_extends
              pre.extendsFree X e hM t
  have hUpdate : J = Instance.update J X (e.eval J) := by
    apply Instance.ext
    intro Y
    by_cases hYX : Y = X
    · subst Y
      simp [Instance.update_lookup_eq, hXEq]
    · simp [Instance.update_lookup_ne, hYX]
  exact
    ⟨hPreJ,
      (Cmd.bigStep_assign_iff J J X e).mpr hUpdate⟩

/- Supply-free SP has the exact semantic SP meaning. -/
theorem spLoopFreeNoFreshFormula?_eval_iff
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre post : QFAssertExpr D Δ)
    (hResult :
      spLoopFreeNoFreshFormula? hExt C hLoopFree pre =
        some post)
    (J : Instance D Γ) :
    (formulaOverExtension hExt post).eval J ↔
      Hoare.sp C
        (formulaOverExtension hExt pre).eval J := by
  induction C generalizing Δ pre post J with
  | skip =>
      simp only [spLoopFreeNoFreshFormula?,
        Option.some.injEq] at hResult
      subst post
      exact (Hoare.sp_skip_iff _ J).symm
  | assign X e =>
      by_cases hNeed :
          X.1 ∈ pre.symbols ∨ X.1 ∈ e.symbols
      · simp only [spLoopFreeNoFreshFormula?, hNeed,
          ↓reduceIte]
          at hResult
        cases hResult
      · simp only [spLoopFreeNoFreshFormula?, hNeed,
          ↓reduceIte, Option.some.injEq]
          at hResult
        subst post
        let source : AssertExpr D Γ :=
          formulaOverExtension hExt pre
        simpa [source, formulaOverExtension,
          spAssignNeedsOld, spAssignNoOldFormula]
          using
            (spAssignNoOld_eval_iff source X e J
              hNeed)
  | seq C₁ C₂ ih₁ ih₂ =>
      rcases hLoopFree with
        ⟨hLoopFree₁, hLoopFree₂⟩
      simp only [spLoopFreeNoFreshFormula?]
        at hResult
      cases hFirst :
          spLoopFreeNoFreshFormula? hExt C₁
            hLoopFree₁ pre with
      | none =>
          simp [hFirst] at hResult
      | some middle =>
          rw [hFirst] at hResult
          calc
            (formulaOverExtension hExt post).eval J ↔
                Hoare.sp C₂
                  (formulaOverExtension hExt middle).eval
                  J :=
              ih₂ hExt hLoopFree₂ middle post hResult J
            _ ↔ Hoare.sp C₂
                  (Hoare.sp C₁
                    (formulaOverExtension hExt pre).eval)
                  J :=
              Hoare.sp_congr C₂
                (fun I =>
                  ih₁ hExt hLoopFree₁ pre
                    middle hFirst I)
                J
            _ ↔ Hoare.sp (.seq C₁ C₂)
                  (formulaOverExtension hExt pre).eval J :=
              (Hoare.sp_seq_iff C₁ C₂ _ J).symm
  | ite G C₁ C₂ ih₁ ih₂ =>
      rcases hLoopFree with
        ⟨hLoopFree₁, hLoopFree₂⟩
      simp only [spLoopFreeNoFreshFormula?]
        at hResult
      cases hThen :
          spLoopFreeNoFreshFormula? hExt C₁
            hLoopFree₁ (formulaGuardAnd hExt pre G) with
      | none =>
          simp [hThen] at hResult
      | some thenPost =>
          rw [hThen] at hResult
          cases hElse :
              spLoopFreeNoFreshFormula? hExt C₂
                hLoopFree₂
                (formulaNotGuardAnd hExt pre G) with
          | none =>
              simp [hElse] at hResult
          | some elsePost =>
              rw [hElse] at hResult
              injection hResult with hResult
              subst post
              let source : AssertExpr D Γ :=
                formulaOverExtension hExt pre
              calc
                (formulaOverExtension hExt
                    (formulaOr
                      thenPost elsePost)).eval J ↔
                    (formulaOverExtension hExt
                      thenPost).eval J ∨
                    (formulaOverExtension hExt
                      elsePost).eval J :=
                  formulaOr_eval_iff hExt
                    thenPost elsePost J
                _ ↔ Hoare.sp C₁
                      (Assertion.andGuard
                        source.eval G) J ∨
                    Hoare.sp C₂
                      (Assertion.andNotGuard
                        source.eval G) J :=
                  or_congr
                    (by
                      calc
                        (formulaOverExtension hExt
                            thenPost).eval J ↔
                            Hoare.sp C₁
                              (AssertExpr.andGuard
                                source G).eval J := by
                          simpa [source, andGuard,
                            formulaOverExtension] using
                            ih₁ hExt hLoopFree₁
                              (formulaGuardAnd hExt pre G)
                              thenPost hThen J
                        _ ↔ Hoare.sp C₁
                              (Assertion.andGuard
                                source.eval G) J :=
                          Hoare.sp_congr C₁
                            (fun I =>
                              andGuard_eval_iff
                                source G I) J)
                    (by
                      calc
                        (formulaOverExtension hExt
                            elsePost).eval J ↔
                            Hoare.sp C₂
                              (AssertExpr.andNotGuard
                                source G).eval J := by
                          simpa [source, andNotGuard,
                            formulaOverExtension] using
                            ih₂ hExt hLoopFree₂
                              (formulaNotGuardAnd
                                hExt pre G)
                              elsePost hElse J
                        _ ↔ Hoare.sp C₂
                              (Assertion.andNotGuard
                                source.eval G) J :=
                          Hoare.sp_congr C₂
                            (fun I =>
                              andNotGuard_eval_iff
                                source G I) J)
                _ ↔ Hoare.sp (.ite G C₁ C₂)
                      source.eval J :=
                  (Hoare.sp_ite_iff G C₁ C₂
                    source.eval J).symm
  | «while» G C ih =>
      exact False.elim hLoopFree

/- A supply-free SP model is fixed by its command. -/
theorem spLoopFreeNoFreshFormula?_eval_imp_fixed
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre post : QFAssertExpr D Δ)
    (hResult :
      spLoopFreeNoFreshFormula? hExt C hLoopFree pre =
        some post)
    (J : Instance D Γ)
    (hEval : (formulaOverExtension hExt post).eval J) :
    (formulaOverExtension hExt pre).eval J ∧
      Cmd.BigStep C J J := by
  induction C generalizing Δ pre post J with
  | skip =>
      simp only [spLoopFreeNoFreshFormula?,
        Option.some.injEq] at hResult
      subst post
      exact ⟨hEval, Cmd.BigStep.skip J⟩
  | assign X e =>
      by_cases hNeed :
          X.1 ∈ pre.symbols ∨ X.1 ∈ e.symbols
      · simp only [spLoopFreeNoFreshFormula?, hNeed,
          ↓reduceIte]
          at hResult
        cases hResult
      · simp only [spLoopFreeNoFreshFormula?, hNeed,
          ↓reduceIte, Option.some.injEq]
          at hResult
        subst post
        let source : AssertExpr D Γ :=
          formulaOverExtension hExt pre
        simpa [source, formulaOverExtension,
          spAssignNeedsOld, spAssignNoOldFormula]
          using
            (spAssignNoOld_eval_imp_fixed
              source X e J hNeed hEval)
  | seq C₁ C₂ ih₁ ih₂ =>
      rcases hLoopFree with
        ⟨hLoopFree₁, hLoopFree₂⟩
      simp only [spLoopFreeNoFreshFormula?]
        at hResult
      cases hFirst :
          spLoopFreeNoFreshFormula? hExt C₁
            hLoopFree₁ pre with
      | none =>
          simp [hFirst] at hResult
      | some middle =>
          rw [hFirst] at hResult
          have hSecond :=
            ih₂ hExt hLoopFree₂ middle post
              hResult J hEval
          have hFirstFixed :=
            ih₁ hExt hLoopFree₁ pre middle
              hFirst J hSecond.1
          exact
            ⟨hFirstFixed.1,
              Cmd.BigStep.seq hFirstFixed.2 hSecond.2⟩
  | ite G C₁ C₂ ih₁ ih₂ =>
      rcases hLoopFree with
        ⟨hLoopFree₁, hLoopFree₂⟩
      simp only [spLoopFreeNoFreshFormula?]
        at hResult
      cases hThen :
          spLoopFreeNoFreshFormula? hExt C₁
            hLoopFree₁ (formulaGuardAnd hExt pre G) with
      | none =>
          simp [hThen] at hResult
      | some thenPost =>
          rw [hThen] at hResult
          cases hElse :
              spLoopFreeNoFreshFormula? hExt C₂
                hLoopFree₂
                (formulaNotGuardAnd hExt pre G) with
          | none =>
              simp [hElse] at hResult
          | some elsePost =>
              rw [hElse] at hResult
              injection hResult with hResult
              subst post
              have hBranches :=
                (formulaOr_eval_iff hExt
                  thenPost elsePost J).mp hEval
              let source : AssertExpr D Γ :=
                formulaOverExtension hExt pre
              rcases hBranches with hThenEval | hElseEval
              · have hFixed :=
                  ih₁ hExt hLoopFree₁
                    (formulaGuardAnd hExt pre G)
                    thenPost hThen J hThenEval
                have hSourceGuard :
                    source.eval J ∧ G.eval J := by
                  apply
                    (andGuard_eval_iff source G J).mp
                  simpa [source, andGuard,
                    formulaOverExtension] using hFixed.1
                exact
                  ⟨hSourceGuard.1,
                    Cmd.BigStep.ite_true
                      hSourceGuard.2 hFixed.2⟩
              · have hFixed :=
                  ih₂ hExt hLoopFree₂
                    (formulaNotGuardAnd hExt pre G)
                    elsePost hElse J hElseEval
                have hSourceGuard :
                    source.eval J ∧ ¬ G.eval J := by
                  apply
                    (andNotGuard_eval_iff source G J).mp
                  simpa [source, andNotGuard,
                    formulaOverExtension] using hFixed.1
                exact
                  ⟨hSourceGuard.1,
                    Cmd.BigStep.ite_false
                      hSourceGuard.2 hFixed.2⟩
  | «while» G C ih =>
      exact False.elim hLoopFree

/- Checked supply-free SP has exact SP semantics. -/
theorem spLoopFreeNoFresh?_eval_iff
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre post : AssertExpr D Γ)
    (hResult :
      spLoopFreeNoFresh? C hLoopFree pre = some post)
    (J : Instance D Γ) :
    post.eval J ↔ Hoare.sp C pre.eval J := by
  unfold spLoopFreeNoFresh? at hResult
  cases hFormula :
      spLoopFreeNoFreshFormula? pre.extendsFree C
        hLoopFree pre.formula with
  | none =>
      simp [hFormula] at hResult
  | some formula =>
      rw [hFormula] at hResult
      simp only [Option.map_some,
        Option.some.injEq] at hResult
      subst post
      simpa [formulaOverExtension] using
        (spLoopFreeNoFreshFormula?_eval_iff
          pre.extendsFree C hLoopFree pre.formula
          formula hFormula J)

/- Supply-free SP models are command fixed points. -/
theorem spLoopFreeNoFresh?_eval_imp_fixed
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre post : AssertExpr D Γ)
    (hResult :
      spLoopFreeNoFresh? C hLoopFree pre = some post)
    (J : Instance D Γ)
    (hEval : post.eval J) :
    pre.eval J ∧ Cmd.BigStep C J J := by
  unfold spLoopFreeNoFresh? at hResult
  cases hFormula :
      spLoopFreeNoFreshFormula? pre.extendsFree C
        hLoopFree pre.formula with
  | none =>
      simp [hFormula] at hResult
  | some formula =>
      rw [hFormula] at hResult
      simp only [Option.map_some,
        Option.some.injEq] at hResult
      subst post
      simpa [formulaOverExtension] using
        (spLoopFreeNoFreshFormula?_eval_imp_fixed
          pre.extendsFree C hLoopFree pre.formula
          formula hFormula J hEval)

/- Supply-free SP preserves an already bound-free schema. -/
theorem spLoopFreeNoFresh?_noBoundSymbols
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre post : AssertExpr D Γ)
    (hResult :
      spLoopFreeNoFresh? C hLoopFree pre = some post)
    (hPre : pre.NoBoundSymbols) :
    post.NoBoundSymbols := by
  unfold spLoopFreeNoFresh? at hResult
  cases hFormula :
      spLoopFreeNoFreshFormula? pre.extendsFree C
        hLoopFree pre.formula with
  | none =>
      simp [hFormula] at hResult
  | some formula =>
      rw [hFormula] at hResult
      simp only [Option.map_some,
        Option.some.injEq] at hResult
      subst post
      exact hPre

end AssertExpr

end Whiel

------------------------------------------------------------
-- General SP Proof Support with Fresh Names
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Assignment SP with an old symbol implies semantic
  assignment SP.
-/
theorem spAssignOld_eval_imp_sp
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X))
    (J : Instance D Γ) :
    ({ fullSchema := spAssignOldFullSchema pre X,
       extendsFree := spAssignOldExtFree pre X,
       formula := spAssignOldFormula pre X e } :
        AssertExpr D Γ).eval J →
      Hoare.sp (.assign X e) pre.eval J := by
  intro hEval
  rcases hEval with ⟨K, hM, hFormula⟩
  rcases hFormula with ⟨hPreOld, hEq⟩
  let hFull := spAssignOldExtFull pre X
  let hFree := spAssignOldExtFree pre X
  let Xtarget := spAssignOldTarget pre X
  let Xold := spAssignOldRel pre X
  let Mpre := Instance.update K Xtarget (Xold.eval K)
  let I := Instance.reduct hFree Mpre
  have hMpreExt : Instance.Extends hFree I Mpre := by
    apply Instance.extends_of_reduct_eq hFree
    rfl
  have hPreExt :
      Instance.Extends pre.extendsFree I
        (Instance.reduct hFull Mpre) := by
    apply Instance.extends_of_reduct_eq pre.extendsFree
    calc
      Instance.reduct pre.extendsFree
          (Instance.reduct hFull Mpre) =
          Instance.reduct hFree Mpre := by
            simpa [hFull, hFree] using
              (Instance.reduct_trans
                hFull pre.extendsFree Mpre)
      _ = I := rfl
  have hPreFormulaExtended :
      (pre.formula.onExtension hFull).eval Mpre := by
    have hSub :=
      QFAssertExpr.subst_eval K Xtarget Xold
        (pre.formula.onExtension hFull)
    exact hSub.mp hPreOld
  have hPreFormula :
      pre.formula.eval (Instance.reduct hFull Mpre) := by
    letI : Fact ((spAssignOldFullSchema pre X).extensionOf
        pre.fullSchema) := ⟨hFull⟩
    exact
      (Guard.onExtension_eval_reduct
        (Γ := spAssignOldFullSchema pre X)
        (Δ := pre.fullSchema)
        pre.formula Mpre
          (Instance.reduct hFull Mpre) rfl).mp
        hPreFormulaExtended
  have hPreI : pre.eval I :=
    ⟨Instance.reduct hFull Mpre, hPreExt, hPreFormula⟩
  have hAssigned : J X = e.eval I := by
    apply Finset.ext
    intro t
    calc
      t ∈ J X
          ↔ Tuple.toExtension hFree X t ∈
              (RAExpr.rel Xtarget).eval K := by
            exact
              (rel_symExt_mem_eval_iff_of_extends
                hFree X hM t).symm
      _ ↔ Tuple.toExtension hFree X t ∈
              ((liftRA hFree X e).subst Xtarget Xold).eval
                K := by
            have hEq' :
                (RAExpr.rel Xtarget).eval K =
                  ((liftRA hFree X e).subst
                    Xtarget Xold).eval K := by
              simpa [hFree, Xtarget, Xold] using hEq
            rw [hEq']
            rfl
      _ ↔ Tuple.toExtension hFree X t ∈
              (liftRA hFree X e).eval Mpre := by
            have hSub :
                ((liftRA hFree X e).subst Xtarget Xold).eval
                    K =
                  (liftRA hFree X e).eval Mpre := by
              simpa [Mpre, Xtarget, Xold] using
                (RAExpr.subst_eval
                  (liftRA hFree X e) K Xtarget Xold)
            rw [hSub]
      _ ↔ t ∈ e.eval I :=
            liftRA_mem_eval_iff_of_extends
              hFree X e hMpreExt t
  have hJUpdate : J = Instance.update I X (e.eval I) := by
    apply Instance.ext
    intro Y
    by_cases hYX : Y = X
    · subst Y
      simp [Instance.update_lookup_eq, hAssigned]
    · apply Finset.ext
      intro t
      have hRawNe : Y.1 ≠ X.1 := by
        intro hRaw
        exact hYX (Subtype.ext hRaw)
      have hLiftNe :
          UnnamedSchema.symOfExtension hFree Y ≠
            Xtarget := by
        intro hEq
        exact hRawNe
          (congrArg
            (fun Z :
              (spAssignOldFullSchema pre X).syms => Z.1)
            hEq)
      calc
        t ∈ J Y
            ↔ Tuple.toExtension hFree Y t ∈
                (RAExpr.rel
                  (UnnamedSchema.symOfExtension
                    hFree Y)).eval K := by
              exact
                (rel_symExt_mem_eval_iff_of_extends
                  hFree Y hM t).symm
        _ ↔ Tuple.toExtension hFree Y t ∈
                (RAExpr.rel
                  (UnnamedSchema.symOfExtension
                    hFree Y)).eval Mpre := by
              rw [ra_eval_rel]
              rw [ra_eval_rel]
              simp [Mpre, Instance.update_lookup_ne,
                hLiftNe]
        _ ↔ t ∈ I Y :=
              rel_symExt_mem_eval_iff_of_extends
                hFree Y hMpreExt t
        _ ↔ t ∈ (Instance.update I X (e.eval I)) Y := by
              simp [Instance.update_lookup_ne, hYX]
  rw [Hoare.sp_assign_iff]
  exact ⟨I, hPreI, hJUpdate⟩

/-
  Semantic assignment SP implies assignment SP with an old
  symbol.
-/
theorem spAssignOld_sp_imp_eval
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X))
    (J : Instance D Γ) :
    Hoare.sp (.assign X e) pre.eval J →
    ({ fullSchema := spAssignOldFullSchema pre X,
       extendsFree := spAssignOldExtFree pre X,
       formula := spAssignOldFormula pre X e } :
        AssertExpr D Γ).eval J := by
  rw [Hoare.sp_assign_iff]
  rintro ⟨I, hPreI, hJ⟩
  subst hJ
  rcases hPreI with ⟨N, hN, hPreFormula⟩
  let hFull := spAssignOldExtFull pre X
  let hFree := spAssignOldExtFree pre X
  let Xtarget := spAssignOldTarget pre X
  let XoldSym := spAssignOldSymbol pre X
  let Xold := spAssignOldRel pre X
  let Jpost := Instance.update I X (e.eval I)
  let M0 := Instance.expandEmpty hFull N
  let oldR :
      FinRelation D
        ((spAssignOldFullSchema pre X).arity
          XoldSym) :=
    cast
      (congrArg (FinRelation D)
        (by
          have hTarget :
              (spAssignOldFullSchema pre X).arity Xtarget =
                Γ.arity X :=
            UnnamedSchema.arity_eq_of_extensionOf hFree X
          have hOld :
              (spAssignOldFullSchema pre X).arity XoldSym =
                Γ.arity X := by
            simp [XoldSym, spAssignOldSymbol,
              spAssignOldFullSchema]
          exact hTarget.trans hOld.symm))
      (M0 Xtarget)
  let M1 := Instance.update M0 XoldSym oldR
  let postR :
      FinRelation D
        ((spAssignOldFullSchema pre X).arity
          Xtarget) :=
    Instance.relationOfExtension hFree Jpost Xtarget X.2
  let J := Instance.update M1 Xtarget postR
  have hOldNeTarget : XoldSym ≠ Xtarget := by
    intro hEq
    have hRaw : spAssignOldName pre X = X.1 := by
      simpa [XoldSym, Xtarget, spAssignOldSymbol,
        spAssignOldTarget, UnnamedSchema.symOfExtension,
        UnnamedSchema.symOfExtension] using
        congrArg
          (fun Z :
            (spAssignOldFullSchema pre X).syms => Z.1)
          hEq
    have hXFull : X.1 ∈ pre.fullSchema.syms :=
      pre.extendsFree.1 X.2
    exact spAssignOldName_fresh pre X
      (by simpa [hRaw] using hXFull)
  have hMExt : Instance.Extends hFree Jpost J := by
    intro Y hY
    by_cases hYX : Y = Xtarget
    · subst Y
      simp [J, Instance.update_lookup_eq, postR]
    · have hOldNeY : Y ≠ XoldSym := by
        intro hEq
        have hRaw0 : Y.1 = XoldSym.1 := by
          exact congrArg
            (fun Z :
              (spAssignOldFullSchema pre X).syms => Z.1)
            hEq
        have hRaw : Y.1 = spAssignOldName pre X := by
          simpa [XoldSym, spAssignOldSymbol,
            UnnamedSchema.insertedSym] using hRaw0
        have hFresh := spAssignOldName_fresh pre X
        have hYFull : Y.1 ∈ pre.fullSchema.syms :=
          pre.extendsFree.1 hY
        exact hFresh (by simpa [hRaw] using hYFull)
      apply Finset.ext
      intro t
      have hMY : J Y = M0 Y := by
        simp [J, M1, Instance.update_lookup_ne,
          hYX, hOldNeY]
      rw [hMY]
      have hYPre : Y.1 ∈ pre.fullSchema.syms :=
        pre.extendsFree.1 hY
      have hYBaseNe : (⟨Y.1, hY⟩ : Γ.syms) ≠ X := by
        intro hEq
        apply hYX
        have hRaw : Y.1 = X.1 := by
          exact congrArg (fun Z : Γ.syms => Z.1) hEq
        exact Subtype.ext hRaw
      have hM0Mem :=
        Instance.expandEmpty_mem_iff_of_mem
          hFull N Y hYPre t
      have hRhsMem :=
        Instance.relationOfExtension_mem_iff
          hFree Jpost Y hY t
      rw [hM0Mem, hRhsMem]
      rw [hN ⟨Y.1, hYPre⟩ hY]
      have hNRelMem :=
        Instance.relationOfExtension_mem_iff
          pre.extendsFree I
          ⟨Y.1, hYPre⟩ hY
          (Tuple.castArity
            (UnnamedSchema.arity_eq_of_extension_mem
              hFull Y hYPre) t)
      rw [hNRelMem]
      simp [Jpost, Instance.update_lookup_ne, hYBaseNe]
      have hCast :
          Tuple.castArity
              (UnnamedSchema.arity_eq_of_extension_mem
                pre.extendsFree ⟨Y.1, hYPre⟩ hY)
              (Tuple.castArity
                (UnnamedSchema.arity_eq_of_extension_mem
                  hFull Y hYPre) t) =
            Tuple.castArity
              (UnnamedSchema.arity_eq_of_extension_mem
                hFree Y hY) t := by
        rw [Tuple.castArity_trans]
      simp [hCast]
  have hOldEvalM : Xold.eval J = M0 Xtarget := by
    apply Finset.ext
    intro t
    unfold Xold spAssignOldRel RAExpr.relAs
    have hTarget :
        (spAssignOldFullSchema pre X).arity Xtarget =
          Γ.arity X :=
      UnnamedSchema.arity_eq_of_extensionOf hFree X
    have hOld :
        (spAssignOldFullSchema pre X).arity XoldSym =
          Γ.arity X := by
      simp [XoldSym, spAssignOldSymbol,
        spAssignOldFullSchema]
    let hAr :
        (spAssignOldFullSchema pre X).arity Xtarget =
          (spAssignOldFullSchema pre X).arity XoldSym :=
      hTarget.trans hOld.symm
    change t ∈ (RAExpr.castArity hAr
          (RAExpr.rel XoldSym)).eval J ↔
      t ∈ M0 Xtarget
    have hMem :=
      RAExpr.mem_eval_castArity hAr (RAExpr.rel XoldSym) J t
    rw [hMem]
    rw [ra_eval_rel]
    have hMXold : J XoldSym = oldR := by
      simp [J, M1, Instance.update_lookup_ne, hOldNeTarget]
    rw [hMXold]
    have hCastMem :=
      FinRelation.mem_cast_iff hAr (M0 Xtarget)
        (Tuple.castArity hAr.symm t)
    rw [hCastMem]
    have hTuple :
        Tuple.castArity hAr (Tuple.castArity hAr.symm t) =
          t := by
      exact Tuple.castArity_symm hAr.symm t
    simp [hTuple]
  let Mpre := Instance.update J Xtarget (Xold.eval J)
  have hMpreEq : Mpre = M1 := by
    have hTargetNeOld : Xtarget ≠ XoldSym :=
      Ne.symm hOldNeTarget
    have hM1Xtarget : M1 Xtarget = M0 Xtarget := by
      simp [M1, Instance.update_lookup_ne, hTargetNeOld]
    simpa [Mpre, J, hOldEvalM,
      Instance.update_shadowing, hM1Xtarget.symm] using
      Instance.update_cancel Xtarget M1
  have hReductFull : Instance.reduct hFull Mpre = N := by
    rw [hMpreEq]
    calc
      Instance.reduct hFull M1 =
          Instance.reduct hFull M0 := by
            exact Instance.reduct_update_of_not_mem
              hFull M0 XoldSym oldR
              (spAssignOldName_fresh pre X)
      _ = N := by
            simp [M0, Instance.reduct_expandEmpty]
  have hReductFree : Instance.reduct hFree Mpre = I := by
    calc
      Instance.reduct hFree Mpre =
          Instance.reduct pre.extendsFree
            (Instance.reduct hFull Mpre) := by
            simpa [hFull, hFree] using
              (Instance.reduct_trans
                hFull pre.extendsFree Mpre).symm
      _ = Instance.reduct pre.extendsFree N := by
            rw [hReductFull]
      _ = I := Instance.reduct_eq_of_extends
            pre.extendsFree hN
  refine ⟨J, hMExt, ?_⟩
  constructor
  · have hMpreFormula :
        (pre.formula.onExtension hFull).eval Mpre := by
      letI : Fact ((spAssignOldFullSchema pre X).extensionOf
          pre.fullSchema) := ⟨hFull⟩
      exact
        (Guard.onExtension_eval_reduct
          (Γ := spAssignOldFullSchema pre X)
          (Δ := pre.fullSchema)
          pre.formula Mpre N hReductFull).mpr hPreFormula
    have hSub :=
      QFAssertExpr.subst_eval J Xtarget Xold
        (pre.formula.onExtension hFull)
    exact hSub.mpr (by simpa [Mpre] using hMpreFormula)
  · apply Finset.ext
    intro t
    have hSub :
        ((liftRA hFree X e).subst Xtarget Xold).eval J =
          (liftRA hFree X e).eval Mpre := by
      simpa [Mpre, Xtarget, Xold] using
        (RAExpr.subst_eval
          (liftRA hFree X e) J Xtarget Xold)
    calc
      t ∈ (RAExpr.rel Xtarget).eval J
          ↔ Tuple.castArity
              (UnnamedSchema.arity_eq_of_extension_mem
                hFree Xtarget X.2) t ∈
              Jpost X :=
            rel_symExt_mem_eval_iff_of_extends_cast
              hFree X hMExt t
      _ ↔ Tuple.castArity
              (UnnamedSchema.arity_eq_of_extension_mem
                hFree Xtarget X.2) t ∈
              e.eval I := by
            simp [Jpost, Instance.update_lookup_eq]
      _ ↔ Tuple.castArity
              (UnnamedSchema.arity_eq_of_extension_mem
                hFree Xtarget X.2) t ∈
              e.eval (Instance.reduct hFree Mpre) := by
            rw [hReductFree]
      _ ↔ t ∈ (liftRA hFree X e).eval Mpre :=
            (liftRA_mem_eval_iff_of_extends_cast
              hFree X e
              (Instance.extends_of_reduct_eq
                hFree rfl) t).symm
      _ ↔ t ∈
            ((liftRA hFree X e).subst Xtarget Xold).eval
              J := by
            rw [hSub]

/-
  Assignment SP with an old symbol has assignment semantics.
-/
theorem spAssignOld_eval_iff
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X))
    (J : Instance D Γ) :
    ({ fullSchema := spAssignOldFullSchema pre X,
       extendsFree := spAssignOldExtFree pre X,
       formula := spAssignOldFormula pre X e } :
        AssertExpr D Γ).eval J ↔
      Hoare.sp (.assign X e) pre.eval J :=
  ⟨spAssignOld_eval_imp_sp pre X e J,
    spAssignOld_sp_imp_eval pre X e J⟩

end AssertExpr

end Whiel

------------------------------------------------------------
-- Concrete SP Correctness
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Assignment SP matches the abstract semantic SP. -/
theorem spAssign_eval_iff
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X))
    (J : Instance D Γ) :
    (spAssign pre X e).eval J ↔
      Hoare.sp (.assign X e) pre.eval J := by
  by_cases hNeed : spAssignNeedsOld pre X e
  · dsimp [spAssign]
    rw [if_pos hNeed]
    exact spAssignOld_eval_iff pre X e J
  · dsimp [spAssign]
    rw [if_neg hNeed]
    exact spAssignNoOld_eval_iff pre X e J hNeed

/-
  Concrete loop-free SP matches the abstract semantic SP.
-/
theorem spLoopFreeResult_eval_iff
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre : AssertExpr D Γ)
    (J : Instance D Γ) :
    (spLoopFreeResult C hLoopFree pre).post.eval J ↔
      Hoare.sp C pre.eval J := by
  induction C generalizing pre J with
  | skip =>
      exact (Hoare.sp_skip_iff pre.eval J).symm
  | assign X e =>
      simpa [spLoopFreeResult, spAssignResult] using
        spAssign_eval_iff pre X e J
  | seq C₁ C₂ ih₁ ih₂ =>
      rcases hLoopFree with ⟨hLoopFree₁, hLoopFree₂⟩
      let r₁ := spLoopFreeResult C₁ hLoopFree₁ pre
      calc
        (spLoopFreeResult (.seq C₁ C₂)
            ⟨hLoopFree₁, hLoopFree₂⟩ pre).post.eval
            J
            ↔
          Hoare.sp C₂ r₁.post.eval J :=
            ih₂ hLoopFree₂ r₁.post J
        _ ↔
          Hoare.sp C₂ (Hoare.sp C₁ pre.eval) J :=
            Hoare.sp_congr C₂
              (fun K => ih₁ hLoopFree₁ pre K) J
        _ ↔
          Hoare.sp (.seq C₁ C₂) pre.eval J :=
            (Hoare.sp_seq_iff C₁ C₂ pre.eval J).symm
  | ite G C₁ C₂ ih₁ ih₂ =>
      rcases hLoopFree with ⟨hLoopFree₁, hLoopFree₂⟩
      let preThen := andGuard pre G
      let preElse := andNotGuard pre G
      let rThen :=
        spLoopFreeResult C₁ hLoopFree₁ preThen
      let hThenExt :
          rThen.post.fullSchema.extensionOf
            pre.fullSchema := by
        simpa [preThen, andGuard] using rThen.extendsFull
      let preElseLift := preElse.liftFull
        (by simpa [preElse, andNotGuard] using hThenExt)
      let rElse :=
        spLoopFreeResult C₂ hLoopFree₂ preElseLift
      let hElseExt :
          rElse.post.fullSchema.extensionOf
            rThen.post.fullSchema := by
        simpa [preElseLift, AssertExpr.liftFull] using
          rElse.extendsFull
      let thenLift := rThen.post.liftFull hElseExt
      have hFinal :
          (spLoopFreeResult (.ite G C₁ C₂)
            ⟨hLoopFree₁, hLoopFree₂⟩ pre).post.eval
              J ↔
            thenLift.eval J ∨ rElse.post.eval J := by
        constructor
        · rintro ⟨K, hM, hFormula⟩
          dsimp [spLoopFreeResult] at hM hFormula
          cases hFormula with
          | inl hThenFormula =>
              let thenAlt : AssertExpr D Γ :=
                { fullSchema := rElse.post.fullSchema,
                  extendsFree := rElse.post.extendsFree,
                  formula := thenLift.formula }
              have hThenAlt : thenAlt.eval J := by
                exact ⟨K, hM, hThenFormula⟩
              have hIrrel :=
                eval_extendsFree_irrel
                  rElse.post.extendsFree
                  thenLift.extendsFree thenLift.formula J
              exact Or.inl (hIrrel.mp hThenAlt)
          | inr hElseFormula =>
              exact Or.inr ⟨K, hM, hElseFormula⟩
        · intro h
          cases h with
          | inl hThen =>
              let thenAlt : AssertExpr D Γ :=
                { fullSchema := rElse.post.fullSchema,
                  extendsFree := rElse.post.extendsFree,
                  formula := thenLift.formula }
              have hIrrel :=
                eval_extendsFree_irrel thenLift.extendsFree
                  rElse.post.extendsFree thenLift.formula J
              have hThenAlt : thenAlt.eval J :=
                hIrrel.mp hThen
              rcases hThenAlt with ⟨K, hM, hFormula⟩
              exact ⟨K, hM, Or.inl hFormula⟩
          | inr hElse =>
              rcases hElse with ⟨K, hM, hFormula⟩
              exact ⟨K, hM, Or.inr hFormula⟩
      have hThen :
          thenLift.eval J ↔
            Hoare.sp C₁
              (Assertion.andGuard pre.eval G) J := by
        calc
          thenLift.eval J
              ↔ rThen.post.eval J :=
                liftFull_eval_iff rThen.post hElseExt J
          _ ↔ Hoare.sp C₁ preThen.eval J :=
                ih₁ hLoopFree₁ preThen J
          _ ↔ Hoare.sp C₁
                (Assertion.andGuard pre.eval G) J :=
                Hoare.sp_congr C₁
                  (fun K => andGuard_eval_iff pre G K) J
      have hElse :
          rElse.post.eval J ↔
            Hoare.sp C₂
              (Assertion.andNotGuard pre.eval G) J := by
        calc
          rElse.post.eval J
              ↔ Hoare.sp C₂ preElseLift.eval J :=
                ih₂ hLoopFree₂ preElseLift J
          _ ↔ Hoare.sp C₂ preElse.eval J :=
                Hoare.sp_congr C₂
                  (fun K =>
                    liftFull_eval_iff preElse hThenExt K) J
          _ ↔ Hoare.sp C₂
                (Assertion.andNotGuard pre.eval G) J :=
                Hoare.sp_congr C₂
                  (fun K => andNotGuard_eval_iff pre G K) J
      calc
        (spLoopFreeResult (.ite G C₁ C₂)
            ⟨hLoopFree₁, hLoopFree₂⟩ pre).post.eval
            J ↔
          thenLift.eval J ∨ rElse.post.eval J := hFinal
        _ ↔
          Hoare.sp C₁
              (Assertion.andGuard pre.eval G) J ∨
            Hoare.sp C₂
              (Assertion.andNotGuard pre.eval G) J :=
              or_congr hThen hElse
        _ ↔
          Hoare.sp (.ite G C₁ C₂) pre.eval J :=
            (Hoare.sp_ite_iff G C₁ C₂ pre.eval J).symm
  | «while» G C ih =>
      exact False.elim hLoopFree

/-
  Concrete loop-free SP matches the abstract semantic SP.
-/
theorem spLoopFree_eval_iff
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre : AssertExpr D Γ)
    (J : Instance D Γ) :
    (spLoopFree C hLoopFree pre).eval J ↔
      Hoare.sp C pre.eval J :=
  spLoopFreeResult_eval_iff C hLoopFree pre J

/-
  If a computed loop-free SP introduces no bound relation,
  each satisfying state is a source state fixed by the
  command.
-/
theorem spLoopFree_eval_imp_fixed
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre : AssertExpr D Γ)
    (J : Instance D Γ)
    (hNo : (spLoopFree C hLoopFree pre).NoBoundSymbols)
    (hEval : (spLoopFree C hLoopFree pre).eval J) :
    pre.eval J ∧ Cmd.BigStep C J J := by
  have noBound_of_ext :
      ∀ (φ ψ : AssertExpr D Γ),
        ψ.fullSchema.extensionOf φ.fullSchema →
          ψ.NoBoundSymbols → φ.NoBoundSymbols := by
    intro φ ψ hExt hNoψ
    unfold NoBoundSymbols boundSymbols
    apply Finset.sdiff_eq_empty_iff_subset.mpr
    intro X hX
    exact ψ.fullSchema_syms_subset_free hNoψ
      (hExt.1 hX)
  induction C generalizing pre J with
  | skip =>
      exact ⟨hEval, Cmd.BigStep.skip J⟩
  | assign X e =>
      by_cases hNeed : spAssignNeedsOld pre X e
      · have hFreshFull :
            spAssignOldName pre X ∈
              (spLoopFree (.assign X e) hLoopFree pre).fullSchema.syms := by
          simp [spLoopFree, spLoopFreeResult,
            spAssignResult, spAssign, hNeed,
            spAssignOldFullSchema,
            UnnamedSchema.insertFresh]
        have hFreshSubset :=
          fullSchema_syms_subset_free
            (spLoopFree (.assign X e) hLoopFree pre) hNo
        have hFreshFree : spAssignOldName pre X ∈ Γ.syms :=
          hFreshSubset hFreshFull
        exact False.elim
          (spAssignOldName_fresh pre X
            (pre.extendsFree.1 hFreshFree))
      · have hEvalNoOld :
            ({ fullSchema := pre.fullSchema,
               extendsFree := pre.extendsFree,
               formula := spAssignNoOldFormula pre X e } :
                AssertExpr D Γ).eval J := by
          simpa [spLoopFree, spLoopFreeResult,
            spAssignResult, spAssign, hNeed] using hEval
        exact
          spAssignNoOld_eval_imp_fixed
            pre X e J hNeed hEvalNoOld
  | seq C₁ C₂ ih₁ ih₂ =>
      rcases hLoopFree with ⟨hLoopFree₁, hLoopFree₂⟩
      let r₁ := spLoopFreeResult C₁ hLoopFree₁ pre
      let r₂ := spLoopFreeResult C₂ hLoopFree₂ r₁.post
      have hNo₂ : r₂.post.NoBoundSymbols := by
        exact hNo
      have hEval₂ : r₂.post.eval J := by
        exact hEval
      have hFixed₂ :=
        ih₂ hLoopFree₂ r₁.post J hNo₂ hEval₂
      have hNo₁ : r₁.post.NoBoundSymbols :=
        noBound_of_ext r₁.post r₂.post
          r₂.extendsFull hNo₂
      have hFixed₁ :=
        ih₁ hLoopFree₁ pre J hNo₁ hFixed₂.1
      exact
        ⟨hFixed₁.1,
          Cmd.BigStep.seq hFixed₁.2 hFixed₂.2⟩
  | ite G C₁ C₂ ih₁ ih₂ =>
      rcases hLoopFree with ⟨hLoopFree₁, hLoopFree₂⟩
      let preThen := andGuard pre G
      let preElse := andNotGuard pre G
      let rThen :=
        spLoopFreeResult C₁ hLoopFree₁ preThen
      let hThenExt :
          rThen.post.fullSchema.extensionOf
            pre.fullSchema := by
        simpa [preThen, andGuard] using rThen.extendsFull
      let preElseLift := preElse.liftFull
        (by simpa [preElse, andNotGuard] using hThenExt)
      let rElse :=
        spLoopFreeResult C₂ hLoopFree₂ preElseLift
      let hElseExt :
          rElse.post.fullSchema.extensionOf
            rThen.post.fullSchema := by
        simpa [preElseLift, AssertExpr.liftFull] using
          rElse.extendsFull
      let thenLift := rThen.post.liftFull hElseExt
      have hSplit :
          (spLoopFree (.ite G C₁ C₂)
              ⟨hLoopFree₁, hLoopFree₂⟩ pre).eval J ↔
            thenLift.eval J ∨ rElse.post.eval J := by
        constructor
        · rintro ⟨K, hM, hFormula⟩
          dsimp [spLoopFree, spLoopFreeResult] at hM hFormula
          cases hFormula with
          | inl hThenFormula =>
              let thenAlt : AssertExpr D Γ :=
                { fullSchema := rElse.post.fullSchema,
                  extendsFree := rElse.post.extendsFree,
                  formula := thenLift.formula }
              have hThenAlt : thenAlt.eval J := by
                exact ⟨K, hM, hThenFormula⟩
              have hIrrel :=
                eval_extendsFree_irrel
                  rElse.post.extendsFree
                  thenLift.extendsFree thenLift.formula J
              exact Or.inl (hIrrel.mp hThenAlt)
          | inr hElseFormula =>
              exact Or.inr ⟨K, hM, hElseFormula⟩
        · intro h
          cases h with
          | inl hThen =>
              let thenAlt : AssertExpr D Γ :=
                { fullSchema := rElse.post.fullSchema,
                  extendsFree := rElse.post.extendsFree,
                  formula := thenLift.formula }
              have hIrrel :=
                eval_extendsFree_irrel thenLift.extendsFree
                  rElse.post.extendsFree thenLift.formula J
              have hThenAlt : thenAlt.eval J :=
                hIrrel.mp hThen
              rcases hThenAlt with ⟨K, hM, hFormula⟩
              exact ⟨K, hM, Or.inl hFormula⟩
          | inr hElse =>
              rcases hElse with ⟨K, hM, hFormula⟩
              exact ⟨K, hM, Or.inr hFormula⟩
      have hNoThen : rThen.post.NoBoundSymbols := by
        apply noBound_of_ext rThen.post
          (spLoopFree (.ite G C₁ C₂)
            ⟨hLoopFree₁, hLoopFree₂⟩ pre)
        · exact hElseExt
        · exact hNo
      have hNoElse : rElse.post.NoBoundSymbols := by
        exact hNo
      rcases hSplit.mp hEval with hThen | hElse
      · have hThenPost : rThen.post.eval J :=
          (liftFull_eval_iff rThen.post hElseExt J).mp hThen
        have hFixedThen :=
          ih₁ hLoopFree₁ preThen J hNoThen hThenPost
        have hPreGuard :=
          (andGuard_eval_iff pre G J).mp hFixedThen.1
        exact
          ⟨hPreGuard.1,
            Cmd.BigStep.ite_true hPreGuard.2 hFixedThen.2⟩
      · have hFixedElse :=
          ih₂ hLoopFree₂ preElseLift J hNoElse hElse
        have hPreElse : preElse.eval J :=
          (liftFull_eval_iff preElse hThenExt J).mp
            hFixedElse.1
        have hPreGuard :=
          (andNotGuard_eval_iff pre G J).mp hPreElse
        exact
          ⟨hPreGuard.1,
            Cmd.BigStep.ite_false hPreGuard.2 hFixedElse.2⟩
  | «while» G C ih =>
      exact False.elim hLoopFree

end AssertExpr

end Whiel

------------------------------------------------------------
-- Loop-Only Invariant Hoare Theorems
------------------------------------------------------------

namespace Whiel

namespace Hoare

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

open AssertExpr
open Assertion

/-
  Three assertion entailments prove a loop-only Hoare
  triple.
-/
theorem hoareValid_loopOnly_of_vcs
    (pre post inv : AssertExpr D Γ)
    (G : Guard D Γ)
    (Body : Cmd D Γ)
    (hBody : Body.LoopFree)
    (hInit : pre.entails inv)
    (hMaint :
      (andGuard inv G).entails
        (wpLoopFree Body hBody inv))
    (hTerm :
      (andNotGuard inv G).entails post) :
    HoareValid pre (.while G Body) post := by
  have hInitAbs :
      entails pre.eval inv.eval := hInit
  have hMaintAbs :
      entails
        (andGuard inv.eval G)
        (Hoare.wp Body inv.eval) := by
    intro I hI
    have hAnd :
        (andGuard inv G).eval I :=
      (andGuard_eval_iff inv G I).mpr hI
    have hWP :
        (wpLoopFree Body hBody inv).eval I :=
      hMaint I hAnd
    exact
      (wpLoopFree_eval_iff Body hBody inv I).mp hWP
  have hTermAbs :
      entails
        (andNotGuard inv.eval G)
        post.eval := by
    intro I hI
    exact hTerm I
      ((andNotGuard_eval_iff inv G I).mpr hI)
  exact
    Hoare.hoareValid_while_of_vcs
      hInitAbs hMaintAbs hTermAbs

/-
  Generated loop-only invariant VCs prove the loop-only
  Hoare triple.
-/
theorem hoareValid_loopOnly_of_invariantVCs
    (pre post inv : AssertExpr D Γ)
    (G : Guard D Γ)
    (Body : Cmd D Γ)
    (hBody : Body.LoopFree)
    (hInit :
      loopOnlyInitValid pre inv)
    (hMaint :
      loopOnlyMaintValid inv G Body hBody)
    (hTerm :
      loopOnlyTermValid inv post G) :
    HoareValid pre (.while G Body) post := by
  exact
    hoareValid_loopOnly_of_vcs
      pre post inv G Body hBody hInit hMaint hTerm

/-
  Command-level loop-only invariant VCs prove the
  corresponding loop-only Hoare triple.
-/
theorem hoareValid_loopOnly_of_invariantVCsOfCmd
    (pre post inv : AssertExpr D Γ)
    (C : Cmd D Γ)
    (hInit : loopOnlyInitValid pre inv)
    (hMaint : loopOnlyMaintValidOfCmd inv C)
    (hTerm : loopOnlyTermValidOfCmd inv post C) :
    HoareValid pre C post := by
  unfold loopOnlyMaintValidOfCmd at hMaint
  unfold loopOnlyTermValidOfCmd at hTerm
  cases hParts : C.loopOnlyParts? with
  | none =>
      simp [hParts] at hMaint
  | some parts =>
      rcases parts with ⟨G, Body⟩
      rw [hParts] at hMaint hTerm
      by_cases hBody : Body.LoopFree
      · change
          (if h : Body.LoopFree then
            loopOnlyMaintValid inv G Body h
          else
            False) at hMaint
        rw [dif_pos hBody] at hMaint
        have hSound := Cmd.loopOnlyParts?_sound hParts
        rcases hSound with ⟨hC, _hBodySound⟩
        subst C
        exact
          hoareValid_loopOnly_of_invariantVCs
            pre post inv G Body hBody
            hInit hMaint hTerm
      · change
          (if h : Body.LoopFree then
            loopOnlyMaintValid inv G Body h
          else
            False) at hMaint
        rw [dif_neg hBody] at hMaint
        exact False.elim hMaint

end Hoare

end Whiel

------------------------------------------------------------
-- Concrete SP Hoare Theorems
------------------------------------------------------------

namespace Whiel

namespace Hoare

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Assignment SP satisfies the strongest-postcondition spec.
-/
theorem spAssign_spOf
    (pre : AssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    Assertion.spOf
      (AssertExpr.spAssign pre X e).eval
      pre.eval
      (.assign X e) := by
  constructor
  · intro I J hPre hStep
    exact
      (AssertExpr.spAssign_eval_iff pre X e J).mpr
        ⟨I, hPre, hStep⟩
  · intro post hValid J hSP
    have hSemantic : sp (.assign X e) pre.eval J :=
      (AssertExpr.spAssign_eval_iff pre X e J).mp hSP
    exact sp_strongest hValid J hSemantic

/- The computed loop-free SP is a valid postcondition. -/
theorem spLoopFree_valid
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre : AssertExpr D Γ) :
    HoareValid pre C
      (AssertExpr.spLoopFree C hLoopFree pre) := by
  intro I J hPre hStep
  exact
    (AssertExpr.spLoopFree_eval_iff C hLoopFree pre J).mpr
      ⟨I, hPre, hStep⟩

/-
  The computed loop-free SP satisfies the
  strongest-postcondition spec.
-/
theorem spLoopFree_spOf
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre : AssertExpr D Γ) :
    Assertion.spOf
      (AssertExpr.spLoopFree C hLoopFree pre).eval
      pre.eval
      C := by
  constructor
  · intro I J hPre hStep
    exact
      (AssertExpr.spLoopFree_eval_iff C hLoopFree pre J).mpr
        ⟨I, hPre, hStep⟩
  · intro post hValid J hSP
    have hSemantic : sp C pre.eval J :=
      (AssertExpr.spLoopFree_eval_iff
        C hLoopFree pre J).mp hSP
    exact sp_strongest hValid J hSemantic

/-
  Hoare validity is entailment from the computed loop-free
  SP.
-/
theorem hoareValid_iff_spLoopFree_entails
    (pre : AssertExpr D Γ)
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (post : Assertion D Γ) :
    HoareValid pre C post ↔
      Assertion.entails
        (AssertExpr.spLoopFree C hLoopFree pre).eval
        post := by
  change HoareValid (pre.eval : Assertion D Γ) C post ↔
    Assertion.entails
      (AssertExpr.spLoopFree C hLoopFree pre).eval
      post
  rw [hoareValid_iff_sp_entails]
  constructor
  · intro hEntails J hSP
    exact hEntails J
      ((AssertExpr.spLoopFree_eval_iff C hLoopFree pre J).mp
        hSP)
  · intro hEntails J hSP
    exact hEntails J
      ((AssertExpr.spLoopFree_eval_iff
          C hLoopFree pre J).mpr
        hSP)

end Hoare

end Whiel
