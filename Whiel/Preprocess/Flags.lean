-- Author: Jesse Comer
import Whiel.Preprocess.Framed
import Whiel.Concrete.WhielNames

/-
  Flags and schema retagging for the generic Whiel
  preprocessor.

  A flag is a nullary relation `flagSymbol i 0`. At arity
  zero there are exactly two relations, so a flag is a
  Boolean: `up` is the nullary singleton and `down` is the
  empty relation. Raising and lowering are ordinary
  assignments and the flag test is an ordinary guard.

  The design note's Definition "Flag" spells the guard `f`
  as the equality of the flag with the nullary singleton
  and `¬ f` as its negation, and spells "down" as `f = ∅`.
  `FlagSym.test` is the positive guard, so a negated flag
  test is a single negation and no guard the preprocessor
  builds carries a double negation. Both flag values are
  written at the flag's own arity by an arity cast of a
  nullary constant, so the raw syntax of every raise, lower
  and test is a literal constant and carries no
  finite-set arity computation.

  Key definitions include:
    * `Whiel.Preprocess.retag`
    * `Whiel.Preprocess.FlagSym`
    * `Whiel.Preprocess.FlagSym.raise`
    * `Whiel.Preprocess.FlagSym.lower`
    * `Whiel.Preprocess.FlagSym.test`
    * `Whiel.Preprocess.project`
    * `Whiel.Preprocess.lift`
    * `Whiel.Preprocess.flagExt`

  The retagging facts of the design note are:
    * `Whiel.Preprocess.retag_bigStep_project`
    * `Whiel.Preprocess.retag_bigStep_lift`
    * `Whiel.Preprocess.retag_eval_iff`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Reduct And Cast Support
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  Updating an old symbol commutes with the reduct along a
  schema extension.
-/
theorem reduct_update_symOfExtension
    (hExt : Ω.extensionOf Δ)
    (J : Instance D Ω)
    (X : Δ.syms)
    (R :
      FinRelation D
        (Ω.arity (UnnamedSchema.symOfExtension hExt X))) :
    Instance.reduct hExt
        (Instance.update J
          (UnnamedSchema.symOfExtension hExt X) R) =
      Instance.update
        (Instance.reduct hExt J)
        X
        (cast
          (congrArg (FinRelation D)
            (UnnamedSchema.arity_eq_of_extensionOf
              hExt X))
          R) := by
  apply Instance.ext
  intro Y
  by_cases hYX : Y = X
  · subst hYX
    unfold Instance.reduct
    simp [Instance.update_lookup_eq,
      UnnamedSchema.symOfExtension]
  · have hNe :
        (⟨Y.1, hExt.1 Y.2⟩ : Ω.syms) ≠
          UnnamedSchema.symOfExtension hExt X := by
      intro hEq
      apply hYX
      exact Subtype.ext
        (congrArg (fun Z : Ω.syms => Z.1) hEq)
    unfold Instance.reduct
    simp [Instance.update_lookup_ne, hNe, hYX]

/- Casting along a type equality is injective. -/
theorem eq_of_cast_eq
    {α β : Type}
    (h : α = β)
    {a b : α}
    (hEq : cast h a = cast h b) :
    a = b := by
  cases h
  exact hEq

/-
  Evaluating an arity-cast expression and casting back is
  the original evaluation.
-/
theorem eval_castArity_cast
    {m n : Nat}
    (h : m = n)
    (e : RAExpr D Δ n)
    (I : Instance D Δ) :
    cast (congrArg (FinRelation D) h)
        ((RAExpr.castArity h e).eval I) =
      e.eval I := by
  cases h
  rfl

end Preprocess

end Whiel

------------------------------------------------------------
-- Command Retagging
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- Reinterpret a command over an extending schema. -/
def retag
    (hExt : Ω.extensionOf Δ) :
    Cmd D Δ → Cmd D Ω
| .skip => .skip
| .assign X e =>
    .assign
      (UnnamedSchema.symOfExtension hExt X)
      (RAExpr.castArity
        (UnnamedSchema.arity_eq_of_extensionOf hExt X)
        (e.onExtension hExt))
| .seq C₁ C₂ =>
    .seq (retag hExt C₁) (retag hExt C₂)
| .ite G C₁ C₂ =>
    .ite
      (G.onExtension hExt)
      (retag hExt C₁)
      (retag hExt C₂)
| .«while» G C =>
    .«while» (G.onExtension hExt) (retag hExt C)

/- Retagging preserves the assigned raw names. -/
@[simp] theorem assignedSymbols_retag
    (hExt : Ω.extensionOf Δ)
    (C : Cmd D Δ) :
    (retag hExt C).assignedSymbols =
      C.assignedSymbols := by
  induction C with
  | skip =>
      simp [retag, Cmd.assignedSymbols]
  | assign X e =>
      simp [retag, Cmd.assignedSymbols,
        UnnamedSchema.symOfExtension]
  | seq C₁ C₂ ih₁ ih₂ =>
      simp [retag, Cmd.assignedSymbols, ih₁, ih₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [retag, Cmd.assignedSymbols, ih₁, ih₂]
  | «while» G C ih =>
      simp [retag, Cmd.assignedSymbols, ih]

/- Retagging preserves the read and assigned raw names. -/
@[simp] theorem symbols_retag
    (hExt : Ω.extensionOf Δ)
    (C : Cmd D Δ) :
    (retag hExt C).symbols = C.symbols := by
  induction C with
  | skip =>
      simp [retag, Cmd.symbols]
  | assign X e =>
      simp [retag, Cmd.symbols,
        UnnamedSchema.symOfExtension,
        RAExpr.symbols, RAExpr.castArity,
        RAExpr.onExtension]
  | seq C₁ C₂ ih₁ ih₂ =>
      simp [retag, Cmd.symbols, ih₁, ih₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [retag, Cmd.symbols, ih₁, ih₂]
  | «while» G C ih =>
      simp [retag, Cmd.symbols, ih]

/- Retagging preserves the number of loops. -/
@[simp] theorem loops_retag
    (hExt : Ω.extensionOf Δ)
    (C : Cmd D Δ) :
    loops (retag hExt C) = loops C := by
  induction C with
  | skip => rfl
  | assign X e => rfl
  | seq C₁ C₂ ih₁ ih₂ =>
      simp [retag, loops, ih₁, ih₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [retag, loops, ih₁, ih₂]
  | «while» G C ih =>
      simp [retag, loops, ih]

end Preprocess

end Whiel

------------------------------------------------------------
-- Projection And Lift
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- The projection of a state over `Ω` to one over `Δ`. -/
def project
    (hExt : Ω.extensionOf Δ)
    (I : Instance D Ω) :
    Instance D Δ :=
  Instance.reduct hExt I

/- The lift of a state over `Δ`, with every flag down. -/
def lift
    (hExt : Ω.extensionOf Δ)
    (I : Instance D Δ) :
    Instance D Ω :=
  Instance.expandEmpty hExt I

@[simp] theorem project_lift
    (hExt : Ω.extensionOf Δ)
    (I : Instance D Δ) :
    project (D := D) hExt (lift hExt I) = I :=
  Instance.reduct_expandEmpty hExt I

/- The lift sends every new relation to the empty one. -/
theorem lift_eq_empty_of_not_mem
    (hExt : Ω.extensionOf Δ)
    (I : Instance D Δ)
    (X : Ω.syms)
    (hX : X.1 ∉ Δ.syms) :
    lift hExt I X = ∅ :=
  Instance.expandEmpty_eq_empty_of_not_mem hExt I X hX

end Preprocess

end Whiel

------------------------------------------------------------
-- Retagging Semantics
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- A retagged guard is true exactly on the reduct. -/
theorem retag_eval_iff
    (hExt : Ω.extensionOf Δ)
    (G : Guard D Δ)
    (I : Instance D Ω) :
    (G.onExtension hExt).eval I ↔
      G.eval (project hExt I) := by
  letI : Fact (Ω.extensionOf Δ) := ⟨hExt⟩
  exact
    Guard.onExtension_eval_reduct
      (Γ := Ω) (Δ := Δ) G I _ rfl

/- Reduct compatibility for a retagged loop. -/
private theorem retag_while_bigStep_project
    (hExt : Ω.extensionOf Δ)
    {G : Guard D Δ}
    {Body : Cmd D Δ}
    (hBody :
      ∀ {I J : Instance D Ω},
        Cmd.BigStep (retag hExt Body) I J →
          Cmd.BigStep Body
            (project hExt I)
            (project hExt J))
    {I J : Instance D Ω} :
    Cmd.BigStep
        (.«while» (G.onExtension hExt)
          (retag hExt Body)) I J →
      Cmd.BigStep (.«while» G Body)
        (project hExt I)
        (project hExt J) := by
  intro hStep
  generalize hW :
      (Whiel.Cmd.«while» (G.onExtension hExt)
        (retag hExt Body) : Cmd D Ω) = W at hStep
  induction hStep generalizing G Body with
  | skip I => cases hW
  | assign I X E => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hStep ih => cases hW
  | ite_false hEval hStep ih => cases hW
  | while_false hFalse =>
      cases hW
      exact Cmd.BigStep.while_false
        (fun hEval =>
          hFalse
            ((retag_eval_iff hExt G _).mpr hEval))
  | while_true hEval hBodyStep hLoop ihBody ihLoop =>
      cases hW
      exact Cmd.BigStep.while_true
        ((retag_eval_iff hExt G _).mp hEval)
        (hBody hBodyStep)
        (ihLoop hBody rfl)

/-
  A run of a retagged command projects to a run of the
  original command on the reducts.
-/
theorem retag_bigStep_project
    (hExt : Ω.extensionOf Δ)
    {C : Cmd D Δ}
    {I J : Instance D Ω}
    (hStep : Cmd.BigStep (retag hExt C) I J) :
    Cmd.BigStep C
      (project hExt I)
      (project hExt J) := by
  unfold project
  induction C generalizing I J with
  | skip =>
      have hEq : J = I :=
        (Cmd.bigStep_skip_iff I J).mp
          (by simpa [retag] using hStep)
      rw [hEq]
      exact Cmd.BigStep.skip _
  | assign X e =>
      let hAr :=
        UnnamedSchema.arity_eq_of_extensionOf hExt X
      have hAssign :
          J =
            Instance.update I
              (UnnamedSchema.symOfExtension hExt X)
              ((RAExpr.castArity hAr
                (e.onExtension hExt)).eval I) :=
        (Cmd.bigStep_assign_iff I J
          (UnnamedSchema.symOfExtension hExt X)
          (RAExpr.castArity hAr
            (e.onExtension hExt))).mp
          (by simpa [retag] using hStep)
      rw [hAssign, Cmd.bigStep_assign_iff,
        reduct_update_symOfExtension]
      have hEval :
          cast (congrArg (FinRelation D) hAr)
              ((RAExpr.castArity hAr
                (e.onExtension hExt)).eval I) =
            e.eval (Instance.reduct hExt I) := by
        letI : Fact (Ω.extensionOf Δ) := ⟨hExt⟩
        rw [eval_castArity_cast]
        exact RAExpr.reduct_property (Δ := Ω) (e := e) I
      rw [hEval]
  | seq C₁ C₂ ih₁ ih₂ =>
      rcases
        (Cmd.bigStep_seq_iff _ _ I J).mp
          (by simpa [retag] using hStep) with
        ⟨K, h₁, h₂⟩
      exact Cmd.BigStep.seq (ih₁ h₁) (ih₂ h₂)
  | ite G C₁ C₂ ih₁ ih₂ =>
      rcases
        (Cmd.bigStep_ite_iff _ _ _ I J).mp
          (by simpa [retag] using hStep) with
        h | h
      · exact Cmd.BigStep.ite_true
          ((retag_eval_iff hExt G I).mp h.1)
          (ih₁ h.2)
      · exact Cmd.BigStep.ite_false
          (fun hEval =>
            h.1 ((retag_eval_iff hExt G I).mpr hEval))
          (ih₂ h.2)
  | «while» G Body ihBody =>
      exact retag_while_bigStep_project
        hExt (fun h => ihBody h) hStep

/-
  A run of the original command lifts to a run of the
  retagged command from any state over the extension.
-/
theorem retag_bigStep_lift
    (hExt : Ω.extensionOf Δ)
    {C : Cmd D Δ}
    {I J : Instance D Δ}
    {IΩ : Instance D Ω}
    (hReduct : project hExt IΩ = I)
    (hStep : Cmd.BigStep C I J) :
    ∃ JΩ : Instance D Ω,
      Cmd.BigStep (retag hExt C) IΩ JΩ ∧
        project hExt JΩ = J := by
  unfold project at hReduct ⊢
  induction hStep generalizing IΩ with
  | skip I =>
      exact ⟨IΩ, Cmd.BigStep.skip IΩ, hReduct⟩
  | assign I X e =>
      let XΩ := UnnamedSchema.symOfExtension hExt X
      let hAr :=
        UnnamedSchema.arity_eq_of_extensionOf hExt X
      let eΩ :=
        RAExpr.castArity hAr (e.onExtension hExt)
      refine
        ⟨Instance.update IΩ XΩ (eΩ.eval IΩ), ?_, ?_⟩
      · exact Cmd.BigStep.assign IΩ XΩ eΩ
      · rw [reduct_update_symOfExtension, hReduct]
        have hEval :
            cast (congrArg (FinRelation D) hAr)
                (eΩ.eval IΩ) =
              e.eval I := by
          letI : Fact (Ω.extensionOf Δ) := ⟨hExt⟩
          rw [eval_castArity_cast]
          simpa [hReduct] using
            (RAExpr.reduct_property
              (Δ := Ω) (e := e) IΩ)
        rw [hEval]
  | seq h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ hReduct with ⟨KΩ, hK, hKR⟩
      rcases ih₂ hKR with ⟨JΩ, hJ, hJR⟩
      exact ⟨JΩ, Cmd.BigStep.seq hK hJ, hJR⟩
  | ite_true hG hC ih =>
      rcases ih hReduct with ⟨JΩ, hJ, hJR⟩
      refine ⟨JΩ, ?_, hJR⟩
      exact Cmd.BigStep.ite_true
        ((retag_eval_iff hExt _ IΩ).mpr
          (by unfold project; rw [hReduct]; exact hG))
        hJ
  | ite_false hG hC ih =>
      rcases ih hReduct with ⟨JΩ, hJ, hJR⟩
      refine ⟨JΩ, ?_, hJR⟩
      exact Cmd.BigStep.ite_false
        (fun hEval =>
          hG
            (by
              rw [← hReduct]
              exact (retag_eval_iff hExt _ IΩ).mp hEval))
        hJ
  | while_false hG =>
      refine ⟨IΩ, ?_, hReduct⟩
      exact Cmd.BigStep.while_false
        (fun hEval =>
          hG
            (by
              rw [← hReduct]
              exact (retag_eval_iff hExt _ IΩ).mp hEval))
  | while_true hG hBody hLoop ihBody ihLoop =>
      rcases ihBody hReduct with ⟨KΩ, hK, hKR⟩
      rcases ihLoop hKR with ⟨JΩ, hJ, hJR⟩
      refine ⟨JΩ, ?_, hJR⟩
      exact Cmd.BigStep.while_true
        ((retag_eval_iff hExt _ IΩ).mpr
          (by unfold project; rw [hReduct]; exact hG))
        hK hJ

/-
  A retagged command leaves every relation outside the
  smaller schema unchanged.
-/
theorem retag_preserves_new
    (hExt : Ω.extensionOf Δ)
    {C : Cmd D Δ}
    {I J : Instance D Ω}
    (hStep : Cmd.BigStep (retag hExt C) I J)
    (X : Ω.syms)
    (hX : X.1 ∉ Δ.syms) :
    J X = I X := by
  refine Cmd.BigStep.no_update_preservation hStep X ?_
  rw [assignedSymbols_retag]
  intro hMem
  exact hX (Cmd.assignedSymbols_subset_syms C hMem)

end Preprocess

end Whiel

------------------------------------------------------------
-- Flag Symbols
------------------------------------------------------------

namespace Whiel

namespace Preprocess

/-
  A nullary relation of `Ω` used as a Boolean control
  state.
-/
structure FlagSym
    {A : Type} [RelationNames A]
    (Ω : UnnamedSchema A) : Type where
  sym : Ω.syms
  arityZero : Ω.arity sym = 0

namespace FlagSym

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Ω : UnnamedSchema A}

/- The nullary singleton, typed at the flag's arity. -/
def topExpr
    (f : FlagSym Ω) :
    RAExpr D Ω (Ω.arity f.sym) :=
  RAExpr.castArity f.arityZero RAExpr.top

/- The nullary empty relation at the flag's arity. -/
def emptyExpr
    (f : FlagSym Ω) :
    RAExpr D Ω (Ω.arity f.sym) :=
  RAExpr.castArity f.arityZero
    (RAExpr.empty (D := D) 0)

/- Raise the flag: assign the nullary singleton. -/
def raise (f : FlagSym Ω) : Cmd D Ω :=
  .assign f.sym f.topExpr

/- Lower the flag: assign the empty relation. -/
def lower (f : FlagSym Ω) : Cmd D Ω :=
  .assign f.sym f.emptyExpr

/- The flag guard: the flag is the nullary singleton. -/
def test (f : FlagSym Ω) : Guard D Ω :=
  .eq (RAExpr.rel f.sym) f.topExpr

/- The flag is up at a state. -/
def Up (f : FlagSym Ω) (I : Instance D Ω) : Prop :=
  (f.test (D := D)).eval I

end FlagSym

end Preprocess

end Whiel

------------------------------------------------------------
-- Flag Evaluation
------------------------------------------------------------

namespace Whiel

namespace Preprocess

namespace FlagSym

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Ω : UnnamedSchema A}

/- A relation expression evaluates to its relation. -/
theorem eval_rel
    (X : Ω.syms)
    (I : Instance D Ω) :
    (RAExpr.rel X).eval I = I X := by
  have hSpec :=
    RAExpr.raw_eval?_eq_eval
      (RAExpr.rel X : RAExpr D Ω (Ω.arity X)) I
  have hRaw :
      (RAExpr.rel X : RAExpr D Ω (Ω.arity X)).expr.eval?
          (Γ := Ω) I =
        some ⟨Ω.arity X, I X⟩ := by
    simp [RAExpr.rel, RawRAExpr.eval?,
      Instance.relation?, X.2]
  rw [hRaw] at hSpec
  injection hSpec with hSigma
  injection hSigma with _ hRel
  exact hRel.symm

/- Casting the empty relation gives the empty relation. -/
omit [Domain D] in
theorem cast_empty
    {m n : Nat}
    (h : m = n) :
    cast (congrArg (FinRelation D) h)
        (∅ : FinRelation D m) = ∅ := by
  cases h
  rfl

/- The lowered value is the empty relation. -/
theorem eval_emptyExpr
    (f : FlagSym Ω)
    (I : Instance D Ω) :
    (f.emptyExpr).eval I =
      (∅ : FinRelation D (Ω.arity f.sym)) := by
  have hSpec :=
    RAExpr.raw_eval?_eq_eval
      (f.emptyExpr (D := D)) I
  have hRaw :
      (f.emptyExpr (D := D)).expr.eval? (Γ := Ω) I =
        some ⟨0, (∅ : FinRelation D 0)⟩ := by
    simp [emptyExpr, RAExpr.castArity, RAExpr.empty,
      RawRAExpr.eval?]
  rw [hRaw] at hSpec
  injection hSpec with hSigma
  injection hSigma with hEq hRel
  have hCast :
      (f.emptyExpr (D := D)).eval I =
        cast (congrArg (FinRelation D) f.arityZero.symm)
          (∅ : FinRelation D 0) :=
    eq_cast_iff_heq.mpr hRel.symm
  rw [hCast]
  exact cast_empty f.arityZero.symm

/- The raised value is the nullary singleton. -/
theorem eval_topExpr
    (f : FlagSym Ω)
    (I : Instance D Ω) :
    (f.topExpr).eval I =
      cast (congrArg (FinRelation D) f.arityZero.symm)
        FinRelation.top := by
  have hSpec :=
    RAExpr.raw_eval?_eq_eval (f.topExpr (D := D)) I
  have hRaw :
      (f.topExpr (D := D)).expr.eval? (Γ := Ω) I =
        some ⟨0, (FinRelation.top : FinRelation D 0)⟩ := by
    simp [topExpr, RAExpr.castArity, RAExpr.top,
      RawRAExpr.eval?]
  rw [hRaw] at hSpec
  injection hSpec with hSigma
  injection hSigma with hEq hRel
  exact eq_cast_iff_heq.mpr hRel.symm

/- The raised value is not the empty relation. -/
theorem eval_topExpr_ne_empty
    (f : FlagSym Ω)
    (I : Instance D Ω) :
    (f.topExpr).eval I ≠
      (∅ : FinRelation D (Ω.arity f.sym)) := by
  intro hEq
  have hTop :
      cast (congrArg (FinRelation D) f.arityZero)
          ((f.topExpr (D := D)).eval I) =
        FinRelation.top := by
    rw [eval_topExpr]
    simp
  rw [hEq, cast_empty f.arityZero] at hTop
  have hMem :
      (Tuple.empty : Tuple D 0) ∈
        (∅ : FinRelation D 0) := by
    rw [hTop]
    simp [FinRelation.top]
  simp at hMem

/- Arity zero has exactly one tuple. -/
omit [Domain D] in
theorem tuple_zero_eq_empty
    (t : Tuple D 0) :
    t = Tuple.empty := by
  apply Vector.ext
  intro i hi
  exact (Nat.not_lt_zero _ hi).elim

/-
  At arity zero there are exactly two relations, so a
  nullary relation is the singleton exactly when it is not
  the empty relation.
-/
theorem nullary_eq_top_iff
    (R : FinRelation D 0) :
    R = FinRelation.top ↔ R ≠ ∅ := by
  constructor
  · rintro rfl hEmpty
    have hMem :
        (Tuple.empty : Tuple D 0) ∈
          (FinRelation.top : FinRelation D 0) :=
      Finset.mem_singleton_self _
    rw [hEmpty] at hMem
    exact Finset.notMem_empty _ hMem
  · intro hNe
    have hMem : (Tuple.empty : Tuple D 0) ∈ R := by
      by_cases hIn : (Tuple.empty : Tuple D 0) ∈ R
      · exact hIn
      · refine absurd (Finset.ext ?_) hNe
        intro t
        rw [tuple_zero_eq_empty t]
        exact ⟨fun h => absurd h hIn,
          fun h => absurd h (Finset.notMem_empty _)⟩
    refine Finset.ext ?_
    intro t
    rw [tuple_zero_eq_empty t]
    exact ⟨fun _ => Finset.mem_singleton_self _,
      fun _ => hMem⟩

/-
  The same dichotomy, read at a propositionally zero
  arity.
-/
theorem eq_cast_top_iff_ne_empty
    {n : Nat}
    (h : n = 0)
    (R : FinRelation D n) :
    R =
        cast (congrArg (FinRelation D) h.symm)
          FinRelation.top ↔
      R ≠ ∅ := by
  subst h
  exact nullary_eq_top_iff R

/- The flag is up exactly when its relation is nonempty. -/
theorem up_iff
    (f : FlagSym Ω)
    (I : Instance D Ω) :
    f.Up I ↔ I f.sym ≠ ∅ := by
  unfold Up test
  rw [Guard.eval, eval_rel, eval_topExpr]
  exact eq_cast_top_iff_ne_empty f.arityZero (I f.sym)

instance
    (f : FlagSym Ω)
    (I : Instance D Ω) :
    Decidable (f.Up I) := by
  unfold Up
  infer_instance

end FlagSym

end Preprocess

end Whiel

------------------------------------------------------------
-- Flag Commands
------------------------------------------------------------

namespace Whiel

namespace Preprocess

namespace FlagSym

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Ω : UnnamedSchema A}

@[simp] theorem assignedSymbols_raise
    (f : FlagSym Ω) :
    (f.raise (D := D)).assignedSymbols = {f.sym.1} :=
  rfl

@[simp] theorem assignedSymbols_lower
    (f : FlagSym Ω) :
    (f.lower (D := D)).assignedSymbols = {f.sym.1} :=
  rfl

@[simp] theorem bigStep_raise_iff
    (f : FlagSym Ω)
    (I J : Instance D Ω) :
    Cmd.BigStep f.raise I J ↔
      J = Instance.update I f.sym (f.topExpr.eval I) :=
  Cmd.bigStep_assign_iff I J f.sym f.topExpr

@[simp] theorem bigStep_lower_iff
    (f : FlagSym Ω)
    (I J : Instance D Ω) :
    Cmd.BigStep f.lower I J ↔
      J = Instance.update I f.sym (f.emptyExpr.eval I) :=
  Cmd.bigStep_assign_iff I J f.sym f.emptyExpr

/- Raising leaves the flag up. -/
theorem up_of_bigStep_raise
    {f : FlagSym Ω}
    {I J : Instance D Ω}
    (hStep : Cmd.BigStep f.raise I J) :
    f.Up J := by
  rw [bigStep_raise_iff] at hStep
  subst hStep
  rw [up_iff, Instance.update_lookup_eq]
  exact eval_topExpr_ne_empty f I

/- Lowering leaves the flag down. -/
theorem not_up_of_bigStep_lower
    {f : FlagSym Ω}
    {I J : Instance D Ω}
    (hStep : Cmd.BigStep f.lower I J) :
    ¬ f.Up J := by
  rw [bigStep_lower_iff] at hStep
  subst hStep
  rw [up_iff, Instance.update_lookup_eq]
  simp [eval_emptyExpr]

/- A run that assigns no flag leaves the flag alone. -/
theorem up_congr_of_not_assigned
    {f : FlagSym Ω}
    {C : Cmd D Ω}
    {I J : Instance D Ω}
    (hStep : Cmd.BigStep C I J)
    (hFree : f.sym.1 ∉ C.assignedSymbols) :
    (f.Up J ↔ f.Up I) := by
  have hEq :=
    Cmd.BigStep.no_update_preservation hStep f.sym hFree
  rw [up_iff, up_iff, hEq]

/- Another flag's value is untouched by a raise. -/
theorem up_congr_of_bigStep_raise_ne
    {f g : FlagSym Ω}
    {I J : Instance D Ω}
    (hNe : g.sym ≠ f.sym)
    (hStep : Cmd.BigStep f.raise I J) :
    (g.Up J ↔ g.Up I) := by
  rw [bigStep_raise_iff] at hStep
  subst hStep
  rw [up_iff, up_iff,
    Instance.update_lookup_ne _ _ _ hNe]

/- Another flag's value is untouched by a lowering. -/
theorem up_congr_of_bigStep_lower_ne
    {f g : FlagSym Ω}
    {I J : Instance D Ω}
    (hNe : g.sym ≠ f.sym)
    (hStep : Cmd.BigStep f.lower I J) :
    (g.Up J ↔ g.Up I) := by
  rw [bigStep_lower_iff] at hStep
  subst hStep
  rw [up_iff, up_iff,
    Instance.update_lookup_ne _ _ _ hNe]

end FlagSym

end Preprocess

end Whiel

------------------------------------------------------------
-- Retagged Framed Loops And The Retagging Lemma
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- Reinterpret a framed loop over an extending schema. -/
def Framed.retagOn
    (hExt : Ω.extensionOf Δ)
    (L : Framed D Δ) :
    Framed D Ω where
  init := retag hExt L.init
  guard := L.guard.onExtension hExt
  body := retag hExt L.body
  close := retag hExt L.close

@[simp] theorem Framed.unfold_retagOn
    (hExt : Ω.extensionOf Δ)
    (L : Framed D Δ) :
    (L.retagOn hExt).unfold = retag hExt L.unfold :=
  rfl

/-
  Two states over the extension with equal reducts that
  agree on the new relations are equal.
-/
theorem eq_of_reduct_eq_of_agree
    (hExt : Ω.extensionOf Δ)
    {I J : Instance D Ω}
    (hReduct :
      Instance.reduct hExt I = Instance.reduct hExt J)
    (hOut :
      ∀ X : Ω.syms, X.1 ∉ Δ.syms → I X = J X) :
    I = J := by
  apply Instance.ext
  intro X
  cases X with
  | mk x hxΩ =>
      by_cases hX : x ∈ Δ.syms
      · have hCast := congrFun hReduct ⟨x, hX⟩
        unfold Instance.reduct at hCast
        exact eq_of_cast_eq _ hCast
      · exact hOut ⟨x, hxΩ⟩ hX

/-
  Lemma "Retagging": a run of the retagged command is
  exactly a run of the original on the reducts together
  with agreement on the new relations.
-/
theorem retag_bigStep_iff
    (hExt : Ω.extensionOf Δ)
    (C : Cmd D Δ)
    (I J : Instance D Ω) :
    Cmd.BigStep (retag hExt C) I J ↔
      Cmd.BigStep C
          (project hExt I)
          (project hExt J) ∧
        ∀ X : Ω.syms, X.1 ∉ Δ.syms → J X = I X := by
  constructor
  · intro hStep
    exact
      ⟨retag_bigStep_project hExt hStep,
        fun X hX => retag_preserves_new hExt hStep X hX⟩
  · rintro ⟨hStep, hOut⟩
    rcases retag_bigStep_lift hExt rfl hStep with
      ⟨JΩ, hJ, hJR⟩
    have hEq : JΩ = J := by
      refine eq_of_reduct_eq_of_agree hExt hJR ?_
      intro X hX
      rw [retag_preserves_new hExt hJ X hX, hOut X hX]
    rw [← hEq]
    exact hJ

/- Flag updates do not change the projection. -/
theorem project_update_of_not_mem
    {f : FlagSym Ω}
    (hExt : Ω.extensionOf Δ)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (I : Instance D Ω)
    (R : FinRelation D (Ω.arity f.sym)) :
    project hExt (Instance.update I f.sym R) =
      project hExt I :=
  Instance.reduct_update_of_not_mem hExt I f.sym R hFresh

/- The lift enters with every new flag down. -/
theorem not_up_lift
    {f : FlagSym Ω}
    (hExt : Ω.extensionOf Δ)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (I : Instance D Δ) :
    ¬ f.Up (lift hExt I) := by
  rw [FlagSym.up_iff]
  simp [lift_eq_empty_of_not_mem hExt I f.sym hFresh]

/- Raising a fresh flag does not move the projection. -/
theorem project_of_bigStep_raise
    {f : FlagSym Ω}
    (hExt : Ω.extensionOf Δ)
    (hFresh : f.sym.1 ∉ Δ.syms)
    {I J : Instance D Ω}
    (hStep : Cmd.BigStep f.raise I J) :
    project hExt J = project hExt I := by
  rw [FlagSym.bigStep_raise_iff] at hStep
  subst hStep
  exact project_update_of_not_mem hExt hFresh I _

/- Lowering a fresh flag does not move the projection. -/
theorem project_of_bigStep_lower
    {f : FlagSym Ω}
    (hExt : Ω.extensionOf Δ)
    (hFresh : f.sym.1 ∉ Δ.syms)
    {I J : Instance D Ω}
    (hStep : Cmd.BigStep f.lower I J) :
    project hExt J = project hExt I := by
  rw [FlagSym.bigStep_lower_iff] at hStep
  subst hStep
  exact project_update_of_not_mem hExt hFresh I _

/- A retagged command never assigns a new relation. -/
theorem not_assigned_retag
    {f : FlagSym Ω}
    (hExt : Ω.extensionOf Δ)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (C : Cmd D Δ) :
    f.sym.1 ∉ (retag hExt C).assignedSymbols := by
  rw [assignedSymbols_retag]
  intro hMem
  exact hFresh (Cmd.assignedSymbols_subset_syms C hMem)

/- A retagged command leaves a fresh flag alone. -/
theorem up_congr_retag
    {f : FlagSym Ω}
    (hExt : Ω.extensionOf Δ)
    (hFresh : f.sym.1 ∉ Δ.syms)
    {C : Cmd D Δ}
    {I J : Instance D Ω}
    (hStep : Cmd.BigStep (retag hExt C) I J) :
    (f.Up J ↔ f.Up I) :=
  FlagSym.up_congr_of_not_assigned hStep
    (not_assigned_retag hExt hFresh C)

end Preprocess

end Whiel

------------------------------------------------------------
-- The Flag Extension Of A Program-Name Schema
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

/- The nullary relation name of a flag identifier. -/
def flagName (i : Nat) : ProgramNames :=
  .flagSymbol i 0

@[simp] theorem isFlag_flagName
    (i : Nat) :
    (flagName i).IsFlag :=
  trivial

@[simp] theorem isBase_flagName
    (i : Nat) :
    (flagName i).IsBase :=
  rfl

theorem flagName_injective :
    Function.Injective flagName := by
  intro i j hEq
  injection hEq

/- The flag names of a list of identifiers. -/
def flagNames (Φ : List Nat) : Finset ProgramNames :=
  (Φ.map flagName).toFinset

@[simp] theorem mem_flagNames_iff
    {i : Nat}
    {Φ : List Nat} :
    flagName i ∈ flagNames Φ ↔ i ∈ Φ := by
  simp [flagNames, flagName_injective.eq_iff]

/-
  The flag extension `Γ[Φ]`: one nullary flag relation per
  identifier of `Φ`, and the arities of `Γ` unchanged.
-/
def flagExt
    (Γ : UnnamedSchema ProgramNames)
    (Φ : List Nat) :
    UnnamedSchema ProgramNames where
  syms := Γ.syms ∪ flagNames Φ
  arity := fun X =>
    if h : X.1 ∈ Γ.syms then Γ.arity ⟨X.1, h⟩ else 0

/- The flag extension extends the input schema. -/
theorem flagExt_extensionOf
    (Γ : UnnamedSchema ProgramNames)
    (Φ : List Nat) :
    (flagExt Γ Φ).extensionOf Γ := by
  refine ⟨Finset.subset_union_left, ?_⟩
  intro s
  have hMem : s.1 ∈ (flagExt Γ Φ).syms :=
    Finset.mem_union_left _ s.2
  simp [UnnamedSchema.arity?, flagExt, s.2]

/- A drawn flag as a nullary symbol of the extension. -/
def flagSymOf
    (Γ : UnnamedSchema ProgramNames)
    (Φ : List Nat)
    (i : Nat)
    (hMem : i ∈ Φ)
    (hFresh : flagName i ∉ Γ.syms) :
    FlagSym (flagExt Γ Φ) where
  sym :=
    ⟨flagName i, by
      refine Finset.mem_union_right _ ?_
      exact mem_flagNames_iff.mpr hMem⟩
  arityZero := by
    simp [flagExt, hFresh]

@[simp] theorem flagSymOf_sym_val
    {Γ : UnnamedSchema ProgramNames}
    {Φ : List Nat}
    {i : Nat}
    (hMem : i ∈ Φ)
    (hFresh : flagName i ∉ Γ.syms) :
    (flagSymOf Γ Φ i hMem hFresh).sym.1 = flagName i :=
  rfl

/- Distinct identifiers give distinct flag symbols. -/
theorem flagSymOf_ne
    {Γ : UnnamedSchema ProgramNames}
    {Φ : List Nat}
    {i j : Nat}
    (hMemI : i ∈ Φ)
    (hFreshI : flagName i ∉ Γ.syms)
    (hMemJ : j ∈ Φ)
    (hFreshJ : flagName j ∉ Γ.syms)
    (hNe : i ≠ j) :
    (flagSymOf Γ Φ i hMemI hFreshI).sym ≠
      (flagSymOf Γ Φ j hMemJ hFreshJ).sym := by
  intro hEq
  exact hNe
    (flagName_injective
      (congrArg (fun X => X.1) hEq))

/- Input schemas at raw index zero contain no flag. -/
theorem flagName_not_mem_of_rawIndexZero
    {Γ : UnnamedSchema ProgramNames}
    (hRaw : Γ.RawIndexZero)
    (i : Nat) :
    flagName i ∉ Γ.syms := by
  intro hMem
  exact (hRaw _ hMem).2 (isFlag_flagName i)

end Preprocess

end Whiel

------------------------------------------------------------
-- The Flag Supply
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

/- One more than a name's flag identifier, or zero. -/
def flagBound : ProgramNames → Nat
| .flagSymbol id _ => id + 1
| .programSymbol _ _ => 0
| .auxiliarySymbol _ _ => 0

/-
  The first free flag identifier of a schema: one more
  than the largest flag identifier it contains.
-/
def flagSeed (Γ : UnnamedSchema ProgramNames) : Nat :=
  Finset.fold (op := max) 0 flagBound Γ.syms

private theorem flagBound_le_fold
    (X : ProgramNames) :
    ∀ s : Finset ProgramNames, X ∈ s →
      flagBound X ≤
        Finset.fold (op := max) 0 flagBound s := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro hMem
      cases hMem
  | insert Y s hY ih =>
      intro hMem
      rw [Finset.fold_insert hY]
      rcases Finset.mem_insert.mp hMem with hEq | hTail
      · subst hEq
        exact le_max_left _ _
      · exact le_trans (ih hTail) (le_max_right _ _)

private theorem fold_flagBound_eq_zero :
    ∀ s : Finset ProgramNames,
      (∀ X ∈ s, flagBound X = 0) →
        Finset.fold (op := max) 0 flagBound s = 0 := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      rfl
  | insert Y s hY ih =>
      intro hAll
      rw [Finset.fold_insert hY,
        hAll Y (Finset.mem_insert_self Y s),
        ih (fun X hX =>
          hAll X (Finset.mem_insert_of_mem hX))]
      exact Nat.max_self 0

/- Every identifier at or above the seed is fresh. -/
theorem flagName_not_mem_of_flagSeed_le
    {Γ : UnnamedSchema ProgramNames}
    {i : Nat}
    (hSeed : flagSeed Γ ≤ i) :
    flagName i ∉ Γ.syms := by
  intro hMem
  have hLe : flagBound (flagName i) ≤ flagSeed Γ :=
    flagBound_le_fold (flagName i) Γ.syms hMem
  have hAbsurd : i + 1 ≤ i :=
    Nat.le_trans hLe hSeed
  omega

/- On a raw input schema the flag supply starts at zero. -/
theorem flagSeed_eq_zero_of_rawIndexZero
    {Γ : UnnamedSchema ProgramNames}
    (hRaw : Γ.RawIndexZero) :
    flagSeed Γ = 0 := by
  refine fold_flagBound_eq_zero Γ.syms ?_
  intro X hX
  have hNotFlag : ¬ X.IsFlag := (hRaw X hX).2
  cases X with
  | programSymbol base index => rfl
  | auxiliarySymbol base index => rfl
  | flagSymbol id index =>
      exact absurd trivial hNotFlag

end Preprocess

end Whiel
