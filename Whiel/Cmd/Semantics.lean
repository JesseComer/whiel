-- Author: Jesse Comer
import Whiel.Cmd.Syntax
import Whiel.Guard.Semantics

/-
  Big-step semantics for Whiel commands and programs.

  `Cmd.BigStep` runs over the full execution schema.
  `Program.BigStep` lifts this relation to external inputs
  and observable outputs by empty-expanding the input and
  then reducing the final execution instance to the output
  schema.

  Key declarations: `Cmd.BigStep`, `Cmd.BigStepEquiv`,
  `Cmd.BigStep.deterministic`,
  `Cmd.BigStep.no_update_preservation`, `Program.BigStep`,
  and `Program.bigStep_unique`.
-/

------------------------------------------------------------
-- Command Big-Step Semantics
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Relational big-step semantics.

  `BigStep C I J` says that command `C`, started in full
  instance `I`, terminates in full instance `J`.
-/
inductive BigStep :
    Cmd D Γ → Instance D Γ → Instance D Γ → Prop
| skip
    (I : Instance D Γ) :
    BigStep .skip I I
| assign
    (I : Instance D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    BigStep
      (.assign X e)
      I
      (Instance.update I X (e.eval I))
| seq
    {C₁ C₂ : Cmd D Γ}
    {I I₁ I₂ : Instance D Γ} :
    BigStep C₁ I I₁ →
    BigStep C₂ I₁ I₂ →
    BigStep (.seq C₁ C₂) I I₂
| ite_true
    {G : Guard D Γ}
    {C₁ C₂ : Cmd D Γ}
    {I J : Instance D Γ} :
    G.eval I →
    BigStep C₁ I J →
    BigStep (.ite G C₁ C₂) I J
| ite_false
    {G : Guard D Γ}
    {C₁ C₂ : Cmd D Γ}
    {I J : Instance D Γ} :
    ¬ G.eval I →
    BigStep C₂ I J →
    BigStep (.ite G C₁ C₂) I J
| while_false
    {G : Guard D Γ}
    {C : Cmd D Γ}
    {I : Instance D Γ} :
    ¬ G.eval I →
    BigStep (.while G C) I I
| while_true
    {G : Guard D Γ}
    {C : Cmd D Γ}
    {I I₁ I₂ : Instance D Γ} :
    G.eval I →
    BigStep C I I₁ →
    BigStep (.while G C) I₁ I₂ →
    BigStep (.while G C) I I₂

end Cmd

end Whiel

------------------------------------------------------------
-- Command Semantic Properties
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Semantic equivalence of commands by big-step behavior. -/
def BigStepEquiv
    (C₁ C₂ : Cmd D Γ) : Prop :=
  ∀ I J : Instance D Γ,
    BigStep C₁ I J ↔ BigStep C₂ I J

/- Big-step equivalence from an explicit pointwise iff. -/
theorem BigStepEquiv.of_iff
    {C₁ C₂ : Cmd D Γ}
    (h :
      ∀ I J : Instance D Γ,
        BigStep C₁ I J ↔ BigStep C₂ I J) :
    BigStepEquiv C₁ C₂ :=
  h

/- Big-step equivalence is reflexive. -/
theorem BigStepEquiv.refl
    (C : Cmd D Γ) :
    BigStepEquiv C C :=
  fun _ _ => Iff.rfl

/- Big-step equivalence is symmetric. -/
theorem BigStepEquiv.symm
    {C₁ C₂ : Cmd D Γ}
    (h : BigStepEquiv C₁ C₂) :
    BigStepEquiv C₂ C₁ :=
  fun I J => (h I J).symm

/- Big-step equivalence is transitive. -/
theorem BigStepEquiv.trans
    {C₁ C₂ C₃ : Cmd D Γ}
    (h₁₂ : BigStepEquiv C₁ C₂)
    (h₂₃ : BigStepEquiv C₂ C₃) :
    BigStepEquiv C₁ C₃ :=
  fun I J => Iff.trans (h₁₂ I J) (h₂₃ I J)

@[simp] theorem bigStep_skip_iff
    (I J : Instance D Γ) :
    BigStep (.skip : Cmd D Γ) I J ↔ J = I := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact BigStep.skip I

@[simp] theorem bigStep_assign_iff
    (I J : Instance D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    BigStep (.assign X e) I J ↔
      J = Instance.update I X (e.eval I) := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact BigStep.assign I X e

@[simp] theorem bigStep_seq_iff
    (C₁ C₂ : Cmd D Γ)
    (I J : Instance D Γ) :
    BigStep (.seq C₁ C₂) I J ↔
      ∃ K : Instance D Γ,
        BigStep C₁ I K ∧ BigStep C₂ K J := by
  constructor
  · intro h
    cases h with
    | seq h₁ h₂ =>
        exact ⟨_, h₁, h₂⟩
  · rintro ⟨K, h₁, h₂⟩
    exact BigStep.seq h₁ h₂

@[simp] theorem bigStep_ite_iff
    (G : Guard D Γ)
    (C₁ C₂ : Cmd D Γ)
    (I J : Instance D Γ) :
    BigStep (.ite G C₁ C₂) I J ↔
      (G.eval I ∧ BigStep C₁ I J) ∨
        (¬ G.eval I ∧ BigStep C₂ I J) := by
  constructor
  · intro h
    cases h with
    | ite_true hG hC =>
        exact Or.inl ⟨hG, hC⟩
    | ite_false hG hC =>
        exact Or.inr ⟨hG, hC⟩
  · intro h
    cases h with
    | inl h =>
        exact BigStep.ite_true h.1 h.2
    | inr h =>
        exact BigStep.ite_false h.1 h.2

@[simp] theorem bigStep_while_iff
    (G : Guard D Γ)
    (C : Cmd D Γ)
    (I J : Instance D Γ) :
    BigStep (.while G C) I J ↔
      (¬ G.eval I ∧ J = I) ∨
        ∃ K : Instance D Γ,
          G.eval I ∧
            BigStep C I K ∧ BigStep (.while G C) K J := by
  constructor
  · intro h
    cases h with
    | while_false hG =>
        exact Or.inl ⟨hG, rfl⟩
    | while_true hG hC hLoop =>
        exact Or.inr ⟨_, hG, hC, hLoop⟩
  · intro h
    cases h with
    | inl h =>
        rw [h.2]
        exact BigStep.while_false h.1
    | inr h =>
        rcases h with ⟨K, hG, hC, hLoop⟩
        exact BigStep.while_true hG hC hLoop

/- Terminating command runs have unique final instances. -/
theorem BigStep.deterministic
    {C : Cmd D Γ}
    {I J₁ J₂ : Instance D Γ}
    (h₁ : BigStep C I J₁)
    (h₂ : BigStep C I J₂) :
    J₁ = J₂ := by
  induction h₁ generalizing J₂ with
  | skip I =>
      cases h₂
      rfl
  | assign I X e =>
      cases h₂
      rfl
  | seq hStep₁ hStep₂ ih₁ ih₂ =>
      rw [bigStep_seq_iff] at h₂
      rcases h₂ with ⟨K, hOther₁, hOther₂⟩
      have hK := ih₁ hOther₁
      subst K
      exact ih₂ hOther₂
  | ite_true hG hStep ih =>
      rw [bigStep_ite_iff] at h₂
      cases h₂ with
      | inl hOther =>
          exact ih hOther.2
      | inr hOther =>
          exact False.elim (hOther.1 hG)
  | ite_false hG hStep ih =>
      rw [bigStep_ite_iff] at h₂
      cases h₂ with
      | inl hOther =>
          exact False.elim (hG hOther.1)
      | inr hOther =>
          exact ih hOther.2
  | while_false hG =>
      rw [bigStep_while_iff] at h₂
      cases h₂ with
      | inl hOther =>
          exact hOther.2.symm
      | inr hOther =>
          rcases hOther with ⟨_, hOtherG, _, _⟩
          exact False.elim (hG hOtherG)
  | while_true hG hStep hLoop ihStep ihLoop =>
      rw [bigStep_while_iff] at h₂
      cases h₂ with
      | inl hOther =>
          exact False.elim (hOther.1 hG)
      | inr hOther =>
          rcases hOther with ⟨K, _, hOtherStep, hOtherLoop⟩
          have hK := ihStep hOtherStep
          subst K
          exact ihLoop hOtherLoop

/-
  A command preserves every relation name that does not
  occur on the left-hand side of an assignment.
-/
theorem BigStep.no_update_preservation
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    (hStep : BigStep C I J)
    (X : Γ.syms)
    (hX : X.1 ∉ C.assignedSymbols) :
    J X = I X := by
  revert X
  induction hStep with
  | skip I =>
      intro X _
      rfl
  | assign I Y e =>
      intro X hX
      have hXY : X ≠ Y := by
        intro hEq
        apply hX
        simp [assignedSymbols, hEq]
      exact Instance.update_lookup_ne I Y X hXY (e.eval I)
  | seq hStep₁ hStep₂ ih₁ ih₂ =>
      intro X hX
      calc
        _ = _ := ih₂ X (by
          intro hMem
          apply hX
          simp [assignedSymbols, hMem])
        _ = _ := ih₁ X (by
          intro hMem
          apply hX
          simp [assignedSymbols, hMem])
  | ite_true hG hStep ih =>
      intro X hX
      exact ih X (by
        intro hMem
        apply hX
        simp [assignedSymbols, hMem])
  | ite_false hG hStep ih =>
      intro X hX
      exact ih X (by
        intro hMem
        apply hX
        simp [assignedSymbols, hMem])
  | while_false hG =>
      intro X _
      rfl
  | while_true hG hStep hLoop ihStep ihLoop =>
      intro X hX
      calc
        _ = _ := ihLoop X hX
        _ = _ := ihStep X hX

/- Big-step execution transports across a semantic frame. -/
theorem BigStep.frame
    {C : Cmd D Γ}
    {I I' J : Instance D Γ}
    {S : Finset A}
    (hSymbols : C.symbols ⊆ S)
    (hAgree : Instance.agreeOn S I I')
    (hStep : BigStep C I J) :
    ∃ J' : Instance D Γ,
      BigStep C I' J' ∧
        Instance.agreeOn S J J' := by
  induction hStep generalizing I' with
  | skip I =>
      exact ⟨I', BigStep.skip I', hAgree⟩
  | assign I X e =>
      let R := e.eval I
      have hX : X.1 ∈ S :=
        hSymbols (by simp [Cmd.symbols])
      have hExpr : e.symbols ⊆ S := by
        intro Y hY
        exact hSymbols (by simp [Cmd.symbols, hY])
      have hEval : e.eval I = e.eval I' := by
        apply RAExpr.eval_eq_of_agreeOn e
        intro Y hY
        exact hAgree Y (hExpr hY)
      refine
        ⟨Instance.update I' X (e.eval I'),
          BigStep.assign I' X e, ?_⟩
      intro Y hY
      by_cases hYX : Y = X
      · subst Y
        simp [Instance.update_lookup_eq, hEval]
      · simp [Instance.update_lookup_ne, hYX,
          hAgree Y hY]
  | @seq C₁ C₂ I K J h₁ h₂ ih₁ ih₂ =>
      have hSymbols₁ : C₁.symbols ⊆ S := by
        intro X hX
        exact hSymbols (by simp [Cmd.symbols, hX])
      have hSymbols₂ : C₂.symbols ⊆ S := by
        intro X hX
        exact hSymbols (by simp [Cmd.symbols, hX])
      rcases ih₁ hSymbols₁ hAgree with
        ⟨K', hStep₁, hAgreeK⟩
      rcases ih₂ hSymbols₂ hAgreeK with
        ⟨J', hStep₂, hAgreeJ⟩
      exact ⟨J', BigStep.seq hStep₁ hStep₂, hAgreeJ⟩
  | @ite_true G C₁ C₂ I J hG hC ih =>
      have hGuard : G.symbols ⊆ S := by
        intro X hX
        exact hSymbols (by simp [Cmd.symbols, hX])
      have hBranch : C₁.symbols ⊆ S := by
        intro X hX
        exact hSymbols (by simp [Cmd.symbols, hX])
      have hG' : G.eval I' :=
        (Guard.eval_reduct_property G (by
          intro X hX
          exact hAgree X (hGuard hX))).mp hG
      rcases ih hBranch hAgree with
        ⟨J', hStep', hAgreeJ⟩
      exact
        ⟨J', BigStep.ite_true hG' hStep', hAgreeJ⟩
  | @ite_false G C₁ C₂ I J hG hC ih =>
      have hGuard : G.symbols ⊆ S := by
        intro X hX
        exact hSymbols (by simp [Cmd.symbols, hX])
      have hBranch : C₂.symbols ⊆ S := by
        intro X hX
        exact hSymbols (by simp [Cmd.symbols, hX])
      have hG' : ¬ G.eval I' := by
        intro hEval
        apply hG
        exact
          (Guard.eval_reduct_property G (by
            intro X hX
            exact hAgree X (hGuard hX))).mpr hEval
      rcases ih hBranch hAgree with
        ⟨J', hStep', hAgreeJ⟩
      exact
        ⟨J', BigStep.ite_false hG' hStep', hAgreeJ⟩
  | @while_false G Body I hG =>
      have hGuard : G.symbols ⊆ S := by
        intro X hX
        exact hSymbols (by simp [Cmd.symbols, hX])
      have hG' : ¬ G.eval I' := by
        intro hEval
        apply hG
        exact
          (Guard.eval_reduct_property G (by
            intro X hX
            exact hAgree X (hGuard hX))).mpr hEval
      exact
        ⟨I', BigStep.while_false hG', hAgree⟩
  | @while_true G Body I K J hG hBody hLoop
      ihBody ihLoop =>
      have hGuard : G.symbols ⊆ S := by
        intro X hX
        exact hSymbols (by simp [Cmd.symbols, hX])
      have hBodySymbols : Body.symbols ⊆ S := by
        intro X hX
        exact hSymbols (by simp [Cmd.symbols, hX])
      have hG' : G.eval I' :=
        (Guard.eval_reduct_property G (by
          intro X hX
          exact hAgree X (hGuard hX))).mp hG
      rcases ihBody hBodySymbols hAgree with
        ⟨K', hBody', hAgreeK⟩
      rcases ihLoop hSymbols hAgreeK with
        ⟨J', hLoop', hAgreeJ⟩
      exact
        ⟨J', BigStep.while_true hG' hBody' hLoop',
          hAgreeJ⟩

end Cmd

end Whiel

------------------------------------------------------------
-- Program Semantic Support
------------------------------------------------------------

namespace Whiel

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Λ : UnnamedSchema A}

/- Initialize execution state by empty-expanding input. -/
def initialInstance
    (P : Program D Δ Λ)
    (I : Instance D Δ) :
    Instance D P.execSchema :=
  Instance.expandEmpty P.extendsInput I

/-
  Observe an execution instance through the output schema.
-/
def observe
    (P : Program D Δ Λ)
    (J : Instance D P.execSchema) :
    Instance D Λ :=
  Instance.reduct P.extendsOutput J

@[simp] theorem reduct_initialInstance
    (P : Program D Δ Λ)
    (I : Instance D Δ) :
    Instance.reduct P.extendsInput (P.initialInstance I) =
      I :=
  Instance.reduct_expandEmpty P.extendsInput I

end Program

end Whiel

------------------------------------------------------------
-- Program Big-Step Semantics
------------------------------------------------------------

namespace Whiel

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Λ : UnnamedSchema A}

/-
  Observational big-step semantics.

  `BigStep P I K` says that `P` terminates from external
  input `I` with observable final instance `K`.
-/
def BigStep
    (P : Program D Δ Λ)
    (I : Instance D Δ)
    (K : Instance D Λ) : Prop :=
  ∃ J : Instance D P.execSchema,
    Cmd.BigStep P.cmd (P.initialInstance I) J ∧
      P.observe J = K

/- Termination from an external input. -/
def Terminates
    (P : Program D Δ Λ)
    (I : Instance D Δ) : Prop :=
  ∃ K : Instance D Λ, P.BigStep I K

@[simp] theorem bigStep_iff
    (P : Program D Δ Λ)
    (I : Instance D Δ)
    (K : Instance D Λ) :
    P.BigStep I K ↔
      ∃ J : Instance D P.execSchema,
        Cmd.BigStep P.cmd (P.initialInstance I) J ∧
          P.observe J = K :=
  Iff.rfl

/- Observable final instances are unique. -/
theorem bigStep_unique
    (P : Program D Δ Λ)
    {I : Instance D Δ}
    {K₁ K₂ : Instance D Λ}
    (h₁ : P.BigStep I K₁)
    (h₂ : P.BigStep I K₂) :
    K₁ = K₂ := by
  rcases h₁ with ⟨J₁, hStep₁, hObs₁⟩
  rcases h₂ with ⟨J₂, hStep₂, hObs₂⟩
  have hJ : J₁ = J₂ :=
    Cmd.BigStep.deterministic hStep₁ hStep₂
  rw [← hObs₁, ← hObs₂, hJ]

end Program

end Whiel
