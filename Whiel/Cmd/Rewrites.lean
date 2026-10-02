import Whiel.Rewrites.UnnamedRA
import Whiel.Cmd.Semantics
import Whiel.Guard.Rewrites

/-
  Syntax-directed Whiel command rewrites.

  Key declarations:
    * `Whiel.Cmd.clean`
    * `Whiel.Cmd.bigStep_clean_iff`
-/

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Sequence two commands, deleting vacuous `skip`s and
  reassociating nested sequences to the right.
-/
def cleanSeq :
    Cmd D Γ → Cmd D Γ → Cmd D Γ
| .skip, C => C
| .seq C₁ C₂, C₃ =>
    cleanSeq C₁ (cleanSeq C₂ C₃)
| C, .skip => C
| C₁, C₂ => .seq C₁ C₂

/-
  Remove sequencing `skip`s, right-associate sequences, and
  clean embedded expressions.
-/
def clean :
    Cmd D Γ → Cmd D Γ
| .skip => .skip
| .assign X E => .assign X E.clean
| .seq C₁ C₂ => cleanSeq (clean C₁) (clean C₂)
| .ite G C₁ C₂ => .ite G.clean (clean C₁) (clean C₂)
| .while G C => .while G.clean (clean C)

/-
  Cleaning one sequence preserves the assigned relation
  names.
-/
@[simp] theorem assignedSymbols_cleanSeq
    (C₁ C₂ : Cmd D Γ) :
    (cleanSeq C₁ C₂).assignedSymbols =
      (.seq C₁ C₂ : Cmd D Γ).assignedSymbols := by
  induction C₁ generalizing C₂
  <;> cases C₂
  <;> simp [cleanSeq, assignedSymbols, *,
    Finset.union_assoc]

/- Cleaning preserves the assigned relation names. -/
@[simp] theorem assignedSymbols_clean
    (C : Cmd D Γ) :
    C.clean.assignedSymbols = C.assignedSymbols := by
  induction C with
  | skip =>
      simp [clean, assignedSymbols]
  | assign X E =>
      simp [clean, assignedSymbols]
  | seq C₁ C₂ ih₁ ih₂ =>
      simp [clean, assignedSymbols, ih₁, ih₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [clean, assignedSymbols, ih₁, ih₂]
  | «while» G C ih =>
      simp [clean, assignedSymbols, ih]

/- Cleaning one sequence preserves big-step semantics. -/
private theorem bigStep_skip_seq_iff
    (C : Cmd D Γ)
    (I J : Instance D Γ) :
    BigStep C I J ↔
      BigStep (.seq .skip C) I J := by
  constructor
  · intro h
    exact BigStep.seq (BigStep.skip I) h
  · intro h
    rw [bigStep_seq_iff] at h
    rcases h with ⟨K, hSkip, hC⟩
    rw [bigStep_skip_iff] at hSkip
    subst K
    exact hC

private theorem bigStep_seq_skip_iff
    (C : Cmd D Γ)
    (I J : Instance D Γ) :
    BigStep C I J ↔
      BigStep (.seq C .skip) I J := by
  constructor
  · intro h
    exact BigStep.seq h (BigStep.skip J)
  · intro h
    rw [bigStep_seq_iff] at h
    rcases h with ⟨K, hC, hSkip⟩
    rw [bigStep_skip_iff] at hSkip
    subst J
    exact hC

private theorem bigStep_seq_right_congr
    (C₁ : Cmd D Γ)
    {C₂ C₂' : Cmd D Γ}
    (h₂ : ∀ I J,
      BigStep C₂' I J ↔ BigStep C₂ I J)
    (I J : Instance D Γ) :
    BigStep (.seq C₁ C₂') I J ↔
      BigStep (.seq C₁ C₂) I J := by
  simp only [bigStep_seq_iff]
  constructor
  · rintro ⟨K, h₁, h₂'⟩
    exact ⟨K, h₁, (h₂ K J).mp h₂'⟩
  · rintro ⟨K, h₁, h₂'⟩
    exact ⟨K, h₁, (h₂ K J).mpr h₂'⟩

private theorem bigStep_seq_assoc_iff
    (C₁ C₂ C₃ : Cmd D Γ)
    (I J : Instance D Γ) :
    BigStep (.seq C₁ (.seq C₂ C₃)) I J ↔
      BigStep (.seq (.seq C₁ C₂) C₃) I J := by
  simp only [bigStep_seq_iff]
  constructor
  · rintro ⟨K, h₁, L, h₂, h₃⟩
    exact ⟨L, ⟨K, h₁, h₂⟩, h₃⟩
  · rintro ⟨L, ⟨K, h₁, h₂⟩, h₃⟩
    exact ⟨K, h₁, L, h₂, h₃⟩

theorem bigStep_cleanSeq_iff
    (C₁ C₂ : Cmd D Γ)
    (I J : Instance D Γ) :
    BigStep (cleanSeq C₁ C₂) I J ↔
      BigStep (.seq C₁ C₂) I J := by
  induction C₁ generalizing C₂ I J with
  | skip =>
      change
        BigStep C₂ I J ↔
          BigStep (.seq .skip C₂) I J
      exact bigStep_skip_seq_iff C₂ I J
  | assign X E =>
      cases C₂ with
      | skip =>
          change
            BigStep (.assign X E) I J ↔
              BigStep (.seq (.assign X E) .skip) I J
          exact bigStep_seq_skip_iff (.assign X E) I J
      | assign Y F =>
          rfl
      | seq C₂₁ C₂₂ =>
          rfl
      | ite G C₂₁ C₂₂ =>
          rfl
      | «while» G C₂ =>
          rfl
  | seq C₁₁ C₁₂ ih₁ ih₂ =>
      calc
        BigStep
            (cleanSeq C₁₁ (cleanSeq C₁₂ C₂)) I J ↔
          BigStep
            (.seq C₁₁ (cleanSeq C₁₂ C₂)) I J :=
          ih₁ (cleanSeq C₁₂ C₂) I J
        _ ↔
            BigStep (.seq C₁₁ (.seq C₁₂ C₂)) I J :=
          bigStep_seq_right_congr C₁₁
            (fun K L => ih₂ C₂ K L) I J
        _ ↔
            BigStep (.seq (.seq C₁₁ C₁₂) C₂) I J :=
          bigStep_seq_assoc_iff C₁₁ C₁₂ C₂ I J
  | ite G C₁₁ C₁₂ =>
      cases C₂ with
      | skip =>
          change
            BigStep (.ite G C₁₁ C₁₂) I J ↔
              BigStep (.seq (.ite G C₁₁ C₁₂) .skip) I J
          exact bigStep_seq_skip_iff (.ite G C₁₁ C₁₂) I J
      | assign Y F =>
          rfl
      | seq C₂₁ C₂₂ =>
          rfl
      | ite H C₂₁ C₂₂ =>
          rfl
      | «while» H C₂ =>
          rfl
  | «while» G C₁ =>
      cases C₂ with
      | skip =>
          change
            BigStep (.while G C₁) I J ↔
              BigStep (.seq (.while G C₁) .skip) I J
          exact bigStep_seq_skip_iff (.while G C₁) I J
      | assign Y F =>
          rfl
      | seq C₂₁ C₂₂ =>
          rfl
      | ite H C₂₁ C₂₂ =>
          rfl
      | «while» H C₂ =>
          rfl

private theorem bigStep_while_congr_forward
    {G G' : Guard D Γ}
    {C C' : Cmd D Γ}
    (hG : ∀ I, G'.eval I ↔ G.eval I)
    (hC : ∀ I J, BigStep C' I J ↔ BigStep C I J)
    {I J : Instance D Γ} :
    BigStep (.while G' C') I J →
      BigStep (.while G C) I J := by
  intro h
  generalize hW :
      (Whiel.Cmd.«while» G' C' : Cmd D Γ) = W at h
  induction h generalizing G G' C C' with
  | skip I =>
      cases hW
  | assign I X E =>
      cases hW
  | seq h₁ h₂ ih₁ ih₂ =>
      cases hW
  | ite_true hEval hStep ih =>
      cases hW
  | ite_false hEval hStep ih =>
      cases hW
  | while_false hFalse =>
      cases hW
      exact BigStep.while_false
        (fun hEval => hFalse ((hG _).mpr hEval))
  | while_true hEval hBody hLoop ihBody ihLoop =>
      cases hW
      exact BigStep.while_true
        ((hG _).mp hEval)
        ((hC _ _).mp hBody)
        (ihLoop hG hC rfl)

private theorem bigStep_while_congr_reverse
    {G G' : Guard D Γ}
    {C C' : Cmd D Γ}
    (hG : ∀ I, G'.eval I ↔ G.eval I)
    (hC : ∀ I J, BigStep C' I J ↔ BigStep C I J)
    {I J : Instance D Γ} :
    BigStep (.while G C) I J →
      BigStep (.while G' C') I J := by
  intro h
  generalize hW :
      (Whiel.Cmd.«while» G C : Cmd D Γ) = W at h
  induction h generalizing G G' C C' with
  | skip I =>
      cases hW
  | assign I X E =>
      cases hW
  | seq h₁ h₂ ih₁ ih₂ =>
      cases hW
  | ite_true hEval hStep ih =>
      cases hW
  | ite_false hEval hStep ih =>
      cases hW
  | while_false hFalse =>
      cases hW
      exact BigStep.while_false
        (fun hEval => hFalse ((hG _).mp hEval))
  | while_true hEval hBody hLoop ihBody ihLoop =>
      cases hW
      exact BigStep.while_true
        ((hG _).mpr hEval)
        ((hC _ _).mpr hBody)
        (ihLoop hG hC rfl)

/- Cleaning preserves big-step semantics. -/
theorem bigStep_clean_iff
    (C : Cmd D Γ)
    (I J : Instance D Γ) :
    BigStep C.clean I J ↔ BigStep C I J := by
  induction C generalizing I J with
  | skip =>
      simp [clean]
  | assign X E =>
      simp [clean, bigStep_assign_iff]
  | seq C₁ C₂ ih₁ ih₂ =>
      rw [clean]
      rw [bigStep_cleanSeq_iff]
      simp only [bigStep_seq_iff]
      constructor
      · rintro ⟨K, h₁, h₂⟩
        exact ⟨K, (ih₁ I K).mp h₁, (ih₂ K J).mp h₂⟩
      · rintro ⟨K, h₁, h₂⟩
        exact ⟨K, (ih₁ I K).mpr h₁, (ih₂ K J).mpr h₂⟩
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp only [clean, bigStep_ite_iff]
      constructor
      · rintro (⟨hG, h₁⟩ | ⟨hG, h₂⟩)
        · exact Or.inl
            ⟨(Guard.eval_clean_iff I G).mp hG,
              (ih₁ I J).mp h₁⟩
        · exact Or.inr
            ⟨fun hEval =>
                hG ((Guard.eval_clean_iff I G).mpr hEval),
              (ih₂ I J).mp h₂⟩
      · rintro (⟨hG, h₁⟩ | ⟨hG, h₂⟩)
        · exact Or.inl
            ⟨(Guard.eval_clean_iff I G).mpr hG,
              (ih₁ I J).mpr h₁⟩
        · exact Or.inr
            ⟨fun hEval =>
                hG ((Guard.eval_clean_iff I G).mp hEval),
              (ih₂ I J).mpr h₂⟩
  | «while» G C ih =>
      constructor
      · intro h
        exact
          bigStep_while_congr_forward
            (fun I => Guard.eval_clean_iff I G)
            (fun I J => ih I J)
            h
      · intro h
        exact
          bigStep_while_congr_reverse
            (fun I => Guard.eval_clean_iff I G)
            (fun I J => ih I J)
            h

end Cmd

end Whiel
