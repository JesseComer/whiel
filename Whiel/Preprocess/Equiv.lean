-- Author: Jesse Comer
import Whiel.Preprocess.Flags

/-
  Simulation and equivalence modulo flags.

  A command `W` over an extension `Ω` of `Δ` simulates a
  command `C` over `Δ` when every terminating run of `C`
  from the projection of an *arbitrary* state over `Ω` is
  matched by a run of `W` from that state whose projection
  is the same. Equivalence adds the converse. The
  quantification over arbitrary initial states, rather than
  over lifted ones, is what the loop congruence of the
  normalization theorem and the refutation transfer need.

  Key definitions include:
    * `Whiel.Preprocess.Simulates`
    * `Whiel.Preprocess.EquivMod`

  The main lemmas are:
    * `Whiel.Preprocess.EquivMod.compose`
    * `Whiel.Preprocess.equivMod_retag`
    * `Whiel.Preprocess.flagInit_raise_lower`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Simulation And Equivalence Modulo Flags
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Δ Ω : UnnamedSchema A}

/-
  `W` simulates `C` modulo the relations of `Ω` outside
  `Δ`: from every state over `Ω`, with its flags at
  arbitrary values, every run of `C` on the projection is
  matched by a run of `W` projecting to it.
-/
def Simulates
    (hExt : Ω.extensionOf Δ)
    (C : Cmd D Δ)
    (W : Cmd D Ω) : Prop :=
  ∀ (s : Instance D Ω) (t : Instance D Δ),
    Cmd.BigStep C (project hExt s) t →
      ∃ t' : Instance D Ω,
        Cmd.BigStep W s t' ∧ project hExt t' = t

/-
  `W` is equivalent to `C` modulo those relations: it
  simulates `C`, and every run of `W` projects to a run of
  `C`.
-/
def EquivMod
    (hExt : Ω.extensionOf Δ)
    (C : Cmd D Δ)
    (W : Cmd D Ω) : Prop :=
  Simulates hExt C W ∧
    ∀ s t' : Instance D Ω,
      Cmd.BigStep W s t' →
        Cmd.BigStep C (project hExt s) (project hExt t')

theorem EquivMod.simulates
    {hExt : Ω.extensionOf Δ}
    {C : Cmd D Δ}
    {W : Cmd D Ω}
    (hEquiv : EquivMod hExt C W) :
    Simulates hExt C W :=
  hEquiv.1

theorem EquivMod.projectRun
    {hExt : Ω.extensionOf Δ}
    {C : Cmd D Δ}
    {W : Cmd D Ω}
    (hEquiv : EquivMod hExt C W)
    {s t' : Instance D Ω}
    (hStep : Cmd.BigStep W s t') :
    Cmd.BigStep C
      (Preprocess.project hExt s)
      (Preprocess.project hExt t') :=
  hEquiv.2 s t' hStep

/-
  Equivalence modulo the empty flag set is plain big-step
  equivalence.
-/
theorem equivMod_refl_of_bigStepEquiv
    {C W : Cmd D Δ}
    (hEquiv : Cmd.BigStepEquiv C W) :
    EquivMod (UnnamedSchema.extensionOf_refl Δ) C W := by
  have hProject :
      ∀ I : Instance D Δ,
        project (D := D)
          (UnnamedSchema.extensionOf_refl Δ) I = I := by
    intro I
    exact Instance.reduct_refl I
  constructor
  · intro s t hStep
    refine ⟨t, ?_, hProject t⟩
    rw [hProject s] at hStep
    exact (hEquiv s t).mp hStep
  · intro s t' hStep
    rw [hProject s, hProject t']
    exact (hEquiv s t').mpr hStep

end Preprocess

end Whiel

------------------------------------------------------------
-- Composition
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Δ Ω : UnnamedSchema A}

/-
  Lemma "Composition": equivalences modulo nested flag
  extensions compose to an equivalence modulo their union.
-/
theorem EquivMod.compose
    {hΔΓ : Δ.extensionOf Γ}
    {hΩΔ : Ω.extensionOf Δ}
    {hΩΓ : Ω.extensionOf Γ}
    {C : Cmd D Γ}
    {W : Cmd D Δ}
    {V : Cmd D Ω}
    (hCW : EquivMod hΔΓ C W)
    (hWV : EquivMod hΩΔ W V) :
    EquivMod hΩΓ C V := by
  have hSplit :
      ∀ s : Instance D Ω,
        Preprocess.project hΩΓ s =
          Preprocess.project hΔΓ
            (Preprocess.project hΩΔ s) := by
    intro s
    unfold Preprocess.project
    rw [Instance.reduct_trans hΩΔ hΔΓ s]
  constructor
  · intro s t hStep
    rw [hSplit s] at hStep
    rcases
      hCW.simulates (Preprocess.project hΩΔ s) t
        hStep with ⟨u, hU, hUR⟩
    rcases hWV.simulates s u hU with ⟨v, hV, hVR⟩
    refine ⟨v, hV, ?_⟩
    rw [hSplit v, hVR, hUR]
  · intro s t' hStep
    have hW := hWV.projectRun hStep
    have hC := hCW.projectRun hW
    rw [hSplit s, hSplit t']
    exact hC

/-
  Simulation composes in the same way; only the simulation
  half is used by the transfer theorem.
-/
theorem Simulates.compose
    {hΔΓ : Δ.extensionOf Γ}
    {hΩΔ : Ω.extensionOf Δ}
    {hΩΓ : Ω.extensionOf Γ}
    {C : Cmd D Γ}
    {W : Cmd D Δ}
    {V : Cmd D Ω}
    (hCW : Simulates hΔΓ C W)
    (hWV : Simulates hΩΔ W V) :
    Simulates hΩΓ C V := by
  have hSplit :
      ∀ s : Instance D Ω,
        project hΩΓ s =
          project hΔΓ (project hΩΔ s) := by
    intro s
    unfold project
    rw [Instance.reduct_trans hΩΔ hΔΓ s]
  intro s t hStep
  rw [hSplit s] at hStep
  rcases hCW (project hΩΔ s) t hStep with ⟨u, hU, hUR⟩
  rcases hWV s u hU with ⟨v, hV, hVR⟩
  refine ⟨v, hV, ?_⟩
  rw [hSplit v, hVR, hUR]

end Preprocess

end Whiel

------------------------------------------------------------
-- Retagging Is An Equivalence Modulo Flags
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- A retagged command is equivalent to its original. -/
theorem equivMod_retag
    (hExt : Ω.extensionOf Δ)
    (C : Cmd D Δ) :
    EquivMod hExt C (retag hExt C) := by
  constructor
  · intro s t hStep
    exact retag_bigStep_lift hExt rfl hStep
  · intro s t' hStep
    exact retag_bigStep_project hExt hStep

/-
  A retagged command is equivalent modulo flags to any
  big-step equivalent command over the smaller schema.
-/
theorem equivMod_retag_of_bigStepEquiv
    (hExt : Ω.extensionOf Δ)
    {C W : Cmd D Δ}
    (hEquiv : Cmd.BigStepEquiv C W) :
    EquivMod hExt C (retag hExt W) := by
  constructor
  · intro s t hStep
    exact
      retag_bigStep_lift hExt rfl
        ((hEquiv _ t).mp hStep)
  · intro s t' hStep
    exact
      (hEquiv _ _).mpr
        (retag_bigStep_project hExt hStep)

end Preprocess

end Whiel

------------------------------------------------------------
-- The Flag-Initialization Principle
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  A prefix that runs source code and then raises one flag
  reaches a state whose flag is up whatever the initial
  state carried, and whose projection is the source
  successor.
-/
theorem flagInit_raise
    (hExt : Ω.extensionOf Δ)
    {f : FlagSym Ω}
    (hFresh : f.sym.1 ∉ Δ.syms)
    {Q : Cmd D Δ}
    {s u : Instance D Ω}
    (hStep :
      Cmd.BigStep (.seq (retag hExt Q) f.raise) s u) :
    f.Up u ∧
      Cmd.BigStep Q (project hExt s) (project hExt u) := by
  rcases (Cmd.bigStep_seq_iff _ _ s u).mp hStep with
    ⟨m, hQ, hRaise⟩
  refine ⟨FlagSym.up_of_bigStep_raise hRaise, ?_⟩
  have hProject :
      project hExt u = project hExt m := by
    rw [FlagSym.bigStep_raise_iff] at hRaise
    subst hRaise
    exact project_update_of_not_mem hExt hFresh m _
  rw [hProject]
  exact retag_bigStep_project hExt hQ

/-
  The two-flag initialization the sequence merge performs:
  the first flag is up, the second is down, and the
  projection is the source successor.
-/
theorem flagInit_raise_lower
    (hExt : Ω.extensionOf Δ)
    {f₁ f₂ : FlagSym Ω}
    (hFresh₁ : f₁.sym.1 ∉ Δ.syms)
    (hFresh₂ : f₂.sym.1 ∉ Δ.syms)
    (hNe : f₁.sym ≠ f₂.sym)
    {Q : Cmd D Δ}
    {s u : Instance D Ω}
    (hStep :
      Cmd.BigStep
        (.seq (retag hExt Q)
          (.seq f₁.raise f₂.lower)) s u) :
    f₁.Up u ∧ ¬ f₂.Up u ∧
      Cmd.BigStep Q (project hExt s) (project hExt u) := by
  rcases (Cmd.bigStep_seq_iff _ _ s u).mp hStep with
    ⟨m, hQ, hFlags⟩
  rcases (Cmd.bigStep_seq_iff _ _ m u).mp hFlags with
    ⟨m₁, hRaise, hLower⟩
  have hUpOne : f₁.Up m₁ :=
    FlagSym.up_of_bigStep_raise hRaise
  refine
    ⟨(FlagSym.up_congr_of_bigStep_lower_ne hNe
        hLower).mpr hUpOne,
      FlagSym.not_up_of_bigStep_lower hLower, ?_⟩
  have hProjectOne : project hExt m₁ = project hExt m := by
    rw [FlagSym.bigStep_raise_iff] at hRaise
    subst hRaise
    exact project_update_of_not_mem hExt hFresh₁ m _
  have hProjectTwo : project hExt u = project hExt m₁ := by
    rw [FlagSym.bigStep_lower_iff] at hLower
    subst hLower
    exact project_update_of_not_mem hExt hFresh₂ m₁ _
  rw [hProjectTwo, hProjectOne]
  exact retag_bigStep_project hExt hQ

end Preprocess

end Whiel
