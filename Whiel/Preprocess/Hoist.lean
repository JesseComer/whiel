-- Author: Jesse Comer
import Whiel.Preprocess.Equiv

/-
  The conditional hoist of two framed loops.

  A conditional whose branches are framed loops becomes one
  framed loop over one fresh flag. The flag records the
  branch taken: it is set once, in the prefix, and read by
  the guard, the body and the suffix. No phase flag is
  needed, because the branches are exclusive, and the
  source guard is evaluated once, before either branch
  prefix runs. A loop-free branch goes to the *suffix*
  under the flag, and when neither branch has a loop the
  conditional needs no flag at all.

  Key definitions include:
    * `Whiel.Preprocess.hoistGeneral`
    * `Whiel.Preprocess.hoistThenLoop`
    * `Whiel.Preprocess.hoistElseLoop`
    * `Whiel.Preprocess.hoistFlagFree`
    * `Whiel.Preprocess.hoistIte`

  Correctness is proven by:
    * `Whiel.Preprocess.hoistIte_equivMod`
    * `Whiel.Preprocess.hoistIte_flag_records_branch`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- The Hoist Operations
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  The hoist prefix: evaluate the source guard once, run the
  chosen branch's prefix, and set the flag to the branch
  taken. Both branches are kept in every case.
-/
def hoistInit
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ) :
    Cmd D Ω :=
  .ite (G.onExtension hExt)
    (.seq (retag hExt L₁.init) f.raise)
    (.seq (retag hExt L₂.init) f.lower)

/- The hoist suffix: the taken branch's own suffix. -/
def hoistClose
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (L₁ L₂ : Framed D Δ) :
    Cmd D Ω :=
  .ite f.test (retag hExt L₁.close)
    (retag hExt L₂.close)

/- The hoist body of the general case. -/
def hoistBody
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (L₁ L₂ : Framed D Δ) :
    Cmd D Ω :=
  .ite f.test (retag hExt L₁.body) (retag hExt L₂.body)

/- The hoist guard of the general case. -/
def hoistGuard
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (L₁ L₂ : Framed D Δ) :
    Guard D Ω :=
  .or (.and f.test (L₁.guard.onExtension hExt))
    (.and (.not f.test) (L₂.guard.onExtension hExt))

/-
  The hoisted framed loop with a given guard and body. The
  prefix and the suffix are the same in all three flagged
  cases; only the guard and the body are simplified.
-/
def hoistOf
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ)
    (Gu : Guard D Ω)
    (Bo : Cmd D Ω) :
    Framed D Ω where
  init := hoistInit hExt f G L₁ L₂
  guard := Gu
  body := Bo
  close := hoistClose hExt f L₁ L₂

@[simp] theorem hoistOf_init
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ)
    (Gu : Guard D Ω)
    (Bo : Cmd D Ω) :
    (hoistOf hExt f G L₁ L₂ Gu Bo).init =
      hoistInit hExt f G L₁ L₂ :=
  rfl

@[simp] theorem hoistOf_close
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ)
    (Gu : Guard D Ω)
    (Bo : Cmd D Ω) :
    (hoistOf hExt f G L₁ L₂ Gu Bo).close =
      hoistClose hExt f L₁ L₂ :=
  rfl

/- The hoist when both source branches contain a loop. -/
def hoistGeneral
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ) :
    Framed D Ω :=
  hoistOf hExt f G L₁ L₂ (hoistGuard hExt f L₁ L₂)
    (hoistBody hExt f L₁ L₂)

/-
  The hoist when only the then-branch contains a loop: the
  else-branch is loop-free, so its source goes to the
  suffix under the flag.
-/
def hoistThenLoop
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ) :
    Framed D Ω :=
  hoistOf hExt f G L₁ L₂
    (.and f.test (L₁.guard.onExtension hExt))
    (retag hExt L₁.body)

/- The mirror case: only the else-branch has a loop. -/
def hoistElseLoop
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ) :
    Framed D Ω :=
  hoistOf hExt f G L₁ L₂
    (.and (.not f.test) (L₂.guard.onExtension hExt))
    (retag hExt L₂.body)

/-
  The flag-free case: neither branch contains a loop, so
  the conditional is its own base framed loop.
-/
def hoistFlagFree
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ) :
    Framed D Δ :=
  Framed.base (.ite G L₁.close L₂.close)

/-
  The conditional hoist. The two Booleans are computed from
  the source branches by the caller and are never read off
  the framed loops; the priority is the flag-free case
  first, then the two one-branch simplifications, then the
  general case.
-/
def hoistIte
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ)
    (loopFreeThen loopFreeElse : Bool) :
    Framed D Ω :=
  if loopFreeThen then
    if loopFreeElse then
      (hoistFlagFree G L₁ L₂).retagOn hExt
    else
      hoistElseLoop hExt f G L₁ L₂
  else if loopFreeElse then
    hoistThenLoop hExt f G L₁ L₂
  else
    hoistGeneral hExt f G L₁ L₂

/- The flag-free case does not mention the drawn flag. -/
theorem hoistIte_eq_flagFree
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ) :
    hoistIte hExt f G L₁ L₂ true true =
      (hoistFlagFree G L₁ L₂).retagOn hExt :=
  rfl

theorem hoistIte_eq_elseLoop
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ) :
    hoistIte hExt f G L₁ L₂ true false =
      hoistElseLoop hExt f G L₁ L₂ :=
  rfl

theorem hoistIte_eq_thenLoop
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ) :
    hoistIte hExt f G L₁ L₂ false true =
      hoistThenLoop hExt f G L₁ L₂ :=
  rfl

theorem hoistIte_eq_general
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ) :
    hoistIte hExt f G L₁ L₂ false false =
      hoistGeneral hExt f G L₁ L₂ :=
  rfl

end Preprocess

end Whiel

------------------------------------------------------------
-- Lowering A Flag In A Prefix
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  The flag-initialization principle for the branch that
  lowers: after source code and a lowering, the flag is
  down whatever the initial state carried, and the
  projection is the source successor.
-/
theorem flagInit_lower
    (hExt : Ω.extensionOf Δ)
    {f : FlagSym Ω}
    (hFresh : f.sym.1 ∉ Δ.syms)
    {Q : Cmd D Δ}
    {s u : Instance D Ω}
    (hStep :
      Cmd.BigStep (.seq (retag hExt Q) f.lower) s u) :
    ¬ f.Up u ∧
      Cmd.BigStep Q (project hExt s) (project hExt u) := by
  rcases (Cmd.bigStep_seq_iff _ _ s u).mp hStep with
    ⟨m, hQ, hLower⟩
  refine ⟨FlagSym.not_up_of_bigStep_lower hLower, ?_⟩
  have hProject :
      project hExt u = project hExt m := by
    rw [FlagSym.bigStep_lower_iff] at hLower
    subst hLower
    exact project_update_of_not_mem hExt hFresh m _
  rw [hProject]
  exact retag_bigStep_project hExt hQ

end Preprocess

end Whiel

------------------------------------------------------------
-- Loops Under A Stable Condition
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- A loop whose guard is false runs from a state to it. -/
theorem bigStep_while_eq_of_not_eval
    {Gu : Guard D Ω}
    {Bo : Cmd D Ω}
    {u v : Instance D Ω}
    (hStep : Cmd.BigStep (.«while» Gu Bo) u v)
    (hFalse : ¬ Gu.eval u) :
    v = u := by
  cases hStep with
  | while_false hG => rfl
  | while_true hG hBody hLoop => exact absurd hG hFalse

/- The unfolding of a base framed loop is its suffix. -/
theorem bigStep_unfold_iff_of_isBase
    {L : Framed D Δ}
    (hBase : L.IsBase)
    (I J : Instance D Δ) :
    Cmd.BigStep L.unfold I J ↔
      Cmd.BigStep L.close I J := by
  obtain ⟨hInit, hGuard, hBody⟩ := hBase
  rw [Framed.bigStep_unfold_iff, hInit, hGuard, hBody]
  constructor
  · rintro ⟨K₁, K₂, h₁, h₂, h₃⟩
    have hK₁ : K₁ = I :=
      (Cmd.bigStep_skip_iff I K₁).mp h₁
    subst hK₁
    have hK₂ : K₂ = K₁ :=
      (Framed.bigStep_while_false_iff _ K₁ K₂).mp h₂
    subst hK₂
    exact h₃
  · intro h
    exact
      ⟨I, I, Cmd.BigStep.skip I,
        (Framed.bigStep_while_false_iff _ I I).mpr rfl,
        h⟩

/-
  A loop over the extension that agrees with a source loop
  at every state satisfying a run-stable condition projects
  to a run of that source loop.
-/
theorem flagLoop_project
    (hExt : Ω.extensionOf Δ)
    (Ph : Instance D Ω → Prop)
    (Gu : Guard D Ω)
    (Bo : Cmd D Ω)
    (H : Guard D Δ)
    (B : Cmd D Δ)
    (hGuard :
      ∀ I : Instance D Ω, Ph I →
        (Gu.eval I ↔ H.eval (project hExt I)))
    (hBody :
      ∀ I J : Instance D Ω, Ph I →
        Cmd.BigStep Bo I J →
          Cmd.BigStep (retag hExt B) I J)
    (hPres :
      ∀ I J : Instance D Ω, Ph I →
        Cmd.BigStep (retag hExt B) I J → Ph J)
    {u v : Instance D Ω}
    (hStep : Cmd.BigStep (.«while» Gu Bo) u v) :
    Ph u →
      Cmd.BigStep (.«while» H B) (project hExt u)
          (project hExt v) ∧
        Ph v := by
  generalize hW :
      (Cmd.«while» Gu Bo : Cmd D Ω) = W at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false G' C' u hFalse =>
      cases hW
      intro hPh
      refine ⟨Cmd.BigStep.while_false ?_, hPh⟩
      intro hEval
      exact hFalse ((hGuard u hPh).mpr hEval)
  | @while_true G' C' u m v hEval hRun hLoop ihRun
      ihLoop =>
      cases hW
      intro hPh
      have hSrc : Cmd.BigStep (retag hExt B) u m :=
        hBody u m hPh hRun
      have hPhM : Ph m := hPres u m hPh hSrc
      rcases ihLoop rfl hPhM with ⟨hLoopRun, hPhV⟩
      refine ⟨?_, hPhV⟩
      exact
        Cmd.BigStep.while_true ((hGuard u hPh).mp hEval)
          (retag_bigStep_project hExt hSrc) hLoopRun

/-
  The same agreement, read backwards: a run of the source
  loop lifts to a run of the extended loop from any state
  satisfying the condition.
-/
theorem flagLoop_lift
    (hExt : Ω.extensionOf Δ)
    (Ph : Instance D Ω → Prop)
    (Gu : Guard D Ω)
    (Bo : Cmd D Ω)
    (H : Guard D Δ)
    (B : Cmd D Δ)
    (hGuard :
      ∀ I : Instance D Ω, Ph I →
        (Gu.eval I ↔ H.eval (project hExt I)))
    (hBody :
      ∀ I J : Instance D Ω, Ph I →
        Cmd.BigStep (retag hExt B) I J →
          Cmd.BigStep Bo I J)
    (hPres :
      ∀ I J : Instance D Ω, Ph I →
        Cmd.BigStep (retag hExt B) I J → Ph J)
    {s t : Instance D Δ}
    (hStep : Cmd.BigStep (.«while» H B) s t) :
    ∀ u : Instance D Ω, project hExt u = s → Ph u →
      ∃ v : Instance D Ω,
        Cmd.BigStep (.«while» Gu Bo) u v ∧
          project hExt v = t ∧ Ph v := by
  generalize hW :
      (Cmd.«while» H B : Cmd D Δ) = W at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false G' C' s hFalse =>
      cases hW
      intro u hProj hPh
      refine ⟨u, Cmd.BigStep.while_false ?_, hProj, hPh⟩
      intro hEval
      refine hFalse ?_
      rw [← hProj]
      exact (hGuard u hPh).mp hEval
  | @while_true G' C' s a t hEval hRun hLoop ihRun
      ihLoop =>
      cases hW
      intro u hProj hPh
      rcases retag_bigStep_lift hExt hProj hRun with
        ⟨m, hRunΩ, hProjM⟩
      have hPhM : Ph m := hPres u m hPh hRunΩ
      rcases ihLoop rfl m hProjM hPhM with
        ⟨v, hV, hProjV, hPhV⟩
      refine ⟨v, ?_, hProjV, hPhV⟩
      refine
        Cmd.BigStep.while_true ?_ (hBody u m hPh hRunΩ)
          hV
      refine (hGuard u hPh).mpr ?_
      rw [hProj]
      exact hEval

end Preprocess

end Whiel

------------------------------------------------------------
-- The Guards And Bodies Of The Hoisted Loop
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- The general hoist guard, spelled out. -/
theorem hoistGuard_iff
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (L₁ L₂ : Framed D Δ)
    (I : Instance D Ω) :
    (hoistGuard hExt f L₁ L₂).eval I ↔
      (f.Up I ∧
          (L₁.guard.onExtension hExt).eval I) ∨
        (¬ f.Up I ∧
          (L₂.guard.onExtension hExt).eval I) :=
  Iff.rfl

/- With the flag up the general guard is the first one. -/
theorem hoistGuard_eval_up
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (L₁ L₂ : Framed D Δ)
    (I : Instance D Ω)
    (hUp : f.Up I) :
    (hoistGuard hExt f L₁ L₂).eval I ↔
      L₁.guard.eval (project hExt I) := by
  rw [hoistGuard_iff, ← retag_eval_iff hExt L₁.guard I]
  constructor
  · rintro (⟨_, hG⟩ | ⟨hDown, _⟩)
    · exact hG
    · exact absurd hUp hDown
  · intro hG
    exact Or.inl ⟨hUp, hG⟩

/- With the flag down it is the second one. -/
theorem hoistGuard_eval_down
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (L₁ L₂ : Framed D Δ)
    (I : Instance D Ω)
    (hDown : ¬ f.Up I) :
    (hoistGuard hExt f L₁ L₂).eval I ↔
      L₂.guard.eval (project hExt I) := by
  rw [hoistGuard_iff, ← retag_eval_iff hExt L₂.guard I]
  constructor
  · rintro (⟨hUp, _⟩ | ⟨_, hG⟩)
    · exact absurd hUp hDown
    · exact hG
  · intro hG
    exact Or.inr ⟨hDown, hG⟩

/- The one-branch guards, spelled out. -/
theorem hoistThenGuard_iff
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (L₁ : Framed D Δ)
    (I : Instance D Ω) :
    (Guard.and f.test (L₁.guard.onExtension hExt)).eval
        I ↔
      (f.Up I ∧ (L₁.guard.onExtension hExt).eval I) :=
  Iff.rfl

theorem hoistElseGuard_iff
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (L₂ : Framed D Δ)
    (I : Instance D Ω) :
    (Guard.and (.not f.test)
          (L₂.guard.onExtension hExt)).eval I ↔
      (¬ f.Up I ∧
        (L₂.guard.onExtension hExt).eval I) :=
  Iff.rfl

/- The general body runs the first branch's body. -/
theorem hoistBody_iff_up
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (L₁ L₂ : Framed D Δ)
    (I J : Instance D Ω)
    (hUp : f.Up I) :
    Cmd.BigStep (hoistBody hExt f L₁ L₂) I J ↔
      Cmd.BigStep (retag hExt L₁.body) I J := by
  rw [hoistBody, Cmd.bigStep_ite_iff]
  constructor
  · rintro (⟨_, hRun⟩ | ⟨hDown, _⟩)
    · exact hRun
    · exact absurd hUp hDown
  · intro hRun
    exact Or.inl ⟨hUp, hRun⟩

/- With the flag down it runs the second branch's. -/
theorem hoistBody_iff_down
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (L₁ L₂ : Framed D Δ)
    (I J : Instance D Ω)
    (hDown : ¬ f.Up I) :
    Cmd.BigStep (hoistBody hExt f L₁ L₂) I J ↔
      Cmd.BigStep (retag hExt L₂.body) I J := by
  rw [hoistBody, Cmd.bigStep_ite_iff]
  constructor
  · rintro (⟨hUp, _⟩ | ⟨_, hRun⟩)
    · exact absurd hUp hDown
    · exact hRun
  · intro hRun
    exact Or.inr ⟨hDown, hRun⟩

/- A retagged branch body keeps the flag up. -/
theorem hoist_up_pres
    (hExt : Ω.extensionOf Δ)
    {f : FlagSym Ω}
    (hFresh : f.sym.1 ∉ Δ.syms)
    (B : Cmd D Δ)
    (I J : Instance D Ω)
    (hUp : f.Up I)
    (hRun : Cmd.BigStep (retag hExt B) I J) :
    f.Up J :=
  (up_congr_retag hExt hFresh hRun).mpr hUp

/- A retagged branch body keeps the flag down. -/
theorem hoist_down_pres
    (hExt : Ω.extensionOf Δ)
    {f : FlagSym Ω}
    (hFresh : f.sym.1 ∉ Δ.syms)
    (B : Cmd D Δ)
    (I J : Instance D Ω)
    (hDown : ¬ f.Up I)
    (hRun : Cmd.BigStep (retag hExt B) I J) :
    ¬ f.Up J := by
  intro hUp
  exact hDown ((up_congr_retag hExt hFresh hRun).mp hUp)

end Preprocess

end Whiel

------------------------------------------------------------
-- The Hoist Lemma
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  Lemma "Hoist" in the arbitrary-start form, from the four
  facts that the hoisted loop is the first branch's loop
  while the flag is up and the second branch's loop while
  it is down.
-/
theorem hoistOf_equivMod
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ)
    (Gu : Guard D Ω)
    (Bo : Cmd D Ω)
    (hUpProject :
      ∀ u v : Instance D Ω, f.Up u →
        Cmd.BigStep (.«while» Gu Bo) u v →
          Cmd.BigStep (.«while» L₁.guard L₁.body)
              (project hExt u) (project hExt v) ∧
            f.Up v)
    (hDownProject :
      ∀ u v : Instance D Ω, ¬ f.Up u →
        Cmd.BigStep (.«while» Gu Bo) u v →
          Cmd.BigStep (.«while» L₂.guard L₂.body)
              (project hExt u) (project hExt v) ∧
            ¬ f.Up v)
    (hUpLift :
      ∀ s t : Instance D Δ,
        Cmd.BigStep
            (.«while» L₁.guard L₁.body) s t →
          ∀ u : Instance D Ω, project hExt u = s →
            f.Up u →
              ∃ v : Instance D Ω,
                Cmd.BigStep (.«while» Gu Bo) u v ∧
                  project hExt v = t ∧ f.Up v)
    (hDownLift :
      ∀ s t : Instance D Δ,
        Cmd.BigStep
            (.«while» L₂.guard L₂.body) s t →
          ∀ u : Instance D Ω, project hExt u = s →
            ¬ f.Up u →
              ∃ v : Instance D Ω,
                Cmd.BigStep (.«while» Gu Bo) u v ∧
                  project hExt v = t ∧ ¬ f.Up v) :
    EquivMod hExt (.ite G L₁.unfold L₂.unfold)
      (hoistOf hExt f G L₁ L₂ Gu Bo).unfold := by
  constructor
  · intro s t hRun
    rcases
      (Cmd.bigStep_ite_iff G L₁.unfold L₂.unfold
        (project hExt s) t).mp hRun with hT | hF
    · rcases
        (Framed.bigStep_unfold_iff L₁ (project hExt s)
          t).mp hT.2 with
        ⟨x₁, x₂, hInit, hLoop, hClose⟩
      rcases retag_bigStep_lift hExt rfl hInit with
        ⟨u₀, hInitRun, hProjZero⟩
      have hRaise :
          Cmd.BigStep f.raise u₀
            (Instance.update u₀ f.sym
              (f.topExpr.eval u₀)) :=
        Cmd.BigStep.assign u₀ f.sym f.topExpr
      set u₁ :=
        Instance.update u₀ f.sym
          (f.topExpr.eval u₀) with hu₁
      have hUp : f.Up u₁ :=
        FlagSym.up_of_bigStep_raise hRaise
      have hProjOne : project hExt u₁ = x₁ := by
        rw [project_of_bigStep_raise hExt hFresh hRaise,
          hProjZero]
      rcases hUpLift x₁ x₂ hLoop u₁ hProjOne hUp with
        ⟨v, hV, hProjV, hUpV⟩
      rcases retag_bigStep_lift hExt hProjV hClose with
        ⟨w, hCloseRun, hProjW⟩
      refine ⟨w, ?_, hProjW⟩
      refine
        (Framed.bigStep_unfold_iff _ s w).mpr
          ⟨u₁, v, ?_, hV, ?_⟩
      · refine
          Cmd.BigStep.ite_true ?_
            (Cmd.BigStep.seq hInitRun hRaise)
        exact (retag_eval_iff hExt G s).mpr hT.1
      · exact Cmd.BigStep.ite_true hUpV hCloseRun
    · rcases
        (Framed.bigStep_unfold_iff L₂ (project hExt s)
          t).mp hF.2 with
        ⟨x₁, x₂, hInit, hLoop, hClose⟩
      rcases retag_bigStep_lift hExt rfl hInit with
        ⟨u₀, hInitRun, hProjZero⟩
      have hLower :
          Cmd.BigStep f.lower u₀
            (Instance.update u₀ f.sym
              (f.emptyExpr.eval u₀)) :=
        Cmd.BigStep.assign u₀ f.sym f.emptyExpr
      set u₁ :=
        Instance.update u₀ f.sym
          (f.emptyExpr.eval u₀) with hu₁
      have hDown : ¬ f.Up u₁ :=
        FlagSym.not_up_of_bigStep_lower hLower
      have hProjOne : project hExt u₁ = x₁ := by
        rw [project_of_bigStep_lower hExt hFresh hLower,
          hProjZero]
      rcases
        hDownLift x₁ x₂ hLoop u₁ hProjOne hDown with
        ⟨v, hV, hProjV, hDownV⟩
      rcases retag_bigStep_lift hExt hProjV hClose with
        ⟨w, hCloseRun, hProjW⟩
      refine ⟨w, ?_, hProjW⟩
      refine
        (Framed.bigStep_unfold_iff _ s w).mpr
          ⟨u₁, v, ?_, hV, ?_⟩
      · refine
          Cmd.BigStep.ite_false ?_
            (Cmd.BigStep.seq hInitRun hLower)
        intro hEval
        exact hF.1 ((retag_eval_iff hExt G s).mp hEval)
      · exact Cmd.BigStep.ite_false hDownV hCloseRun
  · intro s t hRun
    rcases (Framed.bigStep_unfold_iff _ s t).mp hRun with
      ⟨u, v, hInit, hLoop, hClose⟩
    rcases
      (Cmd.bigStep_ite_iff _ _ _ s u).mp hInit with
      hT | hF
    · rcases flagInit_raise hExt hFresh hT.2 with
        ⟨hUp, hInitRun⟩
      rcases hUpProject u v hUp hLoop with
        ⟨hLoopRun, hUpV⟩
      rcases
        (Cmd.bigStep_ite_iff _ _ _ v t).mp hClose with
        hC | hC
      · refine Cmd.BigStep.ite_true ?_ ?_
        · exact (retag_eval_iff hExt G s).mp hT.1
        · exact
            (Framed.bigStep_unfold_iff L₁ _ _).mpr
              ⟨project hExt u, project hExt v, hInitRun,
                hLoopRun,
                retag_bigStep_project hExt hC.2⟩
      · exact absurd hUpV hC.1
    · rcases flagInit_lower hExt hFresh hF.2 with
        ⟨hDown, hInitRun⟩
      rcases hDownProject u v hDown hLoop with
        ⟨hLoopRun, hDownV⟩
      rcases
        (Cmd.bigStep_ite_iff _ _ _ v t).mp hClose with
        hC | hC
      · exact absurd hC.1 hDownV
      · refine Cmd.BigStep.ite_false ?_ ?_
        · intro hEval
          exact hF.1 ((retag_eval_iff hExt G s).mpr hEval)
        · exact
            (Framed.bigStep_unfold_iff L₂ _ _).mpr
              ⟨project hExt u, project hExt v, hInitRun,
                hLoopRun,
                retag_bigStep_project hExt hC.2⟩

/-
  The exit status of a hoist flag. The note makes no claim
  that the flag is down at exit; what holds is that at
  every terminal state the flag records the branch taken,
  that is, it is up exactly when the source guard held at
  the initial state.
-/
theorem hoistOf_flag_records_branch
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ)
    (Gu : Guard D Ω)
    (Bo : Cmd D Ω)
    (hUpStable :
      ∀ u v : Instance D Ω, f.Up u →
        Cmd.BigStep (.«while» Gu Bo) u v → f.Up v)
    (hDownStable :
      ∀ u v : Instance D Ω, ¬ f.Up u →
        Cmd.BigStep (.«while» Gu Bo) u v → ¬ f.Up v)
    {s t : Instance D Ω}
    (hRun :
      Cmd.BigStep
        (hoistOf hExt f G L₁ L₂ Gu Bo).unfold s t) :
    (f.Up t ↔ G.eval (project hExt s)) := by
  rcases (Framed.bigStep_unfold_iff _ s t).mp hRun with
    ⟨u, v, hInit, hLoop, hClose⟩
  rcases (Cmd.bigStep_ite_iff _ _ _ s u).mp hInit with
    hT | hF
  · rcases flagInit_raise hExt hFresh hT.2 with
      ⟨hUp, _⟩
    have hUpV : f.Up v := hUpStable u v hUp hLoop
    rcases (Cmd.bigStep_ite_iff _ _ _ v t).mp hClose with
      hC | hC
    · have hUpT : f.Up t :=
        (up_congr_retag hExt hFresh hC.2).mpr hUpV
      constructor
      · intro _
        exact (retag_eval_iff hExt G s).mp hT.1
      · intro _
        exact hUpT
    · exact absurd hUpV hC.1
  · rcases flagInit_lower hExt hFresh hF.2 with
      ⟨hDown, _⟩
    have hDownV : ¬ f.Up v := hDownStable u v hDown hLoop
    rcases (Cmd.bigStep_ite_iff _ _ _ v t).mp hClose with
      hC | hC
    · exact absurd hC.1 hDownV
    · have hDownT : ¬ f.Up t := by
        intro hUp
        exact hDownV
          ((up_congr_retag hExt hFresh hC.2).mp hUp)
      constructor
      · intro hUp
        exact absurd hUp hDownT
      · intro hEval
        exact
          absurd ((retag_eval_iff hExt G s).mpr hEval)
            hF.1

end Preprocess

end Whiel

------------------------------------------------------------
-- The General Hoist
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- The general hoisted loop with the flag up. -/
theorem hoistGeneral_project_up
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (L₁ L₂ : Framed D Δ)
    (u v : Instance D Ω)
    (hUp : f.Up u)
    (hStep :
      Cmd.BigStep
        (.«while» (hoistGuard hExt f L₁ L₂)
          (hoistBody hExt f L₁ L₂)) u v) :
    Cmd.BigStep (.«while» L₁.guard L₁.body)
        (project hExt u) (project hExt v) ∧
      f.Up v :=
  flagLoop_project hExt (fun I => f.Up I) _ _ _ _
    (fun I hPh => hoistGuard_eval_up hExt f L₁ L₂ I hPh)
    (fun I J hPh hRun =>
      (hoistBody_iff_up hExt f L₁ L₂ I J hPh).mp hRun)
    (fun I J hPh hRun =>
      hoist_up_pres hExt hFresh L₁.body I J hPh hRun)
    hStep hUp

/- The general hoisted loop with the flag down. -/
theorem hoistGeneral_project_down
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (L₁ L₂ : Framed D Δ)
    (u v : Instance D Ω)
    (hDown : ¬ f.Up u)
    (hStep :
      Cmd.BigStep
        (.«while» (hoistGuard hExt f L₁ L₂)
          (hoistBody hExt f L₁ L₂)) u v) :
    Cmd.BigStep (.«while» L₂.guard L₂.body)
        (project hExt u) (project hExt v) ∧
      ¬ f.Up v :=
  flagLoop_project hExt (fun I => ¬ f.Up I) _ _ _ _
    (fun I hPh =>
      hoistGuard_eval_down hExt f L₁ L₂ I hPh)
    (fun I J hPh hRun =>
      (hoistBody_iff_down hExt f L₁ L₂ I J hPh).mp hRun)
    (fun I J hPh hRun =>
      hoist_down_pres hExt hFresh L₂.body I J hPh hRun)
    hStep hDown

/- The first branch's loop lifts under a raised flag. -/
theorem hoistGeneral_lift_up
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (L₁ L₂ : Framed D Δ)
    (s t : Instance D Δ)
    (hStep :
      Cmd.BigStep (.«while» L₁.guard L₁.body) s t) :
    ∀ u : Instance D Ω, project hExt u = s → f.Up u →
      ∃ v : Instance D Ω,
        Cmd.BigStep
            (.«while» (hoistGuard hExt f L₁ L₂)
              (hoistBody hExt f L₁ L₂)) u v ∧
          project hExt v = t ∧ f.Up v :=
  flagLoop_lift hExt (fun I => f.Up I) _ _ _ _
    (fun I hPh => hoistGuard_eval_up hExt f L₁ L₂ I hPh)
    (fun I J hPh hRun =>
      (hoistBody_iff_up hExt f L₁ L₂ I J hPh).mpr hRun)
    (fun I J hPh hRun =>
      hoist_up_pres hExt hFresh L₁.body I J hPh hRun)
    hStep

/- The second branch's loop lifts under a lowered flag. -/
theorem hoistGeneral_lift_down
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (L₁ L₂ : Framed D Δ)
    (s t : Instance D Δ)
    (hStep :
      Cmd.BigStep (.«while» L₂.guard L₂.body) s t) :
    ∀ u : Instance D Ω, project hExt u = s →
      ¬ f.Up u →
      ∃ v : Instance D Ω,
        Cmd.BigStep
            (.«while» (hoistGuard hExt f L₁ L₂)
              (hoistBody hExt f L₁ L₂)) u v ∧
          project hExt v = t ∧ ¬ f.Up v :=
  flagLoop_lift hExt (fun I => ¬ f.Up I) _ _ _ _
    (fun I hPh =>
      hoistGuard_eval_down hExt f L₁ L₂ I hPh)
    (fun I J hPh hRun =>
      (hoistBody_iff_down hExt f L₁ L₂ I J hPh).mpr
        hRun)
    (fun I J hPh hRun =>
      hoist_down_pres hExt hFresh L₂.body I J hPh hRun)
    hStep

/- Lemma "Hoist", the general case. -/
theorem hoistGeneral_equivMod
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ) :
    EquivMod hExt (.ite G L₁.unfold L₂.unfold)
      (hoistGeneral hExt f G L₁ L₂).unfold :=
  hoistOf_equivMod hExt f hFresh G L₁ L₂ _ _
    (fun u v hUp hStep =>
      hoistGeneral_project_up hExt f hFresh L₁ L₂ u v
        hUp hStep)
    (fun u v hDown hStep =>
      hoistGeneral_project_down hExt f hFresh L₁ L₂ u v
        hDown hStep)
    (fun s t hStep =>
      hoistGeneral_lift_up hExt f hFresh L₁ L₂ s t
        hStep)
    (fun s t hStep =>
      hoistGeneral_lift_down hExt f hFresh L₁ L₂ s t
        hStep)

/- The general hoist flag records the branch taken. -/
theorem hoistGeneral_flag_records_branch
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ)
    {s t : Instance D Ω}
    (hRun :
      Cmd.BigStep
        (hoistGeneral hExt f G L₁ L₂).unfold s t) :
    (f.Up t ↔ G.eval (project hExt s)) :=
  hoistOf_flag_records_branch hExt f hFresh G L₁ L₂ _ _
    (fun u v hUp hStep =>
      (hoistGeneral_project_up hExt f hFresh L₁ L₂ u v
        hUp hStep).2)
    (fun u v hDown hStep =>
      (hoistGeneral_project_down hExt f hFresh L₁ L₂ u v
        hDown hStep).2)
    hRun

end Preprocess

end Whiel

------------------------------------------------------------
-- The One-Branch Hoists
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- The then-loop hoisted loop with the flag up. -/
theorem hoistThenLoop_project_up
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (L₁ : Framed D Δ)
    (u v : Instance D Ω)
    (hUp : f.Up u)
    (hStep :
      Cmd.BigStep
        (.«while»
          (Guard.and f.test (L₁.guard.onExtension hExt))
          (retag hExt L₁.body)) u v) :
    Cmd.BigStep (.«while» L₁.guard L₁.body)
        (project hExt u) (project hExt v) ∧
      f.Up v :=
  flagLoop_project hExt (fun I => f.Up I) _ _ _ _
    (fun I hPh => by
      rw [hoistThenGuard_iff,
        ← retag_eval_iff hExt L₁.guard I]
      constructor
      · rintro ⟨_, hG⟩
        exact hG
      · intro hG
        exact ⟨hPh, hG⟩)
    (fun _ _ _ hRun => hRun)
    (fun I J hPh hRun =>
      hoist_up_pres hExt hFresh L₁.body I J hPh hRun)
    hStep hUp

/-
  The then-loop hoisted loop stops when the flag is
  down.
-/
theorem hoistThenLoop_project_down
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    {L₁ L₂ : Framed D Δ}
    (hBase : L₂.IsBase)
    (u v : Instance D Ω)
    (hDown : ¬ f.Up u)
    (hStep :
      Cmd.BigStep
        (.«while»
          (Guard.and f.test (L₁.guard.onExtension hExt))
          (retag hExt L₁.body)) u v) :
    Cmd.BigStep (.«while» L₂.guard L₂.body)
        (project hExt u) (project hExt v) ∧
      ¬ f.Up v := by
  have hFalse :
      ¬ (Guard.and f.test
          (L₁.guard.onExtension hExt)).eval u := by
    intro hEval
    exact hDown hEval.1
  have hEq : v = u :=
    bigStep_while_eq_of_not_eval hStep hFalse
  subst hEq
  refine ⟨?_, hDown⟩
  rw [hBase.2.1]
  exact
    (Framed.bigStep_while_false_iff L₂.body
      (project hExt v) (project hExt v)).mpr rfl

/- The first branch's loop lifts under a raised flag. -/
theorem hoistThenLoop_lift_up
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (L₁ : Framed D Δ)
    (s t : Instance D Δ)
    (hStep :
      Cmd.BigStep (.«while» L₁.guard L₁.body) s t) :
    ∀ u : Instance D Ω, project hExt u = s → f.Up u →
      ∃ v : Instance D Ω,
        Cmd.BigStep
            (.«while»
              (Guard.and f.test
                (L₁.guard.onExtension hExt))
              (retag hExt L₁.body)) u v ∧
          project hExt v = t ∧ f.Up v :=
  flagLoop_lift hExt (fun I => f.Up I) _ _ _ _
    (fun I hPh => by
      rw [hoistThenGuard_iff,
        ← retag_eval_iff hExt L₁.guard I]
      constructor
      · rintro ⟨_, hG⟩
        exact hG
      · intro hG
        exact ⟨hPh, hG⟩)
    (fun _ _ _ hRun => hRun)
    (fun I J hPh hRun =>
      hoist_up_pres hExt hFresh L₁.body I J hPh hRun)
    hStep

/- The never-entered second branch lifts trivially. -/
theorem hoistThenLoop_lift_down
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    {L₁ L₂ : Framed D Δ}
    (hBase : L₂.IsBase)
    (s t : Instance D Δ)
    (hStep :
      Cmd.BigStep (.«while» L₂.guard L₂.body) s t) :
    ∀ u : Instance D Ω, project hExt u = s →
      ¬ f.Up u →
      ∃ v : Instance D Ω,
        Cmd.BigStep
            (.«while»
              (Guard.and f.test
                (L₁.guard.onExtension hExt))
              (retag hExt L₁.body)) u v ∧
          project hExt v = t ∧ ¬ f.Up v := by
  intro u hProj hDown
  rw [hBase.2.1] at hStep
  have hEq : t = s :=
    (Framed.bigStep_while_false_iff L₂.body s t).mp hStep
  subst hEq
  refine ⟨u, Cmd.BigStep.while_false ?_, hProj, hDown⟩
  intro hEval
  exact hDown hEval.1

/- Lemma "Hoist", the loop-free else-branch case. -/
theorem hoistThenLoop_equivMod
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    {L₁ L₂ : Framed D Δ}
    (hBase : L₂.IsBase) :
    EquivMod hExt (.ite G L₁.unfold L₂.unfold)
      (hoistThenLoop hExt f G L₁ L₂).unfold :=
  hoistOf_equivMod hExt f hFresh G L₁ L₂ _ _
    (fun u v hUp hStep =>
      hoistThenLoop_project_up hExt f hFresh L₁ u v hUp
        hStep)
    (fun u v hDown hStep =>
      hoistThenLoop_project_down hExt f hBase u v hDown
        hStep)
    (fun s t hStep =>
      hoistThenLoop_lift_up hExt f hFresh L₁ s t hStep)
    (fun s t hStep =>
      hoistThenLoop_lift_down hExt f hBase s t hStep)

/- The then-loop hoist flag records the branch taken. -/
theorem hoistThenLoop_flag_records_branch
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    {L₁ L₂ : Framed D Δ}
    (hBase : L₂.IsBase)
    {s t : Instance D Ω}
    (hRun :
      Cmd.BigStep
        (hoistThenLoop hExt f G L₁ L₂).unfold s t) :
    (f.Up t ↔ G.eval (project hExt s)) :=
  hoistOf_flag_records_branch hExt f hFresh G L₁ L₂ _ _
    (fun u v hUp hStep =>
      (hoistThenLoop_project_up hExt f hFresh L₁ u v hUp
        hStep).2)
    (fun u v hDown hStep =>
      (hoistThenLoop_project_down hExt f hBase u v hDown
        hStep).2)
    hRun

/- The else-loop hoisted loop with the flag down. -/
theorem hoistElseLoop_project_down
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (L₂ : Framed D Δ)
    (u v : Instance D Ω)
    (hDown : ¬ f.Up u)
    (hStep :
      Cmd.BigStep
        (.«while»
          (Guard.and (.not f.test)
            (L₂.guard.onExtension hExt))
          (retag hExt L₂.body)) u v) :
    Cmd.BigStep (.«while» L₂.guard L₂.body)
        (project hExt u) (project hExt v) ∧
      ¬ f.Up v :=
  flagLoop_project hExt (fun I => ¬ f.Up I) _ _ _ _
    (fun I hPh => by
      rw [hoistElseGuard_iff,
        ← retag_eval_iff hExt L₂.guard I]
      constructor
      · rintro ⟨_, hG⟩
        exact hG
      · intro hG
        exact ⟨hPh, hG⟩)
    (fun _ _ _ hRun => hRun)
    (fun I J hPh hRun =>
      hoist_down_pres hExt hFresh L₂.body I J hPh hRun)
    hStep hDown

/- The else-loop hoisted loop stops when the flag is up. -/
theorem hoistElseLoop_project_up
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    {L₁ L₂ : Framed D Δ}
    (hBase : L₁.IsBase)
    (u v : Instance D Ω)
    (hUp : f.Up u)
    (hStep :
      Cmd.BigStep
        (.«while»
          (Guard.and (.not f.test)
            (L₂.guard.onExtension hExt))
          (retag hExt L₂.body)) u v) :
    Cmd.BigStep (.«while» L₁.guard L₁.body)
        (project hExt u) (project hExt v) ∧
      f.Up v := by
  have hFalse :
      ¬ (Guard.and (.not f.test)
          (L₂.guard.onExtension hExt)).eval u := by
    intro hEval
    exact hEval.1 hUp
  have hEq : v = u :=
    bigStep_while_eq_of_not_eval hStep hFalse
  subst hEq
  refine ⟨?_, hUp⟩
  rw [hBase.2.1]
  exact
    (Framed.bigStep_while_false_iff L₁.body
      (project hExt v) (project hExt v)).mpr rfl

/- The second branch's loop lifts under a lowered flag. -/
theorem hoistElseLoop_lift_down
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (L₂ : Framed D Δ)
    (s t : Instance D Δ)
    (hStep :
      Cmd.BigStep (.«while» L₂.guard L₂.body) s t) :
    ∀ u : Instance D Ω, project hExt u = s →
      ¬ f.Up u →
      ∃ v : Instance D Ω,
        Cmd.BigStep
            (.«while»
              (Guard.and (.not f.test)
                (L₂.guard.onExtension hExt))
              (retag hExt L₂.body)) u v ∧
          project hExt v = t ∧ ¬ f.Up v :=
  flagLoop_lift hExt (fun I => ¬ f.Up I) _ _ _ _
    (fun I hPh => by
      rw [hoistElseGuard_iff,
        ← retag_eval_iff hExt L₂.guard I]
      constructor
      · rintro ⟨_, hG⟩
        exact hG
      · intro hG
        exact ⟨hPh, hG⟩)
    (fun _ _ _ hRun => hRun)
    (fun I J hPh hRun =>
      hoist_down_pres hExt hFresh L₂.body I J hPh hRun)
    hStep

/- The never-entered first branch lifts trivially. -/
theorem hoistElseLoop_lift_up
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    {L₁ L₂ : Framed D Δ}
    (hBase : L₁.IsBase)
    (s t : Instance D Δ)
    (hStep :
      Cmd.BigStep (.«while» L₁.guard L₁.body) s t) :
    ∀ u : Instance D Ω, project hExt u = s → f.Up u →
      ∃ v : Instance D Ω,
        Cmd.BigStep
            (.«while»
              (Guard.and (.not f.test)
                (L₂.guard.onExtension hExt))
              (retag hExt L₂.body)) u v ∧
          project hExt v = t ∧ f.Up v := by
  intro u hProj hUp
  rw [hBase.2.1] at hStep
  have hEq : t = s :=
    (Framed.bigStep_while_false_iff L₁.body s t).mp hStep
  subst hEq
  refine ⟨u, Cmd.BigStep.while_false ?_, hProj, hUp⟩
  intro hEval
  exact hEval.1 hUp

/- Lemma "Hoist", the loop-free then-branch case. -/
theorem hoistElseLoop_equivMod
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    {L₁ L₂ : Framed D Δ}
    (hBase : L₁.IsBase) :
    EquivMod hExt (.ite G L₁.unfold L₂.unfold)
      (hoistElseLoop hExt f G L₁ L₂).unfold :=
  hoistOf_equivMod hExt f hFresh G L₁ L₂ _ _
    (fun u v hUp hStep =>
      hoistElseLoop_project_up hExt f hBase u v hUp
        hStep)
    (fun u v hDown hStep =>
      hoistElseLoop_project_down hExt f hFresh L₂ u v
        hDown hStep)
    (fun s t hStep =>
      hoistElseLoop_lift_up hExt f hBase s t hStep)
    (fun s t hStep =>
      hoistElseLoop_lift_down hExt f hFresh L₂ s t hStep)

/- The else-loop hoist flag records the branch taken. -/
theorem hoistElseLoop_flag_records_branch
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    {L₁ L₂ : Framed D Δ}
    (hBase : L₁.IsBase)
    {s t : Instance D Ω}
    (hRun :
      Cmd.BigStep
        (hoistElseLoop hExt f G L₁ L₂).unfold s t) :
    (f.Up t ↔ G.eval (project hExt s)) :=
  hoistOf_flag_records_branch hExt f hFresh G L₁ L₂ _ _
    (fun u v hUp hStep =>
      (hoistElseLoop_project_up hExt f hBase u v hUp
        hStep).2)
    (fun u v hDown hStep =>
      (hoistElseLoop_project_down hExt f hFresh L₂ u v
        hDown hStep).2)
    hRun

end Preprocess

end Whiel

------------------------------------------------------------
-- The Flag-Free Hoist
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  With both branches loop-free the conditional is its own
  base framed loop, over the source schema and with no
  flag.
-/
theorem hoistFlagFree_bigStepEquiv
    (G : Guard D Δ)
    {L₁ L₂ : Framed D Δ}
    (hOne : L₁.IsBase)
    (hTwo : L₂.IsBase) :
    Cmd.BigStepEquiv (.ite G L₁.unfold L₂.unfold)
      (hoistFlagFree G L₁ L₂).unfold := by
  intro I J
  simp only [hoistFlagFree, Framed.bigStep_base_iff,
    Cmd.bigStep_ite_iff,
    bigStep_unfold_iff_of_isBase hOne,
    bigStep_unfold_iff_of_isBase hTwo]

/- Lemma "Hoist", the flag-free case. -/
theorem hoistFlagFree_equivMod
    (hExt : Ω.extensionOf Δ)
    (G : Guard D Δ)
    {L₁ L₂ : Framed D Δ}
    (hOne : L₁.IsBase)
    (hTwo : L₂.IsBase) :
    EquivMod hExt (.ite G L₁.unfold L₂.unfold)
      ((hoistFlagFree G L₁ L₂).retagOn hExt).unfold :=
  equivMod_retag_of_bigStepEquiv hExt
    (hoistFlagFree_bigStepEquiv G hOne hTwo)

end Preprocess

end Whiel

------------------------------------------------------------
-- The Dispatcher
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  The conditional hoist is correct in every case, with the
  case selected by the source-level Booleans.
-/
theorem hoistIte_equivMod
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ)
    (loopFreeThen loopFreeElse : Bool)
    (hThen : loopFreeThen = true → L₁.IsBase)
    (hElse : loopFreeElse = true → L₂.IsBase) :
    EquivMod hExt (.ite G L₁.unfold L₂.unfold)
      (hoistIte hExt f G L₁ L₂ loopFreeThen
        loopFreeElse).unfold := by
  unfold hoistIte
  cases loopFreeThen with
  | true =>
      cases loopFreeElse with
      | true =>
          exact
            hoistFlagFree_equivMod hExt G (hThen rfl)
              (hElse rfl)
      | false =>
          exact
            hoistElseLoop_equivMod hExt f hFresh G
              (hThen rfl)
  | false =>
      cases loopFreeElse with
      | true =>
          exact
            hoistThenLoop_equivMod hExt f hFresh G
              (hElse rfl)
      | false =>
          exact
            hoistGeneral_equivMod hExt f hFresh G L₁ L₂

/-
  In every flagged case the hoist flag records the branch
  taken at every terminal state. The note claims no more:
  a hoist flag is set once and never lowered, so it may be
  up at exit.
-/
theorem hoistIte_flag_records_branch
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (hFresh : f.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ)
    (loopFreeThen loopFreeElse : Bool)
    (hFlagged : (loopFreeThen && loopFreeElse) = false)
    (hThen : loopFreeThen = true → L₁.IsBase)
    (hElse : loopFreeElse = true → L₂.IsBase)
    {s t : Instance D Ω}
    (hRun :
      Cmd.BigStep
        (hoistIte hExt f G L₁ L₂ loopFreeThen
          loopFreeElse).unfold s t) :
    (f.Up t ↔ G.eval (project hExt s)) := by
  revert hRun
  unfold hoistIte
  cases loopFreeThen with
  | true =>
      cases loopFreeElse with
      | true => cases hFlagged
      | false =>
          intro hRun
          exact
            hoistElseLoop_flag_records_branch hExt f
              hFresh G (hThen rfl) hRun
  | false =>
      cases loopFreeElse with
      | true =>
          intro hRun
          exact
            hoistThenLoop_flag_records_branch hExt f
              hFresh G (hElse rfl) hRun
      | false =>
          intro hRun
          exact
            hoistGeneral_flag_records_branch hExt f
              hFresh G L₁ L₂ hRun

end Preprocess

end Whiel

------------------------------------------------------------
-- Loop-Freeness Of The Hoisted Components
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- Retagging preserves loop-freeness. -/
theorem loopFree_of_retag
    (hExt : Ω.extensionOf Δ)
    {C : Cmd D Δ}
    (hC : LoopFree C) :
    LoopFree (retag hExt C) := by
  have hZero : loops C = 0 := hC
  simp [LoopFree, hZero]

/- The hoist prefix is loop-free. -/
theorem hoistInit_loopFree
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    {L₁ L₂ : Framed D Δ}
    (hOne : LoopFree L₁.init)
    (hTwo : LoopFree L₂.init) :
    LoopFree (hoistInit hExt f G L₁ L₂) := by
  have h₁ : loops L₁.init = 0 := hOne
  have h₂ : loops L₂.init = 0 := hTwo
  simp [hoistInit, LoopFree, loops, FlagSym.raise,
    FlagSym.lower, h₁, h₂]

/- The hoist suffix is loop-free. -/
theorem hoistClose_loopFree
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    {L₁ L₂ : Framed D Δ}
    (hOne : LoopFree L₁.close)
    (hTwo : LoopFree L₂.close) :
    LoopFree (hoistClose hExt f L₁ L₂) := by
  have h₁ : loops L₁.close = 0 := hOne
  have h₂ : loops L₂.close = 0 := hTwo
  simp [hoistClose, LoopFree, loops, h₁, h₂]

/- The general hoist keeps the components loop-free. -/
theorem hoistGeneral_loopFreeParts
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    {L₁ L₂ : Framed D Δ}
    (hOne : L₁.LoopFreeParts)
    (hTwo : L₂.LoopFreeParts) :
    (hoistGeneral hExt f G L₁ L₂).LoopFreeParts := by
  have h₁ : loops L₁.body = 0 := hOne.2.1
  have h₂ : loops L₂.body = 0 := hTwo.2.1
  refine
    ⟨hoistInit_loopFree hExt f G hOne.1 hTwo.1, ?_,
      hoistClose_loopFree hExt f hOne.2.2 hTwo.2.2⟩
  simp [hoistGeneral, hoistOf, hoistBody, LoopFree,
    loops, h₁, h₂]

/- The then-loop hoist keeps the components loop-free. -/
theorem hoistThenLoop_loopFreeParts
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    {L₁ L₂ : Framed D Δ}
    (hOne : L₁.LoopFreeParts)
    (hTwo : L₂.LoopFreeParts) :
    (hoistThenLoop hExt f G L₁ L₂).LoopFreeParts := by
  refine
    ⟨hoistInit_loopFree hExt f G hOne.1 hTwo.1, ?_,
      hoistClose_loopFree hExt f hOne.2.2 hTwo.2.2⟩
  exact loopFree_of_retag hExt hOne.2.1

/- The else-loop hoist keeps the components loop-free. -/
theorem hoistElseLoop_loopFreeParts
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    {L₁ L₂ : Framed D Δ}
    (hOne : L₁.LoopFreeParts)
    (hTwo : L₂.LoopFreeParts) :
    (hoistElseLoop hExt f G L₁ L₂).LoopFreeParts := by
  refine
    ⟨hoistInit_loopFree hExt f G hOne.1 hTwo.1, ?_,
      hoistClose_loopFree hExt f hOne.2.2 hTwo.2.2⟩
  exact loopFree_of_retag hExt hTwo.2.1

/- The flag-free hoist keeps the components loop-free. -/
theorem hoistFlagFree_loopFreeParts
    (G : Guard D Δ)
    {L₁ L₂ : Framed D Δ}
    (hOne : L₁.LoopFreeParts)
    (hTwo : L₂.LoopFreeParts) :
    (hoistFlagFree G L₁ L₂).LoopFreeParts := by
  have h₁ : loops L₁.close = 0 := hOne.2.2
  have h₂ : loops L₂.close = 0 := hTwo.2.2
  refine ⟨rfl, rfl, ?_⟩
  simp [hoistFlagFree, Framed.base, LoopFree, loops,
    h₁, h₂]

/- Every case of the hoist preserves loop-freeness. -/
theorem hoistIte_loopFreeParts
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ)
    (loopFreeThen loopFreeElse : Bool)
    (hOne : L₁.LoopFreeParts)
    (hTwo : L₂.LoopFreeParts) :
    (hoistIte hExt f G L₁ L₂ loopFreeThen
      loopFreeElse).LoopFreeParts := by
  unfold hoistIte
  cases loopFreeThen with
  | true =>
      cases loopFreeElse with
      | true =>
          have hParts :=
            hoistFlagFree_loopFreeParts G hOne hTwo
          exact
            ⟨loopFree_of_retag hExt hParts.1,
              loopFree_of_retag hExt hParts.2.1,
              loopFree_of_retag hExt hParts.2.2⟩
      | false =>
          exact
            hoistElseLoop_loopFreeParts hExt f G hOne
              hTwo
  | false =>
      cases loopFreeElse with
      | true =>
          exact
            hoistThenLoop_loopFreeParts hExt f G hOne
              hTwo
      | false =>
          exact
            hoistGeneral_loopFreeParts hExt f G hOne hTwo

end Preprocess

end Whiel
