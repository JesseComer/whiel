-- Author: Jesse Comer
import Whiel.Preprocess.Hoist

/-
  Loop flattening for the generic preprocessor.

  A loop whose body is itself a framed loop becomes one
  framed loop over one fresh inner flag `i`. The flag means
  "the inner loop is running": while `i` is down the body
  opens a new outer iteration, running the inner loop's
  prefix and raising `i`; while `i` is up the body is one
  inner iteration, or the inner loop's exit, which runs the
  inner loop's suffix and lowers `i`. The prefix
  `i := ∅` is not bookkeeping: from a start whose flags are
  arbitrary the merged guard `i ∨ G` is read before any body
  has run, and with `i` up it would be true regardless of
  `G`, so the construction would resume an inner loop that
  never began.

  Key definitions include:
    * `Whiel.Preprocess.flattenGeneral`
    * `Whiel.Preprocess.flattenLoopFree`
    * `Whiel.Preprocess.flattenIdem`
    * `Whiel.Preprocess.flattenWhile`

  Correctness is proven by:
    * `Whiel.Preprocess.flattenWhile_equivMod`
    * `Whiel.Preprocess.flattenGeneral_flag_down`
    * `Whiel.Preprocess.while_idem_bigStepEquiv`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- The Flatten Operations
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- The merged guard: the inner flag or the source guard. -/
def flattenGuard
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ) :
    Guard D Ω :=
  .or i.test (G.onExtension hExt)

/-
  The merged body. With `i` up it is one inner iteration,
  or the inner loop's exit; with `i` down it opens a new
  outer iteration.
-/
def flattenBody
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (L₀ : Framed D Δ) :
    Cmd D Ω :=
  .ite i.test
    (.ite (L₀.guard.onExtension hExt)
      (retag hExt L₀.body)
      (.seq i.lower (retag hExt L₀.close)))
    (.seq (retag hExt L₀.init) i.raise)

/-
  Loop flattening when the source body carries a
  loop: one fresh flag, the prefix `i := ∅`, and an empty
  suffix.
-/
def flattenGeneral
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ)
    (L₀ : Framed D Δ) :
    Framed D Ω where
  init := i.lower
  guard := flattenGuard hExt i G
  body := flattenBody hExt i L₀
  close := .skip

/-
  The flag-free case of a loop-free source body: a loop
  whose body is loop-free is already a framed loop.
-/
def flattenLoopFree
    (G : Guard D Δ)
    (C₀ : Cmd D Δ) :
    Framed D Δ where
  init := .skip
  guard := G
  body := C₀
  close := .skip

/-
  The flag-free case of idempotent nesting: the outer loop
  is discarded and the inner loop's own framed loop is the
  answer.
-/
def flattenIdem (L₀ : Framed D Δ) : Framed D Δ :=
  L₀

/-
  The loop flattening. The two Booleans are
  computed from the source body by the caller and are never
  read off the framed loop; the priority is the note's:
  idempotent nesting first, then a loop-free body, then the
  general case.
-/
def flattenWhile
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ)
    (L₀ : Framed D Δ)
    (idem loopFreeBody : Bool) :
    Framed D Ω :=
  if idem then
    (flattenIdem L₀).retagOn hExt
  else if loopFreeBody then
    (flattenLoopFree G L₀.close).retagOn hExt
  else
    flattenGeneral hExt i G L₀

/- The idempotent case does not mention the drawn flag. -/
theorem flattenWhile_eq_idem
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ)
    (L₀ : Framed D Δ)
    (b : Bool) :
    flattenWhile hExt i G L₀ true b =
      (flattenIdem L₀).retagOn hExt :=
  rfl

theorem flattenWhile_eq_loopFree
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ)
    (L₀ : Framed D Δ) :
    flattenWhile hExt i G L₀ false true =
      (flattenLoopFree G L₀.close).retagOn hExt :=
  rfl

theorem flattenWhile_eq_general
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ)
    (L₀ : Framed D Δ) :
    flattenWhile hExt i G L₀ false false =
      flattenGeneral hExt i G L₀ :=
  rfl

end Preprocess

end Whiel

------------------------------------------------------------
-- The Merged Guard And The Flatten Prefix
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- The merged guard, spelled out. -/
theorem flattenGuard_iff
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ)
    (I : Instance D Ω) :
    (flattenGuard hExt i G).eval I ↔
      (i.Up I ∨ (G.onExtension hExt).eval I) :=
  Iff.rfl

/- With the flag up the merged guard is true. -/
theorem flattenGuard_of_up
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ)
    {I : Instance D Ω}
    (hUp : i.Up I) :
    (flattenGuard hExt i G).eval I :=
  Or.inl hUp

/-
  The outer guard decides the merged guard exactly while
  the inner flag is down.
-/
theorem flattenGuard_eval_down
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ)
    {I : Instance D Ω}
    (hDown : ¬ i.Up I) :
    ((flattenGuard hExt i G).eval I ↔
      G.eval (project hExt I)) := by
  rw [flattenGuard_iff, ← retag_eval_iff hExt G I]
  constructor
  · rintro (hUp | hG)
    · exact absurd hUp hDown
    · exact hG
  · intro hG
    exact Or.inr hG

/-
  The flattening's share of the flag-initialization
  principle: the prefix `i := ∅` lowers the flag whatever
  the initial state carried, and moves no source relation.
-/
theorem flattenInit_lowers
    (hExt : Ω.extensionOf Δ)
    {i : FlagSym Ω}
    (hFresh : i.sym.1 ∉ Δ.syms)
    {s u : Instance D Ω}
    (hStep : Cmd.BigStep i.lower s u) :
    ¬ i.Up u ∧ project hExt u = project hExt s :=
  ⟨FlagSym.not_up_of_bigStep_lower hStep,
    project_of_bigStep_lower hExt hFresh hStep⟩

end Preprocess

end Whiel

------------------------------------------------------------
-- Idempotent Nesting
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- A terminated loop leaves its guard false. -/
theorem not_eval_of_bigStep_while
    {G : Guard D Γ}
    {B : Cmd D Γ}
    {I J : Instance D Γ}
    (hStep : Cmd.BigStep (.«while» G B) I J) :
    ¬ G.eval J := by
  generalize hW :
      (Cmd.«while» G B : Cmd D Γ) = W at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false G' B' I hFalse =>
      cases hW
      exact hFalse
  | @while_true G' B' I K J hEval hRun hLoop ihRun
      ihLoop =>
      cases hW
      exact ihLoop rfl

/-
  Lemma "Idempotent nesting": with the inner guard term
  syntactically equal to the outer one, the outer loop is
  redundant. This is a plain big-step equivalence, over the
  same schema and with no flag.
-/
theorem while_idem_bigStepEquiv
    (G : Guard D Γ)
    (E : Cmd D Γ) :
    Cmd.BigStepEquiv
      (.«while» G (.«while» G E))
      (.«while» G E) := by
  intro I J
  constructor
  · intro hStep
    generalize hW :
        (Cmd.«while» G (Cmd.«while» G E) : Cmd D Γ) =
          W at hStep
    induction hStep with
    | skip I => cases hW
    | assign I X e => cases hW
    | seq h₁ h₂ ih₁ ih₂ => cases hW
    | ite_true hEval hRun ih => cases hW
    | ite_false hEval hRun ih => cases hW
    | @while_false G' B' I hFalse =>
        cases hW
        exact Cmd.BigStep.while_false hFalse
    | @while_true G' B' I K J hEval hRun hLoop ihRun
        ihLoop =>
        cases hW
        have hInner := ihLoop rfl
        have hFalseK : ¬ G.eval K :=
          not_eval_of_bigStep_while hRun
        have hEq : J = K := by
          cases hInner with
          | while_false hF => rfl
          | while_true hG hB hL => exact absurd hG hFalseK
        rw [hEq]
        exact hRun
  · intro hStep
    by_cases hG : G.eval I
    · refine Cmd.BigStep.while_true hG hStep ?_
      exact Cmd.BigStep.while_false
        (not_eval_of_bigStep_while hStep)
    · have hEq : J = I := by
        cases hStep with
        | while_false hF => rfl
        | while_true hEval hB hL => exact absurd hEval hG
      rw [hEq]
      exact Cmd.BigStep.while_false hG

/- Loops are congruent for big-step equivalence. -/
theorem bigStepEquiv_while
    (G : Guard D Γ)
    {B₁ B₂ : Cmd D Γ}
    (hBody : Cmd.BigStepEquiv B₁ B₂) :
    Cmd.BigStepEquiv (.«while» G B₁)
      (.«while» G B₂) := by
  have hOne :
      ∀ (C₁ C₂ : Cmd D Γ),
        (∀ I J : Instance D Γ,
          Cmd.BigStep C₁ I J → Cmd.BigStep C₂ I J) →
          ∀ I J : Instance D Γ,
            Cmd.BigStep (.«while» G C₁) I J →
              Cmd.BigStep (.«while» G C₂) I J := by
    intro C₁ C₂ hImp I J hStep
    generalize hW :
        (Cmd.«while» G C₁ : Cmd D Γ) = W at hStep
    induction hStep with
    | skip I => cases hW
    | assign I X e => cases hW
    | seq h₁ h₂ ih₁ ih₂ => cases hW
    | ite_true hEval hRun ih => cases hW
    | ite_false hEval hRun ih => cases hW
    | @while_false G' B' I hFalse =>
        cases hW
        exact Cmd.BigStep.while_false hFalse
    | @while_true G' B' I K J hEval hRun hLoop ihRun
        ihLoop =>
        cases hW
        exact Cmd.BigStep.while_true hEval
          (hImp _ _ hRun) (ihLoop rfl)
  intro I J
  constructor
  · exact
      hOne B₁ B₂ (fun I J h => (hBody I J).mp h) I J
  · exact
      hOne B₂ B₁ (fun I J h => (hBody I J).mpr h) I J

end Preprocess

end Whiel

------------------------------------------------------------
-- The Flatten Lemma, Forward
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  The note's Claims A and B, forwards, in one induction on
  the merged loop: with the flag up the run is the rest of
  one inner loop, the inner suffix and the outer loop; with
  the flag down it is the outer loop. Either way the flag
  is down at the end.
-/
theorem flattenGeneral_project
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (hFresh : i.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (L₀ : Framed D Δ)
    {u v : Instance D Ω}
    (hStep :
      Cmd.BigStep
        (.«while» (flattenGuard hExt i G)
          (flattenBody hExt i L₀)) u v) :
    (i.Up u →
        Cmd.BigStep
            (.seq (.«while» L₀.guard L₀.body)
              (.seq L₀.close
                (.«while» G L₀.unfold)))
            (project hExt u) (project hExt v) ∧
          ¬ i.Up v) ∧
      (¬ i.Up u →
        Cmd.BigStep (.«while» G L₀.unfold)
            (project hExt u) (project hExt v) ∧
          ¬ i.Up v) := by
  generalize hW :
      (Cmd.«while» (flattenGuard hExt i G)
        (flattenBody hExt i L₀) : Cmd D Ω) = W at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false Gu Bo u hFalse =>
      cases hW
      constructor
      · intro hUp
        exact absurd (flattenGuard_of_up hExt i G hUp)
          hFalse
      · intro hDown
        refine ⟨Cmd.BigStep.while_false ?_, hDown⟩
        intro hG
        exact hFalse
          ((flattenGuard_eval_down hExt i G hDown).mpr hG)
  | @while_true Gu Bo u m v hEval hRun hLoop ihRun
      ihLoop =>
      cases hW
      constructor
      · intro hUp
        rcases
          (Cmd.bigStep_ite_iff _ _ _ u m).mp hRun with
          hT | hF
        · rcases
            (Cmd.bigStep_ite_iff _ _ _ u m).mp hT.2 with
            hH | hNotH
          · have hUpM : i.Up m :=
              hoist_up_pres hExt hFresh L₀.body u m hUp
                hH.2
            rcases (ihLoop rfl).1 hUpM with
              ⟨hTail, hDownV⟩
            refine ⟨?_, hDownV⟩
            rcases
              (Cmd.bigStep_seq_iff _ _ _ _).mp hTail with
              ⟨y, hInner, hRest⟩
            refine Cmd.BigStep.seq ?_ hRest
            refine Cmd.BigStep.while_true ?_ ?_ hInner
            · exact (retag_eval_iff hExt L₀.guard u).mp
                hH.1
            · exact retag_bigStep_project hExt hH.2
          · rcases
              (Cmd.bigStep_seq_iff _ _ u m).mp
                hNotH.2 with ⟨m₁, hLower, hClose⟩
            have hDownOne : ¬ i.Up m₁ :=
              FlagSym.not_up_of_bigStep_lower hLower
            have hProjOne :
                project hExt m₁ = project hExt u :=
              project_of_bigStep_lower hExt hFresh hLower
            have hDownM : ¬ i.Up m :=
              hoist_down_pres hExt hFresh L₀.close m₁ m
                hDownOne hClose
            rcases (ihLoop rfl).2 hDownM with
              ⟨hOuter, hDownV⟩
            refine ⟨?_, hDownV⟩
            refine
              Cmd.BigStep.seq
                (I₁ := project hExt u) ?_ ?_
            · refine Cmd.BigStep.while_false ?_
              intro hEvalH
              exact hNotH.1
                ((retag_eval_iff hExt L₀.guard u).mpr
                  hEvalH)
            · refine Cmd.BigStep.seq ?_ hOuter
              have hRun :=
                retag_bigStep_project hExt hClose
              rw [hProjOne] at hRun
              exact hRun
        · exact absurd hUp hF.1
      · intro hDown
        rcases
          (Cmd.bigStep_ite_iff _ _ _ u m).mp hRun with
          hT | hF
        · exact absurd hT.1 hDown
        · rcases flagInit_raise hExt hFresh hF.2 with
            ⟨hUpM, hInit⟩
          rcases (ihLoop rfl).1 hUpM with
            ⟨hTail, hDownV⟩
          refine ⟨?_, hDownV⟩
          have hG : G.eval (project hExt u) :=
            (flattenGuard_eval_down hExt i G hDown).mp hEval
          rcases
            (Cmd.bigStep_seq_iff _ _ _ _).mp hTail with
            ⟨y, hInner, hRest⟩
          rcases
            (Cmd.bigStep_seq_iff _ _ _ _).mp hRest with
            ⟨z, hClose, hOuter⟩
          refine Cmd.BigStep.while_true hG ?_ hOuter
          exact
            (Framed.bigStep_unfold_iff L₀
              (project hExt u) z).mpr
              ⟨project hExt m, y, hInit, hInner, hClose⟩

end Preprocess

end Whiel

------------------------------------------------------------
-- The Flatten Lemma, Backward
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  The note's Claim A backwards. The continuation hypothesis
  takes the place of the mutual induction: after the inner
  loop and the inner suffix the merged loop is resumed with
  the flag down, which is Claim B at the next outer state.
-/
theorem flattenGeneral_lift_inner
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (hFresh : i.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (L₀ : Framed D Δ)
    {x t : Instance D Δ}
    (hCont :
      ∀ w : Instance D Ω, project hExt w = x →
        ¬ i.Up w →
        ∃ v : Instance D Ω,
          Cmd.BigStep
              (.«while» (flattenGuard hExt i G)
                (flattenBody hExt i L₀)) w v ∧
            project hExt v = t ∧ ¬ i.Up v)
    {a b : Instance D Δ}
    (hInner :
      Cmd.BigStep (.«while» L₀.guard L₀.body) a b) :
    Cmd.BigStep L₀.close b x →
      ∀ u : Instance D Ω, project hExt u = a →
        i.Up u →
        ∃ v : Instance D Ω,
          Cmd.BigStep
              (.«while» (flattenGuard hExt i G)
                (flattenBody hExt i L₀)) u v ∧
            project hExt v = t ∧ ¬ i.Up v := by
  generalize hW :
      (Cmd.«while» L₀.guard L₀.body : Cmd D Δ) =
        W at hInner
  induction hInner with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false H' B' a hFalse =>
      cases hW
      intro hClose u hProj hUp
      set u₁ :=
        Instance.update u i.sym (i.emptyExpr.eval u)
        with hu₁
      have hLower : Cmd.BigStep i.lower u u₁ :=
        Cmd.BigStep.assign u i.sym i.emptyExpr
      have hDownOne : ¬ i.Up u₁ :=
        FlagSym.not_up_of_bigStep_lower hLower
      have hProjOne : project hExt u₁ = a := by
        rw [project_of_bigStep_lower hExt hFresh hLower,
          hProj]
      rcases
        retag_bigStep_lift hExt hProjOne hClose with
        ⟨w, hCloseRun, hProjW⟩
      have hDownW : ¬ i.Up w :=
        hoist_down_pres hExt hFresh L₀.close u₁ w
          hDownOne hCloseRun
      rcases hCont w hProjW hDownW with
        ⟨v, hV, hProjV, hDownV⟩
      refine ⟨v, ?_, hProjV, hDownV⟩
      refine
        Cmd.BigStep.while_true
          (flattenGuard_of_up hExt i G hUp) ?_ hV
      refine Cmd.BigStep.ite_true hUp ?_
      refine Cmd.BigStep.ite_false ?_ ?_
      · intro hEvalH
        refine hFalse ?_
        rw [← hProj]
        exact (retag_eval_iff hExt L₀.guard u).mp hEvalH
      · exact Cmd.BigStep.seq hLower hCloseRun
  | @while_true H' B' a a₁ b hEval hRun hLoop ihRun
      ihLoop =>
      cases hW
      intro hClose u hProj hUp
      rcases retag_bigStep_lift hExt hProj hRun with
        ⟨m, hRunΩ, hProjM⟩
      have hUpM : i.Up m :=
        hoist_up_pres hExt hFresh L₀.body u m hUp hRunΩ
      rcases ihLoop rfl hClose m hProjM hUpM with
        ⟨v, hV, hProjV, hDownV⟩
      refine ⟨v, ?_, hProjV, hDownV⟩
      refine
        Cmd.BigStep.while_true
          (flattenGuard_of_up hExt i G hUp) ?_ hV
      refine Cmd.BigStep.ite_true hUp ?_
      refine Cmd.BigStep.ite_true ?_ hRunΩ
      refine (retag_eval_iff hExt L₀.guard u).mpr ?_
      rw [hProj]
      exact hEval

/-
  The note's Claim B backwards: a run of the source loop
  lifts to a run of the merged loop from any state with the
  inner flag down.
-/
theorem flattenGeneral_lift_outer
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (hFresh : i.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (L₀ : Framed D Δ)
    {s t : Instance D Δ}
    (hStep : Cmd.BigStep (.«while» G L₀.unfold) s t) :
    ∀ u : Instance D Ω, project hExt u = s →
      ¬ i.Up u →
      ∃ v : Instance D Ω,
        Cmd.BigStep
            (.«while» (flattenGuard hExt i G)
              (flattenBody hExt i L₀)) u v ∧
          project hExt v = t ∧ ¬ i.Up v := by
  generalize hW :
      (Cmd.«while» G L₀.unfold : Cmd D Δ) = W at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false G' B' s hFalse =>
      cases hW
      intro u hProj hDown
      refine ⟨u, Cmd.BigStep.while_false ?_, hProj,
        hDown⟩
      intro hEval
      refine hFalse ?_
      rw [← hProj]
      exact (flattenGuard_eval_down hExt i G hDown).mp hEval
  | @while_true G' B' s y t hEval hRun hLoop ihRun
      ihLoop =>
      cases hW
      intro u hProj hDown
      rcases
        (Framed.bigStep_unfold_iff L₀ s y).mp hRun with
        ⟨a, b, hInit, hLoopIn, hClose⟩
      rcases retag_bigStep_lift hExt hProj hInit with
        ⟨m₀, hInitΩ, hProjZero⟩
      set m₁ :=
        Instance.update m₀ i.sym (i.topExpr.eval m₀)
        with hm₁
      have hRaise : Cmd.BigStep i.raise m₀ m₁ :=
        Cmd.BigStep.assign m₀ i.sym i.topExpr
      have hUpOne : i.Up m₁ :=
        FlagSym.up_of_bigStep_raise hRaise
      have hProjOne : project hExt m₁ = a := by
        rw [project_of_bigStep_raise hExt hFresh hRaise,
          hProjZero]
      rcases
        flattenGeneral_lift_inner hExt i hFresh G L₀
          (fun w hw hdown => ihLoop rfl w hw hdown)
          hLoopIn hClose m₁ hProjOne hUpOne with
        ⟨v, hV, hProjV, hDownV⟩
      refine ⟨v, ?_, hProjV, hDownV⟩
      refine Cmd.BigStep.while_true ?_ ?_ hV
      · refine
          (flattenGuard_eval_down hExt i G hDown).mpr ?_
        rw [hProj]
        exact hEval
      · refine Cmd.BigStep.ite_false hDown ?_
        exact Cmd.BigStep.seq hInitΩ hRaise

end Preprocess

end Whiel

------------------------------------------------------------
-- The Flatten Lemma
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- Lemma "Flatten", the general case. -/
theorem flattenGeneral_equivMod
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (hFresh : i.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (L₀ : Framed D Δ) :
    EquivMod hExt (.«while» G L₀.unfold)
      (flattenGeneral hExt i G L₀).unfold := by
  constructor
  · intro s t hRun
    set u₀ :=
      Instance.update s i.sym (i.emptyExpr.eval s)
      with hu₀
    have hLower : Cmd.BigStep i.lower s u₀ :=
      Cmd.BigStep.assign s i.sym i.emptyExpr
    rcases flattenInit_lowers hExt hFresh hLower with
      ⟨hDown, hProj⟩
    rcases
      flattenGeneral_lift_outer hExt i hFresh G L₀ hRun u₀
        hProj hDown with ⟨v, hV, hProjV, _⟩
    refine ⟨v, ?_, hProjV⟩
    exact
      (Framed.bigStep_unfold_iff _ s v).mpr
        ⟨u₀, v, hLower, hV, Cmd.BigStep.skip v⟩
  · intro s t hRun
    rcases (Framed.bigStep_unfold_iff _ s t).mp hRun with
      ⟨u, v, hInit, hLoop, hClose⟩
    rcases flattenInit_lowers hExt hFresh hInit with
      ⟨hDown, hProj⟩
    have hEq : t = v :=
      (Cmd.bigStep_skip_iff v t).mp hClose
    subst hEq
    rcases
      (flattenGeneral_project hExt i hFresh G L₀ hLoop).2
        hDown with ⟨hOuter, _⟩
    rw [← hProj]
    exact hOuter

/-
  The exit clause of Lemma "Flatten": the inner flag is
  down at every terminal state, reached from any initial
  state.
-/
theorem flattenGeneral_flag_down
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (hFresh : i.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (L₀ : Framed D Δ)
    {s t : Instance D Ω}
    (hRun :
      Cmd.BigStep (flattenGeneral hExt i G L₀).unfold s t) :
    ¬ i.Up t := by
  rcases (Framed.bigStep_unfold_iff _ s t).mp hRun with
    ⟨u, v, hInit, hLoop, hClose⟩
  rcases flattenInit_lowers hExt hFresh hInit with
    ⟨hDown, _⟩
  have hEq : t = v :=
    (Cmd.bigStep_skip_iff v t).mp hClose
  subst hEq
  exact
    ((flattenGeneral_project hExt i hFresh G L₀ hLoop).2
      hDown).2

end Preprocess

end Whiel

------------------------------------------------------------
-- The Flag-Free Flattenings
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  A loop whose source body is loop-free is already a framed
  loop: its unfolding is the source loop.
-/
theorem flattenLoopFree_bigStepEquiv
    (G : Guard D Δ)
    (C₀ : Cmd D Δ) :
    Cmd.BigStepEquiv (.«while» G C₀)
      (flattenLoopFree G C₀).unfold := by
  intro I J
  constructor
  · intro hStep
    exact
      Cmd.BigStep.seq (Cmd.BigStep.skip I)
        (Cmd.BigStep.seq hStep (Cmd.BigStep.skip J))
  · intro hStep
    rcases
      (Framed.bigStep_unfold_iff (flattenLoopFree G C₀) I
        J).mp hStep with
      ⟨K₁, K₂, hInit, hLoop, hClose⟩
    have hK₁ : K₁ = I :=
      (Cmd.bigStep_skip_iff I K₁).mp hInit
    subst hK₁
    have hK₂ : J = K₂ :=
      (Cmd.bigStep_skip_iff K₂ J).mp hClose
    subst hK₂
    exact hLoop

/- Lemma "Flatten", the loop-free body case. -/
theorem flattenLoopFree_equivMod
    (hExt : Ω.extensionOf Δ)
    (G : Guard D Δ)
    {L₀ : Framed D Δ}
    (hBase : L₀.IsBase) :
    EquivMod hExt (.«while» G L₀.unfold)
      ((flattenLoopFree G L₀.close).retagOn
        hExt).unfold := by
  have hMid :
      Cmd.BigStepEquiv (.«while» G L₀.unfold)
        (.«while» G L₀.close) :=
    bigStepEquiv_while G
      (fun I J => bigStep_unfold_iff_of_isBase hBase I J)
  exact
    equivMod_retag_of_bigStepEquiv hExt
      (Cmd.BigStepEquiv.trans hMid
        (flattenLoopFree_bigStepEquiv G L₀.close))

/-
  Lemma "Idempotent nesting" for the operation: with the
  source body a loop on the same guard term, the input
  framed loop is already the answer.
-/
theorem flattenIdem_equivMod
    (hExt : Ω.extensionOf Δ)
    (G : Guard D Δ)
    (L₀ : Framed D Δ)
    (hIdem :
      Cmd.BigStepEquiv (.«while» G L₀.unfold)
        L₀.unfold) :
    EquivMod hExt (.«while» G L₀.unfold)
      ((flattenIdem L₀).retagOn hExt).unfold :=
  equivMod_retag_of_bigStepEquiv hExt hIdem

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
  Loop flattening is correct in every case, with
  the case selected by the source-level Booleans.
-/
theorem flattenWhile_equivMod
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (hFresh : i.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (L₀ : Framed D Δ)
    (idem loopFreeBody : Bool)
    (hIdem :
      idem = true →
        Cmd.BigStepEquiv (.«while» G L₀.unfold)
          L₀.unfold)
    (hBody : loopFreeBody = true → L₀.IsBase) :
    EquivMod hExt (.«while» G L₀.unfold)
      (flattenWhile hExt i G L₀ idem
        loopFreeBody).unfold := by
  unfold flattenWhile
  cases idem with
  | true =>
      exact flattenIdem_equivMod hExt G L₀ (hIdem rfl)
  | false =>
      cases loopFreeBody with
      | true =>
          exact flattenLoopFree_equivMod hExt G (hBody rfl)
      | false =>
          exact flattenGeneral_equivMod hExt i hFresh G L₀

end Preprocess

end Whiel

------------------------------------------------------------
-- Loop-Freeness Of The Flattened Components
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- The general flattening keeps the parts loop-free. -/
theorem flattenGeneral_loopFreeParts
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ)
    {L₀ : Framed D Δ}
    (hParts : L₀.LoopFreeParts) :
    (flattenGeneral hExt i G L₀).LoopFreeParts := by
  obtain ⟨hInit, hBody, hClose⟩ := hParts
  have h₁ : loops L₀.init = 0 := hInit
  have h₂ : loops L₀.body = 0 := hBody
  have h₃ : loops L₀.close = 0 := hClose
  refine ⟨rfl, ?_, rfl⟩
  simp [flattenGeneral, flattenBody, LoopFree, loops,
    FlagSym.raise, FlagSym.lower, h₁, h₂, h₃]

/- The loop-free case keeps the components loop-free. -/
theorem flattenLoopFree_loopFreeParts
    (G : Guard D Δ)
    {C₀ : Cmd D Δ}
    (hBody : LoopFree C₀) :
    (flattenLoopFree G C₀).LoopFreeParts :=
  ⟨rfl, hBody, rfl⟩

/- Every flattening case preserves loop-freeness. -/
theorem flattenWhile_loopFreeParts
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ)
    (L₀ : Framed D Δ)
    (idem loopFreeBody : Bool)
    (hParts : L₀.LoopFreeParts) :
    (flattenWhile hExt i G L₀ idem
      loopFreeBody).LoopFreeParts := by
  have hRetag :
      ∀ L : Framed D Δ, L.LoopFreeParts →
        (L.retagOn hExt).LoopFreeParts := by
    intro L hL
    exact
      ⟨loopFree_of_retag hExt hL.1,
        loopFree_of_retag hExt hL.2.1,
        loopFree_of_retag hExt hL.2.2⟩
  unfold flattenWhile
  cases idem with
  | true => exact hRetag _ hParts
  | false =>
      cases loopFreeBody with
      | true =>
          exact hRetag _
            (flattenLoopFree_loopFreeParts G hParts.2.2)
      | false =>
          exact flattenGeneral_loopFreeParts hExt i G hParts

end Preprocess

end Whiel
