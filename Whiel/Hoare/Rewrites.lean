-- Author: Jesse Comer
import Whiel.Hoare.Concrete

/-
  Hoare-triple rewrites for Whiel.

  This file contains rewrites that transform Hoare triples
  while preserving their validity. It uses command rewrites
  from `Whiel.Cmd.Rewrites.FramedLoop` and concrete
  assertion transformers from `Whiel.Hoare.Concrete`.

  Main constructions:
    * `AssertExpr.framedLoopPre`
    * `AssertExpr.framedLoopPost`
    * `Hoare.framedLoopHoareRewrite?`

  Main correctness theorems:
    * `Hoare.hoareValid_framedLoopCommand_iff_loopOnly`
    * `Hoare.hoareValid_framedLoopCommand_of_loopOnly`
    * `Hoare.hoareValid_framedLoopParts?_iff_loopOnly`
    * `Hoare.hoareValid_framedLoopParts?_of_loopOnly`
    * `Hoare.framedLoopHoareRewrite?_sound`
    * `Hoare.hoareValid_of_framedLoopHoareRewrite?`
    * `Hoare.hoareValid_of_framedLoopHoareRewrite?_vcs`
-/

------------------------------------------------------------
-- Framed-Loop Assertion Rewrites
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Rewrite a precondition across a loop-free init block. -/
def framedLoopPre
    (Init : Cmd D Γ)
    (hInit : Init.LoopFree)
    (pre : AssertExpr D Γ) :
    AssertExpr D Γ :=
  spLoopFree Init hInit pre

/-
  Rewrite a postcondition across a loop-free close block.
-/
def framedLoopPost
    (Close : Cmd D Γ)
    (hClose : Close.LoopFree)
    (post : AssertExpr D Γ) :
    AssertExpr D Γ :=
  wpLoopFree Close hClose post

end AssertExpr

end Whiel

------------------------------------------------------------
-- Framed-Loop Hoare Rewrites
------------------------------------------------------------

namespace Whiel

namespace Hoare

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Rewrite a framed-loop triple to its loop-only triple. -/
theorem hoareValid_framedLoopCommand_iff_loopOnly
    (pre post : AssertExpr D Γ)
    (Init : Cmd D Γ)
    (G : Guard D Γ)
    (Body Close : Cmd D Γ)
    (hInit : Init.LoopFree)
    (hClose : Close.LoopFree) :
    HoareValid pre
      (Cmd.framedLoopCommand Init G Body Close)
      post ↔
      HoareValid
        (AssertExpr.framedLoopPre Init hInit pre)
        (.while G Body)
        (AssertExpr.framedLoopPost Close hClose post) := by
  constructor
  · intro h L M hPreLoop hLoop
    exact
      (AssertExpr.wpLoopFree_eval_iff
        Close hClose post M).mpr
        (by
          intro J hCloseStep
          have hInitSP :
              sp Init pre.eval L :=
            (AssertExpr.spLoopFree_eval_iff
              Init hInit pre L).mp
              (by
                simpa [AssertExpr.framedLoopPre] using
                  hPreLoop)
          rcases hInitSP with
            ⟨I, hPre, hInitStep⟩
          have hStep :
              Cmd.BigStep
                (Cmd.framedLoopCommand Init G Body Close)
                I
                J := by
            unfold Cmd.framedLoopCommand
            exact
              Cmd.BigStep.seq
                (Cmd.BigStep.seq hInitStep hLoop)
                hCloseStep
          exact h I J hPre hStep)
  · intro h I J hPre hStep
    change
      Cmd.BigStep
        (.seq (.seq Init (.while G Body)) Close)
        I
        J at hStep
    rcases
      (Cmd.bigStep_seq_iff
        (.seq Init (.while G Body))
        Close
        I
        J).mp hStep
      with ⟨M, hInitLoop, hCloseStep⟩
    rcases
      (Cmd.bigStep_seq_iff Init (.while G Body) I M).mp
        hInitLoop
      with ⟨L, hInitStep, hLoop⟩
    have hPreLoop :
        (AssertExpr.framedLoopPre Init hInit pre).eval
          L := by
      exact
        (AssertExpr.spLoopFree_eval_iff
          Init hInit pre L).mpr
          ⟨I, hPre, hInitStep⟩
    have hPostLoop :
        (AssertExpr.framedLoopPost
          Close hClose post).eval M :=
      h L M hPreLoop hLoop
    have hCloseWP :
        wp Close post.eval M :=
      (AssertExpr.wpLoopFree_eval_iff
        Close hClose post M).mp
        (by
          simpa [AssertExpr.framedLoopPost] using
            hPostLoop)
    exact hCloseWP J hCloseStep

/- A loop-only triple proves the framed-loop triple. -/
theorem hoareValid_framedLoopCommand_of_loopOnly
    (pre post : AssertExpr D Γ)
    (Init : Cmd D Γ)
    (G : Guard D Γ)
    (Body Close : Cmd D Γ)
    (hInit : Init.LoopFree)
    (hClose : Close.LoopFree)
    (hLoop :
      HoareValid
        (AssertExpr.framedLoopPre Init hInit pre)
        (.while G Body)
        (AssertExpr.framedLoopPost Close hClose post)) :
    HoareValid pre
      (Cmd.framedLoopCommand Init G Body Close)
      post :=
  (hoareValid_framedLoopCommand_iff_loopOnly
    pre post Init G Body Close hInit hClose).mpr hLoop

/- Rewrite a decomposed command to its loop-only triple. -/
theorem hoareValid_framedLoopParts?_iff_loopOnly
    (pre post : AssertExpr D Γ)
    {C Init : Cmd D Γ}
    {G : Guard D Γ}
    {Body Close : Cmd D Γ}
    (hParts :
      C.framedLoopParts? =
        some (Init, G, Body, Close)) :
    HoareValid pre C post ↔
      HoareValid
        (AssertExpr.framedLoopPre Init
          (Cmd.framedLoopParts?_sound hParts).1.1
          pre)
        (.while G Body)
        (AssertExpr.framedLoopPost Close
          (Cmd.framedLoopParts?_sound hParts).2.2.1
          post) := by
  let hSound := Cmd.framedLoopParts?_sound hParts
  let hInit : Init.LoopFree := hSound.1.1
  let hClose : Close.LoopFree := hSound.2.2.1
  have hEquiv :
      Cmd.BigStepEquiv C
        (Cmd.framedLoopCommand Init G Body Close) :=
    hSound.2.2.2
  calc
    HoareValid pre C post
        ↔ HoareValid pre
            (Cmd.framedLoopCommand Init G Body Close)
            post :=
          hoareValid_congr_cmd hEquiv
    _ ↔ HoareValid
          (AssertExpr.framedLoopPre Init hInit pre)
          (.while G Body)
          (AssertExpr.framedLoopPost Close hClose post) :=
          hoareValid_framedLoopCommand_iff_loopOnly
            pre post Init G Body Close hInit hClose

/-
  A decomposed loop-only triple proves the source triple.
-/
theorem hoareValid_framedLoopParts?_of_loopOnly
    (pre post : AssertExpr D Γ)
    {C Init : Cmd D Γ}
    {G : Guard D Γ}
    {Body Close : Cmd D Γ}
    (hParts :
      C.framedLoopParts? =
        some (Init, G, Body, Close))
    (hLoop :
      HoareValid
        (AssertExpr.framedLoopPre Init
          (Cmd.framedLoopParts?_sound hParts).1.1
          pre)
        (.while G Body)
        (AssertExpr.framedLoopPost Close
          (Cmd.framedLoopParts?_sound hParts).2.2.1
          post)) :
    HoareValid pre C post :=
  (hoareValid_framedLoopParts?_iff_loopOnly
    pre post hParts).mpr hLoop

/-
  Compute the loop-only triple for a framed-loop command.
-/
def framedLoopHoareRewrite?
    (C : Cmd D Γ)
    (pre post : AssertExpr D Γ) :
    Option
      (AssertExpr D Γ × Cmd D Γ × AssertExpr D Γ) :=
  match hParts : C.framedLoopParts? with
  | none =>
      none
  | some (Init, G, Body, Close) =>
      let hSound := Cmd.framedLoopParts?_sound hParts
      let hInit : Init.LoopFree := hSound.1.1
      let hClose : Close.LoopFree := hSound.2.2.1
      some
        (AssertExpr.framedLoopPre Init hInit pre,
          .while G Body,
          AssertExpr.framedLoopPost Close hClose post)

/-
  A successful computed rewrite preserves Hoare validity.
-/
theorem framedLoopHoareRewrite?_sound
    {C Loop : Cmd D Γ}
    {pre post pre' post' : AssertExpr D Γ}
    (hRewrite :
      framedLoopHoareRewrite? C pre post =
        some (pre', Loop, post')) :
    HoareValid pre C post ↔
      HoareValid pre' Loop post' := by
  unfold framedLoopHoareRewrite? at hRewrite
  split at hRewrite
  · contradiction
  · rename_i Init G Body Close hParts
    cases hRewrite
    exact
      hoareValid_framedLoopParts?_iff_loopOnly
        pre post hParts

/- A computed loop-only triple proves the source triple. -/
theorem hoareValid_of_framedLoopHoareRewrite?
    {C Loop : Cmd D Γ}
    {pre post pre' post' : AssertExpr D Γ}
    (hRewrite :
      framedLoopHoareRewrite? C pre post =
        some (pre', Loop, post'))
    (hLoop : HoareValid pre' Loop post') :
    HoareValid pre C post :=
  (framedLoopHoareRewrite?_sound hRewrite).mpr hLoop

/-
  Generated loop-only invariant VCs prove the original
  framed-loop triple after a successful rewrite.
-/
theorem hoareValid_of_framedLoopHoareRewrite?_vcs
    {C Body : Cmd D Γ}
    {pre post pre' post' inv : AssertExpr D Γ}
    {G : Guard D Γ}
    (hBody : Body.LoopFree)
    (hRewrite :
      framedLoopHoareRewrite? C pre post =
        some (pre', .while G Body, post'))
    (hInit :
      loopOnlyInitValid pre' inv)
    (hMaint :
      loopOnlyMaintValid inv G Body hBody)
    (hTerm :
      loopOnlyTermValid inv post' G) :
    HoareValid pre C post := by
  exact
    hoareValid_of_framedLoopHoareRewrite? hRewrite
      (hoareValid_loopOnly_of_invariantVCs
        pre' post' inv G Body hBody
        hInit hMaint hTerm)

end Hoare

end Whiel
