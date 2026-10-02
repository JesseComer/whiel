-- Author: Jesse Comer
import Whiel.Eval.Cmd.Plan
import Databases.UnnamedModel.PrettyPrint

/-
  Fast counterexample checking for Whiel Hoare triples.

  The main checker is:
    * `CexFast.checkCounterexample`

  The public correctness surface is:
    * `CexFast.unsupportedPre_sound`
    * `CexFast.unsupportedPost_sound`
    * `CexFast.preFalse_sound`
    * `CexFast.outOfFuel_sound`
    * `CexFast.postTrue_sound`
    * `CexFast.counterexample_sound`

  Public result and checker definitions occur first.
  Private helper theorems occupy the middle of the file.
  The six key theorem declarations are isolated in the
  final section.
-/

------------------------------------------------------------
-- Public Checker Definitions
------------------------------------------------------------

namespace Whiel

namespace CexFast

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Result of checking one proposed input instance. -/
inductive CheckResult
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) : Type where
| unsupportedPre : CheckResult D Γ
| unsupportedPost : CheckResult D Γ
| preFalse : CheckResult D Γ
| outOfFuel : CheckResult D Γ
| postTrue (J : Instance D Γ) : CheckResult D Γ
| counterexample (J : Instance D Γ) : CheckResult D Γ
deriving DecidableEq

namespace CheckResult

variable [DBLib.Notation.PrettyLiteral D]

/- Render a check result for interactive inspection. -/
def pretty : CheckResult D Γ → String
| .unsupportedPre => "unsupportedPre"
| .unsupportedPost => "unsupportedPost"
| .preFalse => "preFalse"
| .outOfFuel => "outOfFuel"
| .postTrue J => "postTrue " ++ J.pretty
| .counterexample J => "counterexample " ++ J.pretty

/- Render a check result directly in `#eval`. -/
def display (r : CheckResult D Γ) : DBTPretty.Display :=
  DBTPretty.display r.pretty

end CheckResult

variable [LinearOrder D] [Hashable D]

/- Check a supported no-bound counterexample candidate. -/
private def checkCounterexampleNoBound
    (fuel : Nat)
    (pre : AssertExpr D Γ)
    (C : Cmd D Γ)
    (post : AssertExpr D Γ)
    (hPre : pre.NoBoundSymbols)
    (hPost : post.NoBoundSymbols)
    (S : FastInstance D Γ) :
    CheckResult D Γ :=
  match FastGuard.eval (pre.toQF hPre) S with
  | Bool.false =>
      .preFalse
  | Bool.true =>
      match CmdPlan.eval fuel C S with
      | .outOfFuel =>
          .outOfFuel
      | .halted S' =>
          match FastGuard.eval (post.toQF hPost) S' with
          | Bool.true =>
              .postTrue S'.toInstance
          | Bool.false =>
              .counterexample S'.toInstance

/- Check after the precondition is known to be no-bound. -/
private def checkCounterexamplePreNoBound
    (fuel : Nat)
    (pre : AssertExpr D Γ)
    (C : Cmd D Γ)
    (post : AssertExpr D Γ)
    (hPre : pre.NoBoundSymbols)
    (I : Instance D Γ) :
    CheckResult D Γ :=
  if hPost : post.NoBoundSymbols then
    checkCounterexampleNoBound
      fuel pre C post hPre hPost
      (FastInstance.ofInstance I)
  else
    .unsupportedPost

/- Check a proposed finite input counterexample. -/
def checkCounterexample
    (fuel : Nat)
    (pre : AssertExpr D Γ)
    (C : Cmd D Γ)
    (post : AssertExpr D Γ)
    (I : Instance D Γ) :
    CheckResult D Γ :=
  if hPre : pre.NoBoundSymbols then
    checkCounterexamplePreNoBound
      fuel pre C post hPre I
  else
    .unsupportedPre

end CexFast

end Whiel

------------------------------------------------------------
-- Private Helper Theorems
------------------------------------------------------------

namespace Whiel

namespace CexFast

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/-
  Once the precondition is supported, checking cannot report
  unsupported pre.
-/
private theorem preNoBound_ne_unsupportedPre
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {I : Instance D Γ}
    (hPreNo : pre.NoBoundSymbols) :
    checkCounterexamplePreNoBound
        fuel pre C post hPreNo I ≠
      .unsupportedPre := by
  intro hCheck
  unfold checkCounterexamplePreNoBound at hCheck
  by_cases hPostNo : post.NoBoundSymbols
  · rw [dif_pos hPostNo] at hCheck
    unfold checkCounterexampleNoBound at hCheck
    cases hPreFast :
        FastGuard.eval (pre.toQF hPreNo)
          (FastInstance.ofInstance I)
    · rw [hPreFast] at hCheck
      cases hCheck
    · rw [hPreFast] at hCheck
      cases hCmd :
          CmdPlan.eval fuel C
            (FastInstance.ofInstance I) with
      | outOfFuel =>
          rw [hCmd] at hCheck
          cases hCheck
      | halted S' =>
          rw [hCmd] at hCheck
          change
            (match FastGuard.eval
                (post.toQF hPostNo) S' with
            | Bool.true =>
                CheckResult.postTrue S'.toInstance
            | Bool.false =>
                CheckResult.counterexample S'.toInstance) =
              CheckResult.unsupportedPre at hCheck
          cases hPostFast :
              FastGuard.eval (post.toQF hPostNo) S'
          · rw [hPostFast] at hCheck
            cases hCheck
          · rw [hPostFast] at hCheck
            cases hCheck
  · rw [dif_neg hPostNo] at hCheck
    cases hCheck

/-
  Supported no-bound checking never reports unsupported
  postconditions.
-/
private theorem noBound_ne_unsupportedPost
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {S : FastInstance D Γ}
    (hPreNo : pre.NoBoundSymbols)
    (hPostNo : post.NoBoundSymbols) :
    checkCounterexampleNoBound
        fuel pre C post hPreNo hPostNo S ≠
      .unsupportedPost := by
  intro hCheck
  unfold checkCounterexampleNoBound at hCheck
  cases hPreFast :
      FastGuard.eval (pre.toQF hPreNo) S
  · rw [hPreFast] at hCheck
    cases hCheck
  · rw [hPreFast] at hCheck
    cases hCmd : CmdPlan.eval fuel C S with
    | outOfFuel =>
        rw [hCmd] at hCheck
        cases hCheck
    | halted S' =>
        rw [hCmd] at hCheck
        change
          (match FastGuard.eval (post.toQF hPostNo) S' with
          | Bool.true =>
              CheckResult.postTrue S'.toInstance
          | Bool.false =>
              CheckResult.counterexample S'.toInstance) =
            CheckResult.unsupportedPost at hCheck
        cases hPostFast :
            FastGuard.eval (post.toQF hPostNo) S'
        · rw [hPostFast] at hCheck
          cases hCheck
        · rw [hPostFast] at hCheck
          cases hCheck

/-
  A no-bound `preFalse` result means the precondition is
  false.
-/
private theorem noBound_preFalse_sound
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {S : FastInstance D Γ}
    (hPreNo : pre.NoBoundSymbols)
    (hPostNo : post.NoBoundSymbols)
    (hCheck :
      checkCounterexampleNoBound
          fuel pre C post hPreNo hPostNo S =
        .preFalse) :
    ¬ pre.eval S.toInstance := by
  unfold checkCounterexampleNoBound at hCheck
  cases hPreFast :
      FastGuard.eval (pre.toQF hPreNo) S
  · have hNotQF :
        ¬ (pre.toQF hPreNo).eval S.toInstance :=
      (FastGuard.eval_eq_false_iff
        (pre.toQF hPreNo) S).mp hPreFast
    intro hPreEval
    exact hNotQF
      ((AssertExpr.toQF_eval_iff
        pre hPreNo S.toInstance).mpr hPreEval)
  · rw [hPreFast] at hCheck
    cases hCmd : CmdPlan.eval fuel C S with
    | outOfFuel =>
        rw [hCmd] at hCheck
        cases hCheck
    | halted S' =>
        rw [hCmd] at hCheck
        change
          (match FastGuard.eval (post.toQF hPostNo) S' with
          | Bool.true =>
              CheckResult.postTrue S'.toInstance
          | Bool.false =>
              CheckResult.counterexample S'.toInstance) =
            CheckResult.preFalse at hCheck
        cases hPostFast :
            FastGuard.eval (post.toQF hPostNo) S'
        · rw [hPostFast] at hCheck
          cases hCheck
        · rw [hPostFast] at hCheck
          cases hCheck

/-
  A no-bound `outOfFuel` result still certifies
  precondition truth.
-/
private theorem noBound_outOfFuel_sound
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {S : FastInstance D Γ}
    (hPreNo : pre.NoBoundSymbols)
    (hPostNo : post.NoBoundSymbols)
    (hCheck :
      checkCounterexampleNoBound
          fuel pre C post hPreNo hPostNo S =
        .outOfFuel) :
    pre.eval S.toInstance := by
  unfold checkCounterexampleNoBound at hCheck
  cases hPreFast :
      FastGuard.eval (pre.toQF hPreNo) S
  · rw [hPreFast] at hCheck
    cases hCheck
  · have hPreQF :
        (pre.toQF hPreNo).eval S.toInstance :=
      (FastGuard.eval_eq_true_iff
        (pre.toQF hPreNo) S).mp hPreFast
    exact
      (AssertExpr.toQF_eval_iff
        pre hPreNo S.toInstance).mp hPreQF

/-
  A no-bound `postTrue` result validates the successful run.
-/
private theorem noBound_postTrue_sound
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {S : FastInstance D Γ}
    {J : Instance D Γ}
    (hPreNo : pre.NoBoundSymbols)
    (hPostNo : post.NoBoundSymbols)
    (hCheck :
      checkCounterexampleNoBound
          fuel pre C post hPreNo hPostNo S =
        .postTrue J) :
    pre.eval S.toInstance ∧
      Cmd.BigStep C S.toInstance J ∧
      post.eval J := by
  unfold checkCounterexampleNoBound at hCheck
  cases hPreFast :
      FastGuard.eval (pre.toQF hPreNo) S
  · rw [hPreFast] at hCheck
    cases hCheck
  · have hPreQF :
        (pre.toQF hPreNo).eval S.toInstance :=
      (FastGuard.eval_eq_true_iff
        (pre.toQF hPreNo) S).mp hPreFast
    have hPreEval :
        pre.eval S.toInstance :=
      (AssertExpr.toQF_eval_iff
        pre hPreNo S.toInstance).mp hPreQF
    cases hCmd : CmdPlan.eval fuel C S with
    | outOfFuel =>
        rw [hPreFast, hCmd] at hCheck
        cases hCheck
    | halted S' =>
        rw [hPreFast, hCmd] at hCheck
        change
          (match FastGuard.eval (post.toQF hPostNo) S' with
          | Bool.true =>
              CheckResult.postTrue S'.toInstance
          | Bool.false =>
              CheckResult.counterexample S'.toInstance) =
            CheckResult.postTrue J at hCheck
        cases hPostFast :
            FastGuard.eval (post.toQF hPostNo) S'
        · rw [hPostFast] at hCheck
          cases hCheck
        · have hPostQF :
              (post.toQF hPostNo).eval S'.toInstance :=
            (FastGuard.eval_eq_true_iff
              (post.toQF hPostNo) S').mp hPostFast
          have hPostEval :
              post.eval S'.toInstance :=
            (AssertExpr.toQF_eval_iff
              post hPostNo S'.toInstance).mp hPostQF
          have hStep :
              Cmd.BigStep C S.toInstance S'.toInstance :=
            CmdPlan.eval_sound hCmd
          have hResult :
              (CheckResult.postTrue
                S'.toInstance : CheckResult D Γ) =
                  .postTrue J := by
            simpa [hPostFast] using hCheck
          cases hResult
          exact ⟨hPreEval, hStep, hPostEval⟩

/-
  A no-bound `counterexample` result refutes the command
  run.
-/
private theorem noBound_counterexample_sound
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {S : FastInstance D Γ}
    {J : Instance D Γ}
    (hPreNo : pre.NoBoundSymbols)
    (hPostNo : post.NoBoundSymbols)
    (hCheck :
      checkCounterexampleNoBound
          fuel pre C post hPreNo hPostNo S =
        .counterexample J) :
    pre.eval S.toInstance ∧
      Cmd.BigStep C S.toInstance J ∧
      ¬ post.eval J := by
  unfold checkCounterexampleNoBound at hCheck
  cases hPreFast :
      FastGuard.eval (pre.toQF hPreNo) S
  · rw [hPreFast] at hCheck
    cases hCheck
  · have hPreQF :
        (pre.toQF hPreNo).eval S.toInstance :=
      (FastGuard.eval_eq_true_iff
        (pre.toQF hPreNo) S).mp hPreFast
    have hPreEval :
        pre.eval S.toInstance :=
      (AssertExpr.toQF_eval_iff
        pre hPreNo S.toInstance).mp hPreQF
    cases hCmd : CmdPlan.eval fuel C S with
    | outOfFuel =>
        rw [hPreFast, hCmd] at hCheck
        cases hCheck
    | halted S' =>
        rw [hPreFast, hCmd] at hCheck
        change
          (match FastGuard.eval (post.toQF hPostNo) S' with
          | Bool.true =>
              CheckResult.postTrue S'.toInstance
          | Bool.false =>
              CheckResult.counterexample S'.toInstance) =
            CheckResult.counterexample J at hCheck
        cases hPostFast :
            FastGuard.eval (post.toQF hPostNo) S'
        · have hNotPostQF :
              ¬ (post.toQF hPostNo).eval S'.toInstance :=
            (FastGuard.eval_eq_false_iff
              (post.toQF hPostNo) S').mp hPostFast
          have hNotPost :
              ¬ post.eval S'.toInstance := by
            intro hPostEval
            exact hNotPostQF
              ((AssertExpr.toQF_eval_iff
                post hPostNo S'.toInstance).mpr hPostEval)
          have hStep :
              Cmd.BigStep C S.toInstance S'.toInstance :=
            CmdPlan.eval_sound hCmd
          have hResult :
              (CheckResult.counterexample
                S'.toInstance : CheckResult D Γ) =
                  .counterexample J := by
            simpa [hPostFast] using hCheck
          cases hResult
          exact ⟨hPreEval, hStep, hNotPost⟩
        · rw [hPostFast] at hCheck
          cases hCheck

end CexFast

end Whiel

------------------------------------------------------------
-- Key Correctness Theorems
------------------------------------------------------------

namespace Whiel

namespace CexFast

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/-
  `unsupportedPre` means the precondition has bound symbols.
-/
theorem unsupportedPre_sound
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {I : Instance D Γ}
    (hCheck :
      checkCounterexample fuel pre C post I =
        .unsupportedPre) :
    ¬ pre.NoBoundSymbols := by
  unfold checkCounterexample at hCheck
  by_cases hPreNo : pre.NoBoundSymbols
  · rw [dif_pos hPreNo] at hCheck
    exact False.elim
      (preNoBound_ne_unsupportedPre
        (fuel := fuel) (pre := pre) (post := post)
        (C := C) (I := I) hPreNo hCheck)
  · exact hPreNo

/-
  `unsupportedPost` means only the postcondition has bound
  symbols.
-/
theorem unsupportedPost_sound
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {I : Instance D Γ}
    (hCheck :
      checkCounterexample fuel pre C post I =
        .unsupportedPost) :
    pre.NoBoundSymbols ∧ ¬ post.NoBoundSymbols := by
  unfold checkCounterexample at hCheck
  by_cases hPreNo : pre.NoBoundSymbols
  · rw [dif_pos hPreNo] at hCheck
    unfold checkCounterexamplePreNoBound at hCheck
    by_cases hPostNo : post.NoBoundSymbols
    · rw [dif_pos hPostNo] at hCheck
      exact False.elim
        (noBound_ne_unsupportedPost
          (fuel := fuel) (pre := pre) (post := post)
          (C := C) (S := FastInstance.ofInstance I)
          hPreNo hPostNo hCheck)
    · exact ⟨hPreNo, hPostNo⟩
  · rw [dif_neg hPreNo] at hCheck
    cases hCheck

/-
  `preFalse` means the proposed input does not satisfy the
  precondition.
-/
theorem preFalse_sound
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {I : Instance D Γ}
    (hCheck :
      checkCounterexample fuel pre C post I =
        .preFalse) :
    ¬ pre.eval I := by
  unfold checkCounterexample at hCheck
  by_cases hPreNo : pre.NoBoundSymbols
  · rw [dif_pos hPreNo] at hCheck
    unfold checkCounterexamplePreNoBound at hCheck
    by_cases hPostNo : post.NoBoundSymbols
    · rw [dif_pos hPostNo] at hCheck
      have hPreFalse :
          ¬ pre.eval
              (FastInstance.ofInstance I).toInstance :=
        noBound_preFalse_sound
          hPreNo hPostNo hCheck
      simpa [FastInstance.toInstance_ofInstance]
        using hPreFalse
    · rw [dif_neg hPostNo] at hCheck
      cases hCheck
  · rw [dif_neg hPreNo] at hCheck
    cases hCheck

/-
  `outOfFuel` still certifies that the precondition holds.
-/
theorem outOfFuel_sound
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {I : Instance D Γ}
    (hCheck :
      checkCounterexample fuel pre C post I =
        .outOfFuel) :
    pre.eval I := by
  unfold checkCounterexample at hCheck
  by_cases hPreNo : pre.NoBoundSymbols
  · rw [dif_pos hPreNo] at hCheck
    unfold checkCounterexamplePreNoBound at hCheck
    by_cases hPostNo : post.NoBoundSymbols
    · rw [dif_pos hPostNo] at hCheck
      have hPre :
          pre.eval
              (FastInstance.ofInstance I).toInstance :=
        noBound_outOfFuel_sound
          hPreNo hPostNo hCheck
      simpa [FastInstance.toInstance_ofInstance]
        using hPre
    · rw [dif_neg hPostNo] at hCheck
      cases hCheck
  · rw [dif_neg hPreNo] at hCheck
    cases hCheck

/-
  `postTrue` validates a successful run satisfying the
  postcondition.
-/
theorem postTrue_sound
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    (hCheck :
      checkCounterexample fuel pre C post I =
        .postTrue J) :
    pre.eval I ∧ Cmd.BigStep C I J ∧ post.eval J := by
  unfold checkCounterexample at hCheck
  by_cases hPreNo : pre.NoBoundSymbols
  · rw [dif_pos hPreNo] at hCheck
    unfold checkCounterexamplePreNoBound at hCheck
    by_cases hPostNo : post.NoBoundSymbols
    · rw [dif_pos hPostNo] at hCheck
      have hSound :
          pre.eval
              (FastInstance.ofInstance I).toInstance ∧
            Cmd.BigStep C
              (FastInstance.ofInstance I).toInstance J ∧
            post.eval J :=
        noBound_postTrue_sound
          hPreNo hPostNo hCheck
      simpa [FastInstance.toInstance_ofInstance]
        using hSound
    · rw [dif_neg hPostNo] at hCheck
      cases hCheck
  · rw [dif_neg hPreNo] at hCheck
    cases hCheck

/- A `counterexample` result refutes the Hoare triple. -/
theorem counterexample_sound
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    (hCheck :
      checkCounterexample fuel pre C post I =
        .counterexample J) :
    pre.eval I ∧
      Cmd.BigStep C I J ∧
      ¬ post.eval J := by
  unfold checkCounterexample at hCheck
  by_cases hPreNo : pre.NoBoundSymbols
  · rw [dif_pos hPreNo] at hCheck
    unfold checkCounterexamplePreNoBound at hCheck
    by_cases hPostNo : post.NoBoundSymbols
    · rw [dif_pos hPostNo] at hCheck
      have hSound :
          pre.eval
              (FastInstance.ofInstance I).toInstance ∧
            Cmd.BigStep C
              (FastInstance.ofInstance I).toInstance J ∧
            ¬ post.eval J :=
        noBound_counterexample_sound
          hPreNo hPostNo hCheck
      simpa [FastInstance.toInstance_ofInstance]
        using hSound
    · rw [dif_neg hPostNo] at hCheck
      cases hCheck
  · rw [dif_neg hPreNo] at hCheck
    cases hCheck

end CexFast

end Whiel
