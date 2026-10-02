-- Author: Jesse Comer
import Whiel.Cmd.Semantics
import Whiel.Eval.Assertion.QF
import Whiel.Eval.RA.UnionPlan

/-
  Fuelled command execution over materialized instances.

  The evaluator keeps runtime state in `FastInstance`.
  Halted runs are sound for the existing `Cmd.BigStep`
  semantics after conversion with `FastInstance.toInstance`.
-/

------------------------------------------------------------
-- Fast Fuelled Command Evaluation
------------------------------------------------------------

namespace Whiel

namespace CmdFast

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Result of a fast fuelled command run. -/
inductive Result
    (D : Type)
    [Domain D] [LinearOrder D] [Hashable D]
    (Γ : UnnamedSchema A) : Type where
| halted (S : FastInstance D Γ) : Result D Γ
| outOfFuel : Result D Γ

/- Fast fuelled evaluator over materialized instances. -/
def eval :
    Nat → Cmd D Γ → FastInstance D Γ → Result D Γ
| 0, _, _ =>
    .outOfFuel
| fuel + 1, C, S =>
    match C with
    | .skip =>
        .halted S
    | .assign X e =>
        .halted (S.update X (UnionPlan.eval e S))
    | .seq C₁ C₂ =>
        match eval fuel C₁ S with
        | .halted S₁ => eval fuel C₂ S₁
        | .outOfFuel => .outOfFuel
    | .ite G C₁ C₂ =>
        if FastGuard.eval G S then
          eval fuel C₁ S
        else
          eval fuel C₂ S
    | .while G Body =>
        if FastGuard.eval G S then
          match eval fuel Body S with
          | .halted S₁ => eval fuel (.while G Body) S₁
          | .outOfFuel => .outOfFuel
        else
          .halted S

end CmdFast

end Whiel

------------------------------------------------------------
-- Fast Fuelled Command Soundness
------------------------------------------------------------

namespace Whiel

namespace CmdFast

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Halted fast evaluation is sound for big-step semantics. -/
theorem eval_sound
    {fuel : Nat}
    {C : Cmd D Γ}
    {S S' : FastInstance D Γ}
    (hEval : eval fuel C S = .halted S') :
    Cmd.BigStep C S.toInstance S'.toInstance := by
  induction fuel generalizing C S S' with
  | zero =>
      change (Result.outOfFuel : Result D Γ) = .halted S' at hEval
      cases hEval
  | succ fuel ih =>
      cases C with
      | skip =>
          change (Result.halted S : Result D Γ) = .halted S' at hEval
          cases hEval
          exact Cmd.BigStep.skip S.toInstance
      | assign X e =>
          change
            (Result.halted
              (S.update X (UnionPlan.eval e S)) :
              Result D Γ) = .halted S' at hEval
          cases hEval
          rw [FastInstance.toInstance_update,
            UnionPlan.eval_correct]
          exact Cmd.BigStep.assign S.toInstance X e
      | seq C₁ C₂ =>
          change
            (match eval fuel C₁ S with
            | .halted S₁ => eval fuel C₂ S₁
            | .outOfFuel => .outOfFuel) = .halted S' at hEval
          cases h₁ : eval fuel C₁ S with
          | halted S₁ =>
              have h₂ :
                  eval fuel C₂ S₁ = .halted S' := by
                simpa [h₁] using hEval
              exact Cmd.BigStep.seq
                (ih h₁) (ih h₂)
          | outOfFuel =>
              rw [h₁] at hEval
              cases hEval
      | ite G C₁ C₂ =>
          change
            (if FastGuard.eval G S then
              eval fuel C₁ S
            else
              eval fuel C₂ S) = .halted S' at hEval
          cases hG : FastGuard.eval G S
          · have h₂ :
                eval fuel C₂ S = .halted S' := by
              simpa [hG] using hEval
            have hNotG :
                ¬ G.eval S.toInstance :=
              (FastGuard.eval_eq_false_iff G S).mp hG
            exact Cmd.BigStep.ite_false hNotG (ih h₂)
          · have h₁ :
                eval fuel C₁ S = .halted S' := by
              simpa [hG] using hEval
            have hTrueG :
                G.eval S.toInstance :=
              (FastGuard.eval_eq_true_iff G S).mp hG
            exact Cmd.BigStep.ite_true hTrueG (ih h₁)
      | «while» G Body =>
          change
            (if FastGuard.eval G S then
              match eval fuel Body S with
              | .halted S₁ => eval fuel (.while G Body) S₁
              | .outOfFuel => .outOfFuel
            else
              .halted S) = .halted S' at hEval
          cases hG : FastGuard.eval G S
          · have hDone :
                (Result.halted S : Result D Γ) = .halted S' := by
              simpa [hG] using hEval
            have hNotG :
                ¬ G.eval S.toInstance :=
              (FastGuard.eval_eq_false_iff G S).mp hG
            cases hDone
            exact Cmd.BigStep.while_false hNotG
          · have hEvalLoop :
                (match eval fuel Body S with
                | .halted S₁ => eval fuel (.while G Body) S₁
                | .outOfFuel => .outOfFuel) = .halted S' := by
              simpa [hG] using hEval
            cases hBody : eval fuel Body S with
            | halted S₁ =>
                have hLoop :
                    eval fuel (.while G Body) S₁ =
                      .halted S' := by
                  simpa [hBody] using hEvalLoop
                have hTrueG :
                    G.eval S.toInstance :=
                  (FastGuard.eval_eq_true_iff G S).mp hG
                exact Cmd.BigStep.while_true
                  hTrueG (ih hBody) (ih hLoop)
            | outOfFuel =>
                rw [hBody] at hEvalLoop
                cases hEvalLoop

end CmdFast

end Whiel
