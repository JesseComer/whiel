-- Author: Jesse Comer
import Whiel.Cmd.Semantics

/-
  Fuelled reference evaluator for Whiel commands.

  This file intentionally uses the existing proof-facing
  instance, RA, and guard semantics.  It provides the simple
  soundness target mirrored by the materialized evaluator:
  a halted fuelled run gives a `Cmd.BigStep` derivation.
-/

------------------------------------------------------------
-- Fuelled Command Evaluation
------------------------------------------------------------

namespace Whiel

namespace CmdFuel

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Result of a fuelled command run. -/
inductive Result
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) : Type where
| halted (J : Instance D Γ) : Result D Γ
| outOfFuel : Result D Γ

/- Fuelled evaluator over ordinary instances. -/
def eval :
    Nat → Cmd D Γ → Instance D Γ → Result D Γ
| 0, _, _ =>
    .outOfFuel
| fuel + 1, C, I =>
    match C with
    | .skip =>
        .halted I
    | .assign X e =>
        .halted (Instance.update I X (e.eval I))
    | .seq C₁ C₂ =>
        match eval fuel C₁ I with
        | .halted I₁ => eval fuel C₂ I₁
        | .outOfFuel => .outOfFuel
    | .ite G C₁ C₂ =>
        if G.eval I then
          eval fuel C₁ I
        else
          eval fuel C₂ I
    | .while G Body =>
        if G.eval I then
          match eval fuel Body I with
          | .halted I₁ => eval fuel (.while G Body) I₁
          | .outOfFuel => .outOfFuel
        else
          .halted I

end CmdFuel

end Whiel

------------------------------------------------------------
-- Fuelled Command Soundness
------------------------------------------------------------

namespace Whiel

namespace CmdFuel

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Halted fuelled evaluation is sound for big-step semantics. -/
theorem eval_sound
    {fuel : Nat}
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    (hEval : eval fuel C I = .halted J) :
    Cmd.BigStep C I J := by
  induction fuel generalizing C I J with
  | zero =>
      change (Result.outOfFuel : Result D Γ) = .halted J at hEval
      cases hEval
  | succ fuel ih =>
      cases C with
      | skip =>
          change (Result.halted I : Result D Γ) = .halted J at hEval
          cases hEval
          exact Cmd.BigStep.skip I
      | assign X e =>
          change
            (Result.halted (Instance.update I X (e.eval I)) :
              Result D Γ) = .halted J at hEval
          cases hEval
          exact Cmd.BigStep.assign I X e
      | seq C₁ C₂ =>
          change
            (match eval fuel C₁ I with
            | .halted I₁ => eval fuel C₂ I₁
            | .outOfFuel => .outOfFuel) = .halted J at hEval
          cases h₁ : eval fuel C₁ I with
          | halted I₁ =>
              have h₂ :
                  eval fuel C₂ I₁ = .halted J := by
                simpa [h₁] using hEval
              exact Cmd.BigStep.seq
                (ih h₁) (ih h₂)
          | outOfFuel =>
              rw [h₁] at hEval
              cases hEval
      | ite G C₁ C₂ =>
          change
            (if G.eval I then
              eval fuel C₁ I
            else
              eval fuel C₂ I) = .halted J at hEval
          by_cases hG : G.eval I
          · have h₁ :
                eval fuel C₁ I = .halted J := by
              simpa [hG] using hEval
            exact Cmd.BigStep.ite_true hG (ih h₁)
          · have h₂ :
                eval fuel C₂ I = .halted J := by
              simpa [hG] using hEval
            exact Cmd.BigStep.ite_false hG (ih h₂)
      | «while» G Body =>
          change
            (if G.eval I then
              match eval fuel Body I with
              | .halted I₁ => eval fuel (.while G Body) I₁
              | .outOfFuel => .outOfFuel
            else
              .halted I) = .halted J at hEval
          by_cases hG : G.eval I
          · have hEvalLoop :
                (match eval fuel Body I with
                | .halted I₁ => eval fuel (.while G Body) I₁
                | .outOfFuel => .outOfFuel) = .halted J := by
              simpa [hG] using hEval
            cases hBody : eval fuel Body I with
            | halted I₁ =>
                have hLoop :
                    eval fuel (.while G Body) I₁ =
                      .halted J := by
                  simpa [hBody] using hEvalLoop
                exact Cmd.BigStep.while_true
                  hG (ih hBody) (ih hLoop)
            | outOfFuel =>
                rw [hBody] at hEvalLoop
                cases hEvalLoop
          · have hDone :
                (Result.halted I : Result D Γ) = .halted J := by
              simpa [hG] using hEval
            cases hDone
            exact Cmd.BigStep.while_false hG

end CmdFuel

end Whiel
