-- Author: Jesse Comer
import Whiel.Eval.Cmd.Fuel

/-
  Fuel-counting companion of the fuelled reference
  evaluator.

  `CmdFuel.evalCount` repeats the recursion structure of
  `CmdFuel.eval` and additionally reports the fuel left
  over. The fuel of `eval` bounds the *depth* of the
  recursion, not a number of steps: a sequence gives the
  same fuel to both components, so the fuel left over after
  a compound command is the minimum of the fuel left over
  by its parts.

  `evalCount_fst` states that counting changes nothing about
  the result. `eval_evalConsumed` states that the measured
  consumption is itself a sufficient bound: a halting run
  halts the same way under `evalConsumed`, so a caller may
  freeze the smaller measured bound in place of the bound it
  was given. `eval_halted_mono` is the monotonicity fact the
  measurement rests on, and the fact that lets a frozen
  bound be re-checked under any larger one.
-/

------------------------------------------------------------
-- Fuel-Counting Command Evaluation
------------------------------------------------------------

namespace Whiel

namespace CmdFuel

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Fuelled evaluation reporting the fuel left over. -/
def evalCount :
    Nat → Cmd D Γ → Instance D Γ → Result D Γ × Nat
| 0, _, _ =>
    (.outOfFuel, 0)
| fuel + 1, C, I =>
    match C with
    | .skip =>
        (.halted I, fuel)
    | .assign X e =>
        (.halted (Instance.update I X (e.eval I)), fuel)
    | .seq C₁ C₂ =>
        match evalCount fuel C₁ I with
        | (.halted I₁, leftFirst) =>
            match evalCount fuel C₂ I₁ with
            | (result, leftSecond) =>
                (result, min leftFirst leftSecond)
        | (.outOfFuel, leftFirst) =>
            (.outOfFuel, leftFirst)
    | .ite G C₁ C₂ =>
        if G.eval I then
          evalCount fuel C₁ I
        else
          evalCount fuel C₂ I
    | .while G Body =>
        if G.eval I then
          match evalCount fuel Body I with
          | (.halted I₁, leftBody) =>
              match evalCount fuel (.while G Body) I₁ with
              | (result, leftRest) =>
                  (result, min leftBody leftRest)
          | (.outOfFuel, leftBody) =>
              (.outOfFuel, leftBody)
        else
          (.halted I, fuel)

/- Fuel consumed by one fuelled run under a bound. -/
def evalConsumed
    (fuel : Nat)
    (C : Cmd D Γ)
    (I : Instance D Γ) : Nat :=
  fuel - (evalCount fuel C I).2

end CmdFuel

end Whiel

------------------------------------------------------------
-- Counting Agreement
------------------------------------------------------------

namespace Whiel

namespace CmdFuel

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Counting the fuel does not change the result. -/
theorem evalCount_fst :
    ∀ (fuel : Nat) (C : Cmd D Γ) (I : Instance D Γ),
      (evalCount fuel C I).1 = eval fuel C I := by
  intro fuel
  induction fuel with
  | zero =>
      intro C I
      rfl
  | succ fuel ih =>
      intro C I
      cases C with
      | skip =>
          rfl
      | assign X e =>
          rfl
      | seq C₁ C₂ =>
          change
            (match evalCount fuel C₁ I with
              | (.halted I₁, leftFirst) =>
                  match evalCount fuel C₂ I₁ with
                  | (result, leftSecond) =>
                      (result, min leftFirst leftSecond)
              | (.outOfFuel, leftFirst) =>
                  (.outOfFuel, leftFirst)).1 =
            (match eval fuel C₁ I with
              | .halted I₁ => eval fuel C₂ I₁
              | .outOfFuel => .outOfFuel)
          have hFirst := ih C₁ I
          cases hCount : evalCount fuel C₁ I with
          | mk result leftFirst =>
              rw [hCount] at hFirst
              cases result with
              | halted I₁ =>
                  simp only [hFirst.symm]
                  cases hCountSecond :
                      evalCount fuel C₂ I₁ with
                  | mk resultSecond leftSecond =>
                      have hSecond := ih C₂ I₁
                      rw [hCountSecond] at hSecond
                      simpa using hSecond
              | outOfFuel =>
                  simp only [hFirst.symm]
      | ite G C₁ C₂ =>
          change
            (if G.eval I then
              evalCount fuel C₁ I
            else
              evalCount fuel C₂ I).1 =
            (if G.eval I then
              eval fuel C₁ I
            else
              eval fuel C₂ I)
          by_cases hGuard : G.eval I
          · simp only [hGuard, if_true]
            exact ih C₁ I
          · simp only [hGuard, if_false]
            exact ih C₂ I
      | «while» G Body =>
          change
            (if G.eval I then
              match evalCount fuel Body I with
              | (.halted I₁, leftBody) =>
                  match evalCount fuel (.while G Body) I₁ with
                  | (result, leftRest) =>
                      (result, min leftBody leftRest)
              | (.outOfFuel, leftBody) =>
                  (.outOfFuel, leftBody)
            else
              (.halted I, fuel)).1 =
            (if G.eval I then
              match eval fuel Body I with
              | .halted I₁ => eval fuel (.while G Body) I₁
              | .outOfFuel => .outOfFuel
            else
              .halted I)
          by_cases hGuard : G.eval I
          · simp only [hGuard, if_true]
            have hBody := ih Body I
            cases hCount : evalCount fuel Body I with
            | mk result leftBody =>
                rw [hCount] at hBody
                cases result with
                | halted I₁ =>
                    simp only [hBody.symm]
                    cases hCountRest :
                        evalCount fuel (.while G Body) I₁ with
                    | mk resultRest leftRest =>
                        have hRest :=
                          ih (.while G Body) I₁
                        rw [hCountRest] at hRest
                        simpa using hRest
                | outOfFuel =>
                    simp only [hBody.symm]
          · simp only [hGuard, if_false]

end CmdFuel

end Whiel

------------------------------------------------------------
-- Fuel Monotonicity
------------------------------------------------------------

namespace Whiel

namespace CmdFuel

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- A halted fuelled run halts the same way under more fuel. -/
theorem eval_halted_mono
    {fuel fuel' : Nat}
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    (hEval : eval fuel C I = .halted J)
    (hLe : fuel ≤ fuel') :
    eval fuel' C I = .halted J := by
  induction fuel generalizing fuel' C I J with
  | zero =>
      change (Result.outOfFuel : Result D Γ) = .halted J
        at hEval
      cases hEval
  | succ fuel ih =>
      cases fuel' with
      | zero => exact (Nat.not_succ_le_zero fuel hLe).elim
      | succ fuel' =>
          have hLe' : fuel ≤ fuel' := by omega
          cases C with
          | skip =>
              change (Result.halted I : Result D Γ) =
                .halted J at hEval
              cases hEval
              rfl
          | assign X e =>
              change
                (Result.halted (Instance.update I X (e.eval I)) :
                  Result D Γ) = .halted J at hEval
              cases hEval
              rfl
          | seq C₁ C₂ =>
              change
                (match eval fuel C₁ I with
                | .halted I₁ => eval fuel C₂ I₁
                | .outOfFuel => .outOfFuel) = .halted J at hEval
              change
                (match eval fuel' C₁ I with
                | .halted I₁ => eval fuel' C₂ I₁
                | .outOfFuel => .outOfFuel) = .halted J
              cases h₁ : eval fuel C₁ I with
              | halted I₁ =>
                  have h₂ : eval fuel C₂ I₁ = .halted J := by
                    simpa [h₁] using hEval
                  rw [ih h₁ hLe']
                  exact ih h₂ hLe'
              | outOfFuel =>
                  rw [h₁] at hEval
                  cases hEval
          | ite G C₁ C₂ =>
              change
                (if G.eval I then
                  eval fuel C₁ I
                else
                  eval fuel C₂ I) = .halted J at hEval
              change
                (if G.eval I then
                  eval fuel' C₁ I
                else
                  eval fuel' C₂ I) = .halted J
              by_cases hG : G.eval I
              · have h₁ : eval fuel C₁ I = .halted J := by
                  simpa [hG] using hEval
                simp only [hG, if_true]
                exact ih h₁ hLe'
              · have h₂ : eval fuel C₂ I = .halted J := by
                  simpa [hG] using hEval
                simp only [hG, if_false]
                exact ih h₂ hLe'
          | «while» G Body =>
              change
                (if G.eval I then
                  match eval fuel Body I with
                  | .halted I₁ => eval fuel (.while G Body) I₁
                  | .outOfFuel => .outOfFuel
                else
                  .halted I) = .halted J at hEval
              change
                (if G.eval I then
                  match eval fuel' Body I with
                  | .halted I₁ => eval fuel' (.while G Body) I₁
                  | .outOfFuel => .outOfFuel
                else
                  .halted I) = .halted J
              by_cases hG : G.eval I
              · have hLoop :
                    (match eval fuel Body I with
                    | .halted I₁ => eval fuel (.while G Body) I₁
                    | .outOfFuel => .outOfFuel) = .halted J := by
                  simpa [hG] using hEval
                simp only [hG, if_true]
                cases hBody : eval fuel Body I with
                | halted I₁ =>
                    have hRest :
                        eval fuel (.while G Body) I₁ =
                          .halted J := by
                      simpa [hBody] using hLoop
                    rw [ih hBody hLe']
                    exact ih hRest hLe'
                | outOfFuel =>
                    rw [hBody] at hLoop
                    cases hLoop
              · have hDone :
                    (Result.halted I : Result D Γ) = .halted J := by
                  simpa [hG] using hEval
                cases hDone
                simp only [hG, if_false]

end CmdFuel

end Whiel

------------------------------------------------------------
-- Sufficiency of the Measured Consumption
------------------------------------------------------------

namespace Whiel

namespace CmdFuel

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- A halting run leaves strictly less fuel than its bound. -/
theorem evalCount_snd_lt_of_halted
    {fuel : Nat}
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    {left : Nat}
    (hCount : evalCount fuel C I = (.halted J, left)) :
    left < fuel := by
  induction fuel generalizing C I J left with
  | zero =>
      change ((Result.outOfFuel : Result D Γ), 0) =
        (.halted J, left) at hCount
      simp at hCount
  | succ fuel ih =>
      cases C with
      | skip =>
          change ((Result.halted I : Result D Γ), fuel) =
            (.halted J, left) at hCount
          rw [Prod.mk.injEq] at hCount
          omega
      | assign X e =>
          change
            ((Result.halted (Instance.update I X (e.eval I)) :
              Result D Γ), fuel) = (.halted J, left) at hCount
          rw [Prod.mk.injEq] at hCount
          omega
      | seq C₁ C₂ =>
          change
            (match evalCount fuel C₁ I with
            | (.halted I₁, leftFirst) =>
                match evalCount fuel C₂ I₁ with
                | (result, leftSecond) =>
                    (result, min leftFirst leftSecond)
            | (.outOfFuel, leftFirst) =>
                (.outOfFuel, leftFirst)) =
            (.halted J, left) at hCount
          cases h₁ : evalCount fuel C₁ I with
          | mk result₁ left₁ =>
              rw [h₁] at hCount
              cases result₁ with
              | halted I₁ =>
                  have hBound := ih h₁
                  have hSeq :
                      (match evalCount fuel C₂ I₁ with
                      | (result, leftSecond) =>
                          (result, min left₁ leftSecond)) =
                      ((.halted J : Result D Γ), left) := hCount
                  cases h₂ : evalCount fuel C₂ I₁ with
                  | mk result₂ left₂ =>
                      rw [h₂] at hSeq
                      rw [Prod.mk.injEq] at hSeq
                      omega
              | outOfFuel => simp at hCount
      | ite G C₁ C₂ =>
          change
            (if G.eval I then
              evalCount fuel C₁ I
            else
              evalCount fuel C₂ I) = (.halted J, left) at hCount
          by_cases hG : G.eval I
          · rw [if_pos hG] at hCount
            exact Nat.lt_succ_of_lt (ih hCount)
          · rw [if_neg hG] at hCount
            exact Nat.lt_succ_of_lt (ih hCount)
      | «while» G Body =>
          change
            (if G.eval I then
              match evalCount fuel Body I with
              | (.halted I₁, leftBody) =>
                  match evalCount fuel (.while G Body) I₁ with
                  | (result, leftRest) =>
                      (result, min leftBody leftRest)
              | (.outOfFuel, leftBody) =>
                  (.outOfFuel, leftBody)
            else
              (.halted I, fuel)) = (.halted J, left) at hCount
          by_cases hG : G.eval I
          · rw [if_pos hG] at hCount
            cases hBody : evalCount fuel Body I with
            | mk resultBody leftBody =>
                rw [hBody] at hCount
                cases resultBody with
                | halted I₁ =>
                    have hBound := ih hBody
                    have hLoop :
                        (match evalCount fuel (.while G Body) I₁ with
                        | (result, leftRest) =>
                            (result, min leftBody leftRest)) =
                        ((.halted J : Result D Γ), left) := hCount
                    cases hRest :
                        evalCount fuel (.while G Body) I₁ with
                    | mk resultRest leftRest =>
                        rw [hRest] at hLoop
                        rw [Prod.mk.injEq] at hLoop
                        omega
                | outOfFuel => simp at hCount
          · rw [if_neg hG] at hCount
            rw [Prod.mk.injEq] at hCount
            omega

/-
  The fuel a halting run leaves over is enough to spare: the
  run halts the same way under the difference alone.
-/
theorem eval_sub_snd_of_halted
    {fuel : Nat}
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    {left : Nat}
    (hCount : evalCount fuel C I = (.halted J, left)) :
    eval (fuel - left) C I = .halted J := by
  induction fuel generalizing C I J left with
  | zero =>
      change ((Result.outOfFuel : Result D Γ), 0) =
        (.halted J, left) at hCount
      simp at hCount
  | succ fuel ih =>
      cases C with
      | skip =>
          change ((Result.halted I : Result D Γ), fuel) =
            (.halted J, left) at hCount
          rw [Prod.mk.injEq] at hCount
          obtain ⟨hResult, hLeft⟩ := hCount
          cases hResult
          cases hLeft
          have hArith : fuel + 1 - fuel = 1 := by omega
          rw [hArith]
          rfl
      | assign X e =>
          change
            ((Result.halted (Instance.update I X (e.eval I)) :
              Result D Γ), fuel) = (.halted J, left) at hCount
          rw [Prod.mk.injEq] at hCount
          obtain ⟨hResult, hLeft⟩ := hCount
          cases hResult
          cases hLeft
          have hArith : fuel + 1 - fuel = 1 := by omega
          rw [hArith]
          rfl
      | seq C₁ C₂ =>
          change
            (match evalCount fuel C₁ I with
            | (.halted I₁, leftFirst) =>
                match evalCount fuel C₂ I₁ with
                | (result, leftSecond) =>
                    (result, min leftFirst leftSecond)
            | (.outOfFuel, leftFirst) =>
                (.outOfFuel, leftFirst)) =
            (.halted J, left) at hCount
          cases h₁ : evalCount fuel C₁ I with
          | mk result₁ left₁ =>
              rw [h₁] at hCount
              cases result₁ with
              | halted I₁ =>
                  have hBound₁ := evalCount_snd_lt_of_halted h₁
                  have hSeq :
                      (match evalCount fuel C₂ I₁ with
                      | (result, leftSecond) =>
                          (result, min left₁ leftSecond)) =
                      ((.halted J : Result D Γ), left) := hCount
                  cases h₂ : evalCount fuel C₂ I₁ with
                  | mk result₂ left₂ =>
                      rw [h₂] at hSeq
                      rw [Prod.mk.injEq] at hSeq
                      obtain ⟨hResult, hLeft⟩ := hSeq
                      cases hResult
                      cases hLeft
                      have hFirst := ih h₁
                      have hSecond := ih h₂
                      have hArith :
                          fuel + 1 - min left₁ left₂ =
                            (fuel - min left₁ left₂) + 1 := by
                        omega
                      rw [hArith]
                      change
                        (match eval (fuel - min left₁ left₂) C₁ I with
                        | .halted K =>
                            eval (fuel - min left₁ left₂) C₂ K
                        | .outOfFuel => .outOfFuel) = .halted J
                      rw [eval_halted_mono hFirst (by omega)]
                      exact eval_halted_mono hSecond (by omega)
              | outOfFuel => simp at hCount
      | ite G C₁ C₂ =>
          change
            (if G.eval I then
              evalCount fuel C₁ I
            else
              evalCount fuel C₂ I) = (.halted J, left) at hCount
          by_cases hG : G.eval I
          · rw [if_pos hG] at hCount
            have hBound := evalCount_snd_lt_of_halted hCount
            have hArith :
                fuel + 1 - left = (fuel - left) + 1 := by omega
            rw [hArith]
            change
              (if G.eval I then
                eval (fuel - left) C₁ I
              else
                eval (fuel - left) C₂ I) = .halted J
            simp only [hG, if_true]
            exact ih hCount
          · rw [if_neg hG] at hCount
            have hBound := evalCount_snd_lt_of_halted hCount
            have hArith :
                fuel + 1 - left = (fuel - left) + 1 := by omega
            rw [hArith]
            change
              (if G.eval I then
                eval (fuel - left) C₁ I
              else
                eval (fuel - left) C₂ I) = .halted J
            simp only [hG, if_false]
            exact ih hCount
      | «while» G Body =>
          change
            (if G.eval I then
              match evalCount fuel Body I with
              | (.halted I₁, leftBody) =>
                  match evalCount fuel (.while G Body) I₁ with
                  | (result, leftRest) =>
                      (result, min leftBody leftRest)
              | (.outOfFuel, leftBody) =>
                  (.outOfFuel, leftBody)
            else
              (.halted I, fuel)) = (.halted J, left) at hCount
          by_cases hG : G.eval I
          · rw [if_pos hG] at hCount
            cases hBody : evalCount fuel Body I with
            | mk resultBody leftBody =>
                rw [hBody] at hCount
                cases resultBody with
                | halted I₁ =>
                    have hBound :=
                      evalCount_snd_lt_of_halted hBody
                    have hLoop :
                        (match evalCount fuel (.while G Body) I₁ with
                        | (result, leftRest) =>
                            (result, min leftBody leftRest)) =
                        ((.halted J : Result D Γ), left) := hCount
                    cases hRest :
                        evalCount fuel (.while G Body) I₁ with
                    | mk resultRest leftRest =>
                        rw [hRest] at hLoop
                        rw [Prod.mk.injEq] at hLoop
                        obtain ⟨hResult, hLeft⟩ := hLoop
                        cases hResult
                        cases hLeft
                        have hFirst := ih hBody
                        have hSecond := ih hRest
                        have hArith :
                            fuel + 1 - min leftBody leftRest =
                              (fuel - min leftBody leftRest) + 1 := by
                          omega
                        rw [hArith]
                        change
                          (if G.eval I then
                            match eval
                                (fuel - min leftBody leftRest)
                                Body I with
                            | .halted K =>
                                eval
                                  (fuel - min leftBody leftRest)
                                  (.while G Body) K
                            | .outOfFuel => .outOfFuel
                          else
                            .halted I) = .halted J
                        simp only [hG, if_true]
                        rw [eval_halted_mono hFirst (by omega)]
                        exact eval_halted_mono hSecond (by omega)
                | outOfFuel => simp at hCount
          · rw [if_neg hG] at hCount
            rw [Prod.mk.injEq] at hCount
            obtain ⟨hResult, hLeft⟩ := hCount
            cases hResult
            cases hLeft
            have hArith : fuel + 1 - fuel = 1 := by omega
            rw [hArith]
            change
              (if G.eval I then
                match eval 0 Body I with
                | .halted K => eval 0 (.while G Body) K
                | .outOfFuel => .outOfFuel
              else
                .halted I) = .halted I
            simp only [hG, if_false]

/-
  The measured consumption is a sufficient bound: whenever
  the run under the given bound halts, the run under the
  fuel it consumed halts identically. A caller may therefore
  freeze `evalConsumed` in place of the bound it was given.
-/
theorem eval_evalConsumed
    {fuel : Nat}
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    (hEval : eval fuel C I = .halted J) :
    eval (evalConsumed fuel C I) C I = eval fuel C I := by
  have hFst := evalCount_fst fuel C I
  cases hCount : evalCount fuel C I with
  | mk result left =>
      rw [hCount] at hFst
      have hResult : result = .halted J := hFst.trans hEval
      cases hResult
      have hConsumed : evalConsumed fuel C I = fuel - left := by
        rw [evalConsumed, hCount]
      rw [hConsumed, hEval]
      exact eval_sub_snd_of_halted hCount

end CmdFuel

end Whiel
