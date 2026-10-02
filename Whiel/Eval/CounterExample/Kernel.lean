-- Author: Jesse Comer
import Whiel.Eval.Cmd.Fuel
import Whiel.Eval.Cmd.FuelCount
import Whiel.Hoare.Concrete
import Whiel.Hoare.CounterExample

/-
  Kernel-only certification of Hoare invalidity.

  Key definitions:
    * `Hoare.CounterExample.kernelRefutes`
    * `Hoare.CounterExample.certifyKernel`

  Invalidity follows by:
    * `Hoare.CounterExample.invalid_of_kernelRefutes`

  A caller that measures the fuel one refuting run actually
  consumes may freeze that smaller number instead of the
  bound it was given:
    * `Hoare.CounterExample.kernelRefutes_evalConsumed`

  `kernelRefutes` is built from structural pieces only
  (fuelled reference evaluation, decidable guard
  evaluation), so `decide +kernel` reduces it entirely
  inside the kernel: certificates carry no native trust.
  The final instance is computed during reduction and
  never appears in the certificate.
-/

------------------------------------------------------------
-- Kernel Counterexample Checking
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace CounterExample

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  One Bool: pre and post are quantifier free, pre holds
  at the input, the fuelled run halts, and post fails in
  the halt state.
-/
def kernelRefutes
    (fuel : Nat)
    (pre : AssertExpr D Γ)
    (C : Cmd D Γ)
    (post : AssertExpr D Γ)
    (I : Instance D Γ) : Bool :=
  if hPre : pre.NoBoundSymbols then
    if hPost : post.NoBoundSymbols then
      Bool.and
        (decide ((pre.toQF hPre).eval I))
        (match CmdFuel.eval fuel C I with
         | CmdFuel.Result.halted J =>
             Bool.not
               (decide ((post.toQF hPost).eval J))
         | CmdFuel.Result.outOfFuel => Bool.false)
    else
      Bool.false
  else
    Bool.false

/- A true kernel check refutes the Hoare triple. -/
theorem invalid_of_kernelRefutes
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {I : Instance D Γ}
    (hCheck :
      kernelRefutes fuel pre C post I = Bool.true) :
    ¬ HoareValid pre C post := by
  intro hValid
  by_cases hPre : pre.NoBoundSymbols
  case neg =>
    rw [kernelRefutes, dif_neg hPre] at hCheck
    exact Bool.noConfusion hCheck
  case pos =>
  by_cases hPost : post.NoBoundSymbols
  case neg =>
    rw [kernelRefutes, dif_pos hPre, dif_neg hPost]
      at hCheck
    exact Bool.noConfusion hCheck
  case pos =>
  rw [kernelRefutes, dif_pos hPre, dif_pos hPost]
    at hCheck
  cases hRun : CmdFuel.eval fuel C I with
  | outOfFuel =>
      rw [hRun] at hCheck
      simp at hCheck
  | halted J =>
      rw [hRun] at hCheck
      simp only [Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq, decide_eq_false_iff_not]
        at hCheck
      obtain ⟨hPreEval, hNotPost⟩ := hCheck
      have hStep : Cmd.BigStep C I J :=
        CmdFuel.eval_sound hRun
      have hPreSem : pre.eval I :=
        (AssertExpr.toQF_eval_iff pre hPre I).mp
          hPreEval
      have hPostSem : post.eval J :=
        hValid I J hPreSem hStep
      exact hNotPost
        ((AssertExpr.toQF_eval_iff post hPost J).mpr
          hPostSem)

/-
  The measured consumption certifies exactly as well as the
  bound it was measured under: a run that refutes under
  `fuel` refutes under the fuel it actually consumed. This
  is what lets a caller freeze `CmdFuel.evalConsumed` in
  place of the host's bound without re-deciding anything.
-/
theorem kernelRefutes_evalConsumed
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {I : Instance D Γ}
    (hCheck :
      kernelRefutes fuel pre C post I = Bool.true) :
    kernelRefutes (CmdFuel.evalConsumed fuel C I) pre C post
        I = Bool.true := by
  by_cases hPre : pre.NoBoundSymbols
  case neg =>
    rw [kernelRefutes, dif_neg hPre] at hCheck
    exact Bool.noConfusion hCheck
  case pos =>
  by_cases hPost : post.NoBoundSymbols
  case neg =>
    rw [kernelRefutes, dif_pos hPre, dif_neg hPost]
      at hCheck
    exact Bool.noConfusion hCheck
  case pos =>
  rw [kernelRefutes, dif_pos hPre, dif_pos hPost] at hCheck
  rw [kernelRefutes, dif_pos hPre, dif_pos hPost]
  cases hRun : CmdFuel.eval fuel C I with
  | outOfFuel =>
      rw [hRun] at hCheck
      simp at hCheck
  | halted J =>
      rw [hRun] at hCheck
      rw [CmdFuel.eval_evalConsumed hRun, hRun]
      exact hCheck

/-
  Certify with the kernel checker. The default proof
  reduces entirely inside the kernel; the trusted base is
  the kernel and the development's standard axioms only.
-/
theorem certifyKernel
    (fuel : Nat)
    (I : Instance D Γ)
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    (_hCheck :
      kernelRefutes fuel pre C post I = Bool.true :=
        by decide +kernel) :
    ¬ HoareValid pre C post :=
  invalid_of_kernelRefutes _hCheck

end CounterExample

end Hoare

end Whiel
