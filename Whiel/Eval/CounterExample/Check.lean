-- Author: Jesse Comer
import Whiel.Eval.CounterExample.Fast
import Whiel.Hoare.Concrete
import Whiel.Hoare.CounterExample

/-
  Runtime checking and native certification for Hoare
  counterexamples through `CexFast`.

  `Hoare.CounterExample.runtimeCheck` is the compiled
  diagnostic checker. `Hoare.CounterExample.certify` is the
  production certificate-facing theorem.
-/

------------------------------------------------------------
-- Runtime Counterexample Checking
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace CounterExample

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Fast diagnostic check for one proposed counterexample. -/
def runtimeCheck
    (fuel : Nat)
    (pre : AssertExpr D Γ)
    (C : Cmd D Γ)
    (post : AssertExpr D Γ)
    (I J : Instance D Γ) : Bool :=
  decide
    (CexFast.checkCounterexample fuel pre C post I =
      .counterexample J)

/- Runtime truth establishes a Hoare counterexample. -/
theorem runtimeCheck_sound
    {fuel : Nat}
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    (hCheck : runtimeCheck fuel pre C post I J = true) :
    Hoare.counterExample pre C post I J := by
  have hResult :
      CexFast.checkCounterexample fuel pre C post I =
        .counterexample J := by
    exact of_decide_eq_true hCheck
  exact CexFast.counterexample_sound hResult

end CounterExample

end Hoare

end Whiel

------------------------------------------------------------
-- Native Counterexample Certification
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace CounterExample

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/-
  Certify with the compiled checker. `native_decide` expands
  the trust boundary to Lean's compiler and native runtime.
-/
set_option linter.style.nativeDecide false in
theorem certify
    (fuel : Nat)
    {pre post : AssertExpr D Γ}
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    (_hCheck :
      runtimeCheck fuel pre C post I J = true :=
        by native_decide) :
    Hoare.counterExample pre C post I J :=
  runtimeCheck_sound _hCheck

end CounterExample

end Hoare

end Whiel
