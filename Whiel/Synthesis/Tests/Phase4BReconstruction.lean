-- Author: Jesse Comer
import Whiel.Synthesis.WLayer.Spec

/-
  Focused checks for the Phase 4B same-input
  counterexample-reconstruction bridge.
-/

namespace Whiel

namespace Synthesis

namespace Tests

namespace Phase4BReconstructionTests

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

example
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (pre : AssertExpr D Γ)
    (J : Instance D Γ)
    (hNo : (pre.spLoopFree C hLoopFree).NoBoundSymbols)
    (hEval : (pre.spLoopFree C hLoopFree).eval J) :
    pre.eval J ∧ Cmd.BigStep C J J :=
  AssertExpr.spLoopFree_eval_imp_fixed
    C hLoopFree pre J hNo hEval

example
    {inputPre inputPost : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (J : Instance D P.outSchema)
    (hEval : P.loopPre.eval J) :
    inputPre.eval (Preprocess.project P.outExtends J) ∧
      Cmd.BigStep P.sourcePrefix J J :=
  P.loopPre_eval_imp_sourcePrefix_fixed J hEval

example
    {inputPre inputPost : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (n : Nat)
    (I : Instance D P.outSchema)
    (hLoopPre : P.loopPre.eval I)
    (hNotFormula : ¬(WLayer.formula P n).eval I) :
    ∃ J, Hoare.counterExample
      P.loopPre P.loopCmd P.loopPost I J :=
  WLayer.loop_counterExample_of_not_formula
    P n I hLoopPre hNotFormula

example
    {inputPre inputPost : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (n : Nat)
    (I : Instance D P.outSchema)
    (hLoopPre : P.loopPre.eval I)
    (hNotFormula : ¬(WLayer.formula P n).eval I) :
    ∃ J,
      Hoare.counterExample inputPre inputCmd inputPost
        (Preprocess.project P.outExtends I) J :=
  WLayer.counterExample_input_of_not_formula
    P n I hLoopPre hNotFormula

end Phase4BReconstructionTests

end Tests

end Synthesis

end Whiel
