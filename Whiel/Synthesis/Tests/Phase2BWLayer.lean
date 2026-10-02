-- Author: Jesse Comer
import Whiel.Synthesis.Correspondence
import Whiel.Synthesis.WLayer.Enumeration

/-
  Focused checks for exact-WP layers and their compact
  index realization.
-/

namespace Whiel

namespace Synthesis

namespace Tests

namespace WLayerTests

def parameters :
    WLayer.Parameters where
  maxWIndex := 3

example :
    WLayer.Enumeration.indices parameters =
      [0, 1, 2, 3] := by
  decide

example :
    (WLayer.Enumeration.indices parameters).Nodup :=
  WLayer.Enumeration.indices_nodup parameters

example
    (index : Nat) :
    index ∈
        WLayer.Enumeration.indices parameters ↔
      index ≤ parameters.maxWIndex :=
  WLayer.Enumeration.mem_indices_iff
    parameters index

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

example
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    WLayer.Enumeration.clauses P parameters =
      [WLayer.formula P 0,
       WLayer.formula P 1,
       WLayer.formula P 2,
       WLayer.formula P 3] :=
  rfl

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (I : Instance D P.outSchema) :
    (WLayer.formula P 0).eval I ↔
      P.loopGuard.eval I ∨
        P.loopPost.eval I :=
  WLayer.formula_zero_eval_iff P I

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (n : Nat)
    (I : Instance D P.outSchema) :
    (WLayer.formula P (n + 1)).eval I ↔
      ¬P.loopGuard.eval I ∨
        Hoare.wp P.loopBody
          (WLayer.formula P n).eval I :=
  WLayer.formula_succ_eval_iff P n I

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clause : Clause D P.outSchema) :
    clause ∈
        WLayer.Enumeration.clauses
          P parameters ↔
      clause ∈
        (WLayer.upTo
          P parameters.maxWIndex).clauses :=
  WLayer.Enumeration.mem_clauses_iff
    P parameters clause

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (n : Nat) :
    Assertion.Step P
      (WLayer.formula P (n + 1)).eval
      (WLayer.formula P n).eval :=
  WLayer.formula_succ_step P n

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema) :
    assertion.Term P ↔
      assertion.entails
        (WLayer.formula P 0).eval :=
  WLayer.term_iff_entails_zero
    P assertion

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema)
    (hSufficient :
      assertion.IsSufficientFor P)
    (n : Nat) :
    assertion.entails
      (WLayer.formula P n).eval :=
  WLayer.entails_formula_of_isSufficientFor
      P assertion hSufficient n

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (n : Nat) :
    (ClauseObligation.init
      P (WLayer.formula P n)).Valid ↔
        Assertion.Init P
          (WLayer.formula P n).eval :=
  ClauseObligation.init_valid_iff
    P (WLayer.formula P n)

end WLayerTests

end Tests

end Synthesis

end Whiel
