-- Author: Jesse Comer
import Whiel.Synthesis.WLayer.Spec

/-
  Focused checks for the W(0)-membership sufficiency
  bridge.
-/

namespace Whiel

namespace Synthesis

namespace Tests

namespace Phase2CTests

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (hInductive :
      ({WLayer.formula P 0} :
        Candidate D P.outSchema).IsInductiveFor P) :
    ({WLayer.formula P 0} :
      Candidate D P.outSchema).IsSufficientFor P := by
  apply
    WLayer.isSufficientFor_of_isInductiveFor_of_mem_zero
      P _ hInductive
  simp

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : Candidate D P.outSchema)
    (hInductive : clauses.IsInductiveFor P)
    (hZero : WLayer.formula P 0 ∈ clauses) :
    HoareValid inputPre inputCmd inputPost :=
  P.valid_of_sufficient clauses.denote
    (WLayer.isSufficientFor_of_isInductiveFor_of_mem_zero
      P clauses hInductive hZero)

end Phase2CTests

end Tests

end Synthesis

end Whiel
