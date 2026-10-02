-- Author: Jesse Comer
import Whiel.Synthesis.WLayer.Spec

/-
  Focused checks for Phase 1A supporting results.
-/

------------------------------------------------------------
-- Weakest Preconditions and Finite Disjunction
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace Phase1ATests

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

example
    (C : Cmd D Γ)
    (posts : List (Assertion D Γ))
    (I : Instance D Γ)
    (hTerm :
      ∃ J : Instance D Γ, Cmd.BigStep C I J) :
    Hoare.wp C (Assertion.orList posts) I ↔
      ∃ post ∈ posts, Hoare.wp C post I :=
  Hoare.wp_orList_apply_iff C posts I hTerm

example
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (I : Instance D Γ) :
    ∃ J : Instance D Γ, Cmd.BigStep C I J :=
  Cmd.BigStep.exists_of_loopFree C hLoopFree I

example
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (posts : List (QFAssertExpr D Γ)) :
    (QFAssertExpr.wpLoopFree C hLoopFree
      (QFAssertExpr.orList posts)).equiv
        (QFAssertExpr.orList
          (posts.map
            (QFAssertExpr.wpLoopFree C hLoopFree))) :=
  QFAssertExpr.wpLoopFree_orList_equiv
    C hLoopFree posts

example
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (I : Instance D Γ) :
    ¬(QFAssertExpr.wpLoopFree C hLoopFree
      (QFAssertExpr.orList [])).eval I := by
  simpa using
    (QFAssertExpr.wpLoopFree_orList_eval_iff
      C hLoopFree [] I)

end Phase1ATests

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Contiguous W-Prefix Sufficiency
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace Phase1ATests

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (maxWIndex : Nat)
    (hInit :
      ∀ n ≤ maxWIndex,
        Assertion.Init P (WLayer.formula P n).eval)
    (hTopMaint :
      (WLayer.candidateUpTo P maxWIndex).denote.Step P
        (WLayer.formula P maxWIndex).eval) :
    (WLayer.candidateUpTo P
      maxWIndex).IsSufficientFor P :=
  WLayer.candidateUpTo_isSufficientFor
    P maxWIndex hInit hTopMaint

example
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    WLayer.candidateUpTo P 0 =
      {WLayer.formula P 0} := by
  ext clause
  simp [WLayer.candidateUpTo]

example
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (hInit :
      Assertion.Init P (WLayer.formula P 0).eval)
    (hMaint :
      Assertion.Maint P (WLayer.formula P 0).eval) :
    (WLayer.candidateUpTo P 0).IsSufficientFor P := by
  apply WLayer.candidateUpTo_isSufficientFor P 0
  · intro n hBound
    have hZero : n = 0 :=
      Nat.eq_zero_of_le_zero hBound
    subst n
    exact hInit
  · intro I hGuarded
    apply hMaint I
    exact
      ⟨hGuarded.1 _
          ((WLayer.mem_candidateUpTo_iff
            P 0 (WLayer.formula P 0)).2
              ⟨0, Nat.zero_le 0, rfl⟩),
        hGuarded.2⟩

end Phase1ATests

end Tests

end Synthesis

end Whiel
