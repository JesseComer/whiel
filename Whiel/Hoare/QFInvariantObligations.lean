-- Author: Jesse Comer
import Whiel.AssertExpr.ToRelCalc
import Whiel.Hoare.Concrete

/-
  Solver-independent QF loop-obligation construction.

  This module owns the shared logical queries and their
  semantic contracts. Solver-specific modules may render
  them, while synthesis modules may specialize them.
-/

------------------------------------------------------------
-- Quantifier-Free Obligation Construction
------------------------------------------------------------

namespace Whiel

namespace QFInvariantObligation

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Convert a QF assertion into an assertion. -/
def ofQFAssert
    (φ : QFAssertExpr D Γ) :
    AssertExpr D Γ :=
  AssertExpr.ofQF φ

/- The assertion form of a QF formula has no bounds. -/
def ofQFNoBound
    (φ : QFAssertExpr D Γ) :
    (ofQFAssert (D := D) (Γ := Γ) φ).NoBoundSymbols :=
  AssertExpr.ofQF_noBound φ

/- Initialization obligation: `pre` implies `inv`. -/
def init
    (pre : AssertExpr D Γ)
    (preNoBound : pre.NoBoundSymbols)
    (inv : QFAssertExpr D Γ) :
    QFEntailment (D := D) Γ :=
  let invAssert := ofQFAssert inv
  let E : AssertExpr.Entailment D Γ :=
    { lhs := pre
      rhs := invAssert }
  AssertExpr.entailmentToQFEntailmentOfNoBound
    E preNoBound (ofQFNoBound inv)

/-
  Generic step obligation:
  `lhs ∧ guard` implies `wp(body, rhs)`.
-/
def step
    (lhs rhs : QFAssertExpr D Γ)
    (G : Guard D Γ)
    (Body : Cmd D Γ)
    (hBody : Body.LoopFree) :
    QFEntailment (D := D) Γ :=
  let lhsAssert := ofQFAssert lhs
  let rhsAssert :=
    AssertExpr.wpLoopFree Body hBody (ofQFAssert rhs)
  let E : AssertExpr.Entailment D Γ :=
    { lhs := AssertExpr.andGuard lhsAssert G
      rhs := rhsAssert }
  AssertExpr.entailmentToQFEntailmentOfNoBound
    E
    (AssertExpr.andGuard_noBoundSymbols
      lhsAssert G (ofQFNoBound lhs))
    (AssertExpr.wpLoopFree_noBoundSymbols
      Body hBody (ofQFAssert rhs) (ofQFNoBound rhs))

/- Termination obligation for one invariant. -/
def term
    (inv : QFAssertExpr D Γ)
    (post : AssertExpr D Γ)
    (postNoBound : post.NoBoundSymbols)
    (G : Guard D Γ) :
    QFEntailment (D := D) Γ :=
  let invAssert := ofQFAssert inv
  let E : AssertExpr.Entailment D Γ :=
    { lhs := AssertExpr.andNotGuard invAssert G
      rhs := post }
  AssertExpr.entailmentToQFEntailmentOfNoBound
    E
    (AssertExpr.andNotGuard_noBoundSymbols
      invAssert G (ofQFNoBound inv))
    postNoBound

end QFInvariantObligation

end Whiel

------------------------------------------------------------
-- Conversion Correctness
------------------------------------------------------------

namespace Whiel

namespace QFInvariantObligation

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- No-bound conversion preserves entailment validity. -/
theorem conversion_valid_iff
    (E : AssertExpr.Entailment D Γ)
    (hLhs : E.lhs.NoBoundSymbols)
    (hRhs : E.rhs.NoBoundSymbols) :
    (AssertExpr.entailmentToQFEntailmentOfNoBound
      E hLhs hRhs).Valid ↔ E.Valid := by
  constructor
  · exact
      AssertExpr.entailmentToQFEntailmentOfNoBound_sound
        E hLhs hRhs
  · intro hValid I hAxioms
    apply
      (AssertExpr.toQFOfNoBound_eval_iff
        E.rhs hRhs I).mpr
    apply hValid I
    apply
      (AssertExpr.toQFOfNoBound_eval_iff
        E.lhs hLhs I).mp
    exact hAxioms
      (E.lhs.toQFOfNoBound hLhs) (by
        change
          E.lhs.toQFOfNoBound hLhs ∈
            [E.lhs.toQFOfNoBound hLhs]
        simp)

end QFInvariantObligation

end Whiel

------------------------------------------------------------
-- Semantic Contracts
------------------------------------------------------------

namespace Whiel

namespace QFInvariantObligation

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Init validity is semantic initialization. -/
theorem init_valid_iff
    (pre : AssertExpr D Γ)
    (preNoBound : pre.NoBoundSymbols)
    (inv : QFAssertExpr D Γ) :
    (init pre preNoBound inv).Valid ↔
      Assertion.entails pre.eval inv.eval := by
  unfold init
  rw [conversion_valid_iff]
  constructor
  · intro hValid I hPre
    exact
      (AssertExpr.ofQF_eval_iff inv I).mp
        (hValid I hPre)
  · intro hValid I hPre
    exact
      (AssertExpr.ofQF_eval_iff inv I).mpr
        (hValid I hPre)

/- Step validity is semantic target maintenance. -/
theorem step_valid_iff
    (lhs rhs : QFAssertExpr D Γ)
    (G : Guard D Γ)
    (Body : Cmd D Γ)
    (hBody : Body.LoopFree) :
    (step lhs rhs G Body hBody).Valid ↔
      Assertion.entails
        (Assertion.andGuard lhs.eval G)
        (Hoare.wp Body rhs.eval) := by
  unfold step
  rw [conversion_valid_iff]
  constructor
  · intro hValid I hActive
    have hLhs :
        (AssertExpr.andGuard
          (ofQFAssert lhs) G).eval I := by
      apply
        (AssertExpr.andGuard_eval_iff
          (ofQFAssert lhs) G I).mpr
      exact
        ⟨(AssertExpr.ofQF_eval_iff lhs I).mpr
            hActive.1,
          hActive.2⟩
    have hWp :=
      (AssertExpr.wpLoopFree_eval_iff
        Body hBody (ofQFAssert rhs) I).mp
        (hValid I hLhs)
    exact
      (Hoare.wp_congr Body
        (fun J => AssertExpr.ofQF_eval_iff rhs J) I).mp
        hWp
  · intro hValid I hActive
    apply
      (AssertExpr.wpLoopFree_eval_iff
        Body hBody (ofQFAssert rhs) I).mpr
    apply
      (Hoare.wp_congr Body
        (fun J => AssertExpr.ofQF_eval_iff rhs J) I).mpr
    apply hValid I
    have hAnd :=
      (AssertExpr.andGuard_eval_iff
        (ofQFAssert lhs) G I).mp hActive
    exact
      ⟨(AssertExpr.ofQF_eval_iff lhs I).mp hAnd.1,
        hAnd.2⟩

/- Term validity is semantic postcondition establishment. -/
theorem term_valid_iff
    (inv : QFAssertExpr D Γ)
    (post : AssertExpr D Γ)
    (postNoBound : post.NoBoundSymbols)
    (G : Guard D Γ) :
    (term inv post postNoBound G).Valid ↔
      Assertion.entails
        (Assertion.andNotGuard inv.eval G)
        post.eval := by
  unfold term
  rw [conversion_valid_iff]
  constructor
  · intro hValid I hExit
    apply hValid I
    apply
      (AssertExpr.andNotGuard_eval_iff
        (ofQFAssert inv) G I).mpr
    exact
      ⟨(AssertExpr.ofQF_eval_iff inv I).mpr hExit.1,
        hExit.2⟩
  · intro hValid I hExit
    apply hValid I
    have hAnd :=
      (AssertExpr.andNotGuard_eval_iff
        (ofQFAssert inv) G I).mp hExit
    exact
      ⟨(AssertExpr.ofQF_eval_iff inv I).mp hAnd.1,
        hAnd.2⟩

end QFInvariantObligation

end Whiel
