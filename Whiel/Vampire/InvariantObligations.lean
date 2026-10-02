-- Author: Jesse Comer
import Whiel.Hoare.QFInvariantObligations
import Whiel.Vampire.Manifest
import Whiel.Vampire.QFEntailment
import Whiel.Vampire.TPTP

/-
  Generic Vampire jobs for loop-invariant obligations.

  Key definitions:
    * `Whiel.Vampire.closedJobOfQF`
    * `Whiel.Vampire.initJob`
    * `Whiel.Vampire.stepJob`
    * `Whiel.Vampire.termJob`

  This file builds named Vampire jobs from already-parsed
  QF assertions. It does not call Vampire.
-/

------------------------------------------------------------
-- QF Verification Conditions
------------------------------------------------------------

namespace Whiel

namespace Vampire

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Compatibility name for the shared QF assertion view. -/
def ofQFAssert
    (φ : QFAssertExpr D Γ) :
    AssertExpr D Γ :=
  QFInvariantObligation.ofQFAssert φ

/- Compatibility name for the shared no-bound proof. -/
def ofQFNoBound
    (φ : QFAssertExpr D Γ) :
    (ofQFAssert (D := D) (Γ := Γ) φ).NoBoundSymbols :=
  QFInvariantObligation.ofQFNoBound φ

/- Compatibility name for shared initialization. -/
def initQF
    (pre : AssertExpr D Γ)
    (preNoBound : pre.NoBoundSymbols)
    (inv : QFAssertExpr D Γ) :
    QFEntailment (D := D) Γ :=
  QFInvariantObligation.init pre preNoBound inv

/- Compatibility name for shared step construction. -/
def stepQF
    (lhs rhs : QFAssertExpr D Γ)
    (G : Guard D Γ)
    (Body : Cmd D Γ)
    (hBody : Body.LoopFree) :
    QFEntailment (D := D) Γ :=
  QFInvariantObligation.step lhs rhs G Body hBody

/- Compatibility name for shared termination. -/
def termQF
    (inv : QFAssertExpr D Γ)
    (post : AssertExpr D Γ)
    (postNoBound : post.NoBoundSymbols)
    (G : Guard D Γ) :
    QFEntailment (D := D) Γ :=
  QFInvariantObligation.term inv post postNoBound G

end Vampire
end Whiel

------------------------------------------------------------
-- Job Construction
------------------------------------------------------------

namespace Whiel

namespace Vampire

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Render one QF entailment as a named Vampire job. -/
def jobOfQF
    [SolverName A] [SolverName D]
    [LinearOrder A] [LinearOrder D]
    (id : String)
    (when? : Option Condition)
    (E : QFEntailment (D := D) Γ) :
    Job :=
  let R := E.toRelCalcEntailment
  { id := id
    when? := when?
    axioms := TPTP.relCalcAxiomBlock R
    conjecture := TPTP.relCalcConjectureDecl R }

/-
  The environment `jobOfQF` renders one obligation under.

  The one-shot path's relation carrier proves nothing about
  its names, so the entries below that can refuse do so by
  deciding `NameEnv.wellFormed` on this environment and on
  `closedNameEnvOfQF`.
-/
def jobNameEnvOfQF
    [SolverName A] [SolverName D]
    [LinearOrder A] [LinearOrder D]
    (E : QFEntailment (D := D) Γ) :
    TPTP.NameEnv A D :=
  TPTP.relCalcNameEnv E.toRelCalcEntailment

/- Closed FOL problem used for proof reconstruction. -/
def closedEntailmentOfQF
    [LinearOrder A] [LinearOrder D]
    (E : QFEntailment (D := D) Γ) :
    FOL.SentenceEntailment
      (Γ.toFOLSignature
        E.toRelCalcEntailment.constants) :=
  E.toRelCalcEntailment.toFOLWithSupportAxioms

/- Shared symbol environment for a closed QF problem. -/
def closedNameEnvOfQF
    [SolverName A] [SolverName D]
    [LinearOrder A] [LinearOrder D]
    (E : QFEntailment (D := D) Γ) :
    TPTP.NameEnv A D :=
  TPTP.NameEnv.ofEntailment (closedEntailmentOfQF E)

/- Render a QF entailment as one closed conjecture. -/
def closedJobOfQF
    [SolverName A] [SolverName D]
    [LinearOrder A] [LinearOrder D]
    (id : String)
    (when? : Option Condition)
    (E : QFEntailment (D := D) Γ) :
    Job :=
  let F := closedEntailmentOfQF E
  let env := closedNameEnvOfQF E
  { id := id
    when? := when?
    axioms := env.symbolMapComment
    conjecture :=
      TPTP.namedConjectureWithEnv env
        "conjecture" F.toImplication }

/- Build an initialization job. -/
def initJob
    [SolverName A] [SolverName D]
    [LinearOrder A] [LinearOrder D]
    (id : String)
    (when? : Option Condition)
    (pre : AssertExpr D Γ)
    (preNoBound : pre.NoBoundSymbols)
    (inv : QFAssertExpr D Γ) :
    Job :=
  jobOfQF id when? (initQF pre preNoBound inv)

/- Build a generic loop-step job. -/
def stepJob
    [SolverName A] [SolverName D]
    [LinearOrder A] [LinearOrder D]
    (id : String)
    (when? : Option Condition)
    (lhs rhs : QFAssertExpr D Γ)
    (G : Guard D Γ)
    (Body : Cmd D Γ)
    (hBody : Body.LoopFree) :
    Job :=
  jobOfQF id when? (stepQF lhs rhs G Body hBody)

/- Build a termination/postcondition job. -/
def termJob
    [SolverName A] [SolverName D]
    [LinearOrder A] [LinearOrder D]
    (id : String)
    (when? : Option Condition)
    (inv : QFAssertExpr D Γ)
    (post : AssertExpr D Γ)
    (postNoBound : post.NoBoundSymbols)
    (G : Guard D Γ) :
    Job :=
  jobOfQF id when? (termQF inv post postNoBound G)

end Vampire
end Whiel
