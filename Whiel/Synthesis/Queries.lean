-- Author: Jesse Comer
import Whiel.Hoare.QFInvariantObligations
import Whiel.Synthesis.Spec

/-
  QF obligation queries for class-agnostic clauses.

  Lists are the readable ordered representation accepted by
  these constructors. Their conjunction is independent of a
  program; the program is needed only to build an
  invariant obligation.
-/

------------------------------------------------------------
-- Clause Obligation Construction
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace ClauseObligation

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- Conjoin an ordered list of clauses. -/
def materialize
    {Ω : UnnamedSchema A}
    (clauses : List (Clause D Ω)) :
    QFAssertExpr D Ω :=
  QFAssertExpr.andList clauses

/- Initialization of one target clause. -/
def init
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (target : Clause D P.outSchema) :
    QFEntailment (D := D) P.outSchema :=
  QFInvariantObligation.init
    P.loopPre P.loopPre_noBound target

/- Initialization of a whole candidate list. -/
def initCandidate
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (candidate : List (Clause D P.outSchema)) :
    QFEntailment (D := D) P.outSchema :=
  QFInvariantObligation.init
    P.loopPre P.loopPre_noBound
    (materialize candidate)

/- One target step under a complete candidate list. -/
def step
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (candidate : List (Clause D P.outSchema))
    (target : Clause D P.outSchema) :
    QFEntailment (D := D) P.outSchema :=
  QFInvariantObligation.step
    (materialize candidate) target
    P.loopGuard P.loopBody P.loopBody_loopFree

/- Self-maintenance of a whole candidate list. -/
def maintCandidate
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (candidate : List (Clause D P.outSchema)) :
    QFEntailment (D := D) P.outSchema :=
  QFInvariantObligation.step
    (materialize candidate) (materialize candidate)
    P.loopGuard P.loopBody P.loopBody_loopFree

/- Termination of a whole candidate list. -/
def termCandidate
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (candidate : List (Clause D P.outSchema)) :
    QFEntailment (D := D) P.outSchema :=
  QFInvariantObligation.term
    (materialize candidate)
    P.loopPost P.loopPost_noBound P.loopGuard

end ClauseObligation

end Synthesis

end Whiel
