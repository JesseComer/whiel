-- Author: Jesse Comer
import Whiel.Hoare.Preproc
import Whiel.Vampire.InvariantObligations

/-
  Certificate-facing invariant verification packages.

  A final candidate is recorded as one QF assertion. Algorithm-
  specific generated Lean may build that assertion however it
  wants before passing it to this package.

  The package also exposes stable empty-active-domain checks
  for its initialization, maintenance, and termination VCs.
-/

------------------------------------------------------------
-- Candidate Verification Packages
------------------------------------------------------------

namespace Whiel

namespace Vampire

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Candidate invariant data for one preprocessed input triple.
-/
structure CandidateVerification
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) where
  inputPre : AssertExpr D Γ
  inputCmd : Cmd D Γ
  inputPost : AssertExpr D Γ
  preproc : Hoare.Preproc inputPre inputCmd inputPost
  candidateQF : QFAssertExpr D preproc.outSchema

namespace CandidateVerification

/-
  Construct a verification package from a preprocessed input
  and an explicit final candidate invariant.
-/
def ofPreproc
    {inputPre : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    {inputPost : AssertExpr D Γ}
    (preproc : Hoare.Preproc inputPre inputCmd inputPost)
    (candidateQF : QFAssertExpr D preproc.outSchema) :
    CandidateVerification D Γ where
  inputPre := inputPre
  inputCmd := inputCmd
  inputPost := inputPost
  preproc := preproc
  candidateQF := candidateQF

/- Assertion view of the candidate invariant. -/
def candidateInv
    (P : CandidateVerification D Γ) :
    AssertExpr D P.preproc.outSchema :=
  ofQFAssert P.candidateQF

/- The derived candidate invariant has no bound symbols. -/
def candidateNoBound
    (P : CandidateVerification D Γ) :
    P.candidateInv.NoBoundSymbols :=
  ofQFNoBound P.candidateQF

end CandidateVerification

end Vampire

end Whiel

------------------------------------------------------------
-- Verification Conditions
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace CandidateVerification

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Assertion-level initialization VC. -/
def initVC
    (P : CandidateVerification D Γ) :
    AssertExpr.Entailment D P.preproc.outSchema :=
  loopOnlyInitVC P.preproc.loopPre P.candidateInv

/- Assertion-level maintenance VC. -/
def maintVC
    (P : CandidateVerification D Γ) :
    AssertExpr.Entailment D P.preproc.outSchema :=
  loopOnlyMaintVC
    P.candidateInv P.preproc.loopGuard
    P.preproc.loopBody P.preproc.loopBody_loopFree

/- Assertion-level termination VC. -/
def termVC
    (P : CandidateVerification D Γ) :
    AssertExpr.Entailment D P.preproc.outSchema :=
  loopOnlyTermVC
    P.candidateInv P.preproc.loopPost P.preproc.loopGuard

/- QF initialization entailment. -/
def initQF
    (P : CandidateVerification D Γ) :
    QFEntailment (D := D) P.preproc.outSchema :=
  AssertExpr.entailmentToQFEntailmentOfNoBound
    P.initVC P.preproc.loopPre_noBound P.candidateNoBound

/- QF maintenance entailment. -/
def maintQF
    (P : CandidateVerification D Γ) :
    QFEntailment (D := D) P.preproc.outSchema :=
  AssertExpr.entailmentToQFEntailmentOfNoBound
    P.maintVC
    (AssertExpr.andGuard_noBoundSymbols
      P.candidateInv P.preproc.loopGuard
      P.candidateNoBound)
    (AssertExpr.wpLoopFree_noBoundSymbols
      P.preproc.loopBody P.preproc.loopBody_loopFree
      P.candidateInv P.candidateNoBound)

/- QF termination entailment. -/
def termQF
    (P : CandidateVerification D Γ) :
    QFEntailment (D := D) P.preproc.outSchema :=
  AssertExpr.entailmentToQFEntailmentOfNoBound
    P.termVC
    (AssertExpr.andNotGuard_noBoundSymbols
      P.candidateInv P.preproc.loopGuard
      P.candidateNoBound)
    P.preproc.loopPost_noBound

/- The computed init entailment is valid. -/
def InitValid
    (P : CandidateVerification D Γ) : Prop :=
  P.initQF.Valid

/- The computed maintenance entailment is valid. -/
def MaintValid
    (P : CandidateVerification D Γ) : Prop :=
  P.maintQF.Valid

/- The computed termination entailment is valid. -/
def TermValid
    (P : CandidateVerification D Γ) : Prop :=
  P.termQF.Valid

end CandidateVerification

end Vampire

end Whiel

------------------------------------------------------------
-- Empty Active-Domain Conditions
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace CandidateVerification

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Initialization has no empty-active-domain counterexample.
-/
def InitNoEmpty
    (P : CandidateVerification D Γ) : Prop :=
  P.initQF.toRelCalcEntailment.NoEmptyCounterexample

/- Maintenance has no empty-active-domain counterexample. -/
def MaintNoEmpty
    (P : CandidateVerification D Γ) : Prop :=
  P.maintQF.toRelCalcEntailment.NoEmptyCounterexample

/- Termination has no empty-active-domain counterexample. -/
def TermNoEmpty
    (P : CandidateVerification D Γ) : Prop :=
  P.termQF.toRelCalcEntailment.NoEmptyCounterexample

/- Check the initialization empty-active-domain case. -/
def initEmptyCounterexample?
    (P : CandidateVerification D Γ)
    [Fintype P.preproc.outSchema.syms] : Bool :=
  P.initQF.emptyCounterexample?

/- Check the maintenance empty-active-domain case. -/
def maintEmptyCounterexample?
    (P : CandidateVerification D Γ)
    [Fintype P.preproc.outSchema.syms] : Bool :=
  P.maintQF.emptyCounterexample?

/- Check the termination empty-active-domain case. -/
def termEmptyCounterexample?
    (P : CandidateVerification D Γ)
    [Fintype P.preproc.outSchema.syms] : Bool :=
  P.termQF.emptyCounterexample?

/- Initialization checking exactly decides its condition. -/
theorem initEmptyCounterexample?_eq_false_iff
    (P : CandidateVerification D Γ)
    [Fintype P.preproc.outSchema.syms] :
    P.initEmptyCounterexample? = false ↔
      P.InitNoEmpty :=
  QFEntailment.emptyCounterexample?_eq_false_iff P.initQF

/- Maintenance checking exactly decides its condition. -/
theorem maintEmptyCounterexample?_eq_false_iff
    (P : CandidateVerification D Γ)
    [Fintype P.preproc.outSchema.syms] :
    P.maintEmptyCounterexample? = false ↔
      P.MaintNoEmpty :=
  QFEntailment.emptyCounterexample?_eq_false_iff P.maintQF

/- Termination checking exactly decides its condition. -/
theorem termEmptyCounterexample?_eq_false_iff
    (P : CandidateVerification D Γ)
    [Fintype P.preproc.outSchema.syms] :
    P.termEmptyCounterexample? = false ↔
      P.TermNoEmpty :=
  QFEntailment.emptyCounterexample?_eq_false_iff P.termQF

end CandidateVerification

end Vampire

end Whiel

------------------------------------------------------------
-- Soundness
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace CandidateVerification

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- QF init validity proves the assertion-level init VC. -/
theorem init_valid
    (P : CandidateVerification D Γ)
    (hInit : P.InitValid) :
    P.initVC.Valid := by
  exact
    AssertExpr.entailmentToQFEntailmentOfNoBound_sound
      P.initVC P.preproc.loopPre_noBound
      P.candidateNoBound hInit

/- QF maintenance validity proves the assertion-level VC. -/
theorem maint_valid
    (P : CandidateVerification D Γ)
    (hMaint : P.MaintValid) :
    P.maintVC.Valid := by
  exact
    AssertExpr.entailmentToQFEntailmentOfNoBound_sound
      P.maintVC
      (AssertExpr.andGuard_noBoundSymbols
        P.candidateInv P.preproc.loopGuard
        P.candidateNoBound)
      (AssertExpr.wpLoopFree_noBoundSymbols
        P.preproc.loopBody P.preproc.loopBody_loopFree
        P.candidateInv P.candidateNoBound)
      hMaint

/- QF termination validity proves the assertion-level VC. -/
theorem term_valid
    (P : CandidateVerification D Γ)
    (hTerm : P.TermValid) :
    P.termVC.Valid := by
  exact
    AssertExpr.entailmentToQFEntailmentOfNoBound_sound
      P.termVC
      (AssertExpr.andNotGuard_noBoundSymbols
        P.candidateInv P.preproc.loopGuard
        P.candidateNoBound)
      P.preproc.loopPost_noBound hTerm

/- Valid computed VCs prove the preprocessed loop triple. -/
theorem valid_loop_hoare
    (P : CandidateVerification D Γ)
    (hInit : P.InitValid)
    (hMaint : P.MaintValid)
    (hTerm : P.TermValid) :
    HoareValid
      P.preproc.loopPre P.preproc.loopCmd
      P.preproc.loopPost := by
  exact
    Hoare.hoareValid_loopOnly_of_invariantVCs
      P.preproc.loopPre P.preproc.loopPost
      P.candidateInv P.preproc.loopGuard
      P.preproc.loopBody P.preproc.loopBody_loopFree
      (P.init_valid hInit)
      (P.maint_valid hMaint)
      (P.term_valid hTerm)

/- Valid computed VCs prove the original input triple. -/
theorem valid_input_hoare
    (P : CandidateVerification D Γ)
    (hInit : P.InitValid)
    (hMaint : P.MaintValid)
    (hTerm : P.TermValid) :
    HoareValid P.inputPre P.inputCmd P.inputPost :=
  P.preproc.valid_input
    (P.valid_loop_hoare hInit hMaint hTerm)

end CandidateVerification

end Vampire

end Whiel

------------------------------------------------------------
-- Manifest Helpers
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace CandidateVerification

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The three final obligations, each with its job id. -/
def jobObligations
    (P : CandidateVerification D Γ) :
    List (String ×
      QFEntailment (D := D) P.preproc.outSchema) :=
  [ ("init_check",
      Vampire.initQF P.preproc.loopPre
        P.preproc.loopPre_noBound P.candidateQF),
    ("maint_check",
      Vampire.stepQF P.candidateQF P.candidateQF
        P.preproc.loopGuard P.preproc.loopBody
        P.preproc.loopBody_loopFree),
    ("term_check",
      Vampire.termQF P.candidateQF P.preproc.loopPost
        P.preproc.loopPost_noBound P.preproc.loopGuard) ]

/- Build the three final Vampire jobs from the candidate. -/
def buildJobs
    [SolverName A] [SolverName D]
    [LinearOrder A] [LinearOrder D]
    (P : CandidateVerification D Γ) :
    List Job :=
  P.jobObligations.map fun obligation =>
    jobOfQF obligation.1 none obligation.2

/- Write a batch manifest for the final candidate. -/
def writeManifest
    [SolverName A] [SolverName D]
    [LinearOrder A] [LinearOrder D]
    (P : CandidateVerification D Γ)
    (root : System.FilePath) :
    IO Unit := do
  -- Nothing is renamed apart, and the one-shot relation
  -- carrier proves nothing about its names, so every job's
  -- environment is decided before any problem text is
  -- written rather than after a solver has read it.
  for obligation in P.jobObligations do
    let env : TPTP.NameEnv A D :=
      jobNameEnvOfQF obligation.2
    unless env.wellFormed do
      throw (IO.userError
        ("job " ++ obligation.1 ++
          " has a malformed solver-name environment"))
  Vampire.writeManifest root P.buildJobs

end CandidateVerification

end Vampire

end Whiel
