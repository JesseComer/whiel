-- Author: Jesse Comer
import Databases.FOL.ShallowSemantics
import Whiel.Synthesis.FrameworkII.FixedAmbient.Assembly
import Whiel.Vampire.Job
import Whiel.Vampire.QFEntailment
import Whiel.Vampire.SolverName.Concrete
import Whiel.Vampire.TPTP

/-
  Typed certificate jobs for one frozen fixed-ambient
  Framework-II Core.

  Every job is one of the literal same-schema `2N+1`
  entailments. `closedEntailment`, `nameEnv`,
  `ShallowTarget`, and `tptp` are projections of that one
  Lean-owned QF entailment; the TPTP text is output only.

  `CertificateJob.valid_of_fullProof` carries a proof of the
  exact ordinary shallow target back to QF validity through
  the existing FOL and empty-domain soundness theorems, and
  the clause-proof spine feeds every job into the existing
  fixed-ambient assembly theorem.

  A certificate names its Core as a level list: entry `k`
  lists the formulas at level `k`. The certificate-facing
  jobs, proof spine, and entry point take that level list
  and build the leveled family through `ofLevels`.
-/

------------------------------------------------------------
-- Certificate Jobs
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient

open Concrete

/- The role and retained family row of one exact VC. -/
inductive CertificateJobRole
    (D : Type) [Domain D]
    (Gamma : UnnamedSchema WhielNames) where
| initialization (clause : LeveledClause D Gamma)
| maintenance (clause : LeveledClause D Gamma)
| termination

/- One exact QF job over the literal ambient schema. -/
structure CertificateJob
    (D : Type) [Domain D]
    (Gamma : UnnamedSchema WhielNames) where
  id : String
  role : CertificateJobRole D Gamma
  entailment : QFEntailment (D := D) Gamma

namespace CertificateJobRole

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}

/- Stable machine-facing role name. -/
def name :
    CertificateJobRole D Gamma -> String
| .initialization _ => "initialization"
| .maintenance _ => "maintenance"
| .termination => "termination"

end CertificateJobRole

namespace CertificateJob

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}

/- Package one exact QF entailment. -/
def ofEntailment
    (id : String)
    (role : CertificateJobRole D Gamma)
    (entailment : QFEntailment (D := D) Gamma) :
    CertificateJob D Gamma :=
  { id, role, entailment }

/- Exact closed FOL entailment from the QF VC. -/
def closedEntailment
    [LinearOrder D]
    (job : CertificateJob D Gamma) :
    FOL.SentenceEntailment
      (Gamma.toFOLSignature
        job.entailment.toRelCalcEntailment.constants) :=
  job.entailment.toRelCalcEntailment
    |>.toFOLWithSupportAxioms

/- Exact symbol telescope for the closed implication. -/
def nameEnv
    [Vampire.SolverName D]
    [LinearOrder D]
    (job : CertificateJob D Gamma) :
    Vampire.TPTP.NameEnv WhielNames D :=
  Vampire.TPTP.NameEnv.ofEntailment
    job.closedEntailment

/- Ordinary closed proposition expected from leancheck. -/
abbrev ShallowTarget
    [LinearOrder D]
    (job : CertificateJob D Gamma) : Prop :=
  job.closedEntailment.ImplicationShallowValid

/-
  Opaque solver job for the one closed implication. Its only
  axiom text is the exact symbol map used to read the proof.
-/
def vampireJob
    [Vampire.SolverName D]
    [LinearOrder D]
    (job : CertificateJob D Gamma) :
    Vampire.Job :=
  let env := job.nameEnv
  let closed := job.closedEntailment
  { id := job.id
    axioms := env.symbolMapComment
    conjecture :=
      Vampire.TPTP.namedConjectureWithEnv env
        "conjecture" closed.toImplication }

/- Exact bytes written to the Vampire problem file. -/
def tptp
    [Vampire.SolverName D]
    [LinearOrder D]
    (job : CertificateJob D Gamma) : String :=
  let rendered := job.vampireJob
  rendered.axioms ++ "\n" ++ rendered.conjecture ++ "\n"

/-
  Exact closed entailment whose support axioms range over
  Lean-owned explicit symbol lists instead of canonical
  sorts, so a certificate elaborates it without evaluating
  `Finset.sort`.
-/
def closedEntailmentOfLists
    [LinearOrder D]
    (job : CertificateJob D Gamma)
    (constants :
      List job.entailment.toRelCalcEntailment.constants)
    (relations : List Gamma.syms) :
    FOL.SentenceEntailment
      (Gamma.toFOLSignature
        job.entailment.toRelCalcEntailment.constants) where
  axioms :=
    RelCalc.ToFOL.supportAxiomsOfLists Gamma
        job.entailment.toRelCalcEntailment.constants
        constants relations ++
      job.entailment.toRelCalcEntailment.toFOLSourceAxioms
  conjecture :=
    job.entailment.toRelCalcEntailment.toFOLSourceConjecture

/- Sortedness equalities identify the two closed forms. -/
theorem closedEntailment_eq_ofLists
    [LinearOrder D]
    (job : CertificateJob D Gamma)
    {constants :
      List job.entailment.toRelCalcEntailment.constants}
    {relations : List Gamma.syms}
    (hConstants :
      job.entailment.toRelCalcEntailment.constants.attach.sort =
        constants)
    (hRelations : Gamma.syms.attach.sort = relations) :
    job.closedEntailment =
      job.closedEntailmentOfLists constants relations := by
  unfold closedEntailment closedEntailmentOfLists
    RelCalc.SentenceEntailment.toFOLWithSupportAxioms
  rw [RelCalc.ToFOL.supportAxioms_eq_ofLists Gamma _
    hConstants hRelations]

/- Ordinary closed proposition over explicit lists. -/
abbrev ShallowTargetOfLists
    [LinearOrder D]
    (job : CertificateJob D Gamma)
    (constants :
      List job.entailment.toRelCalcEntailment.constants)
    (relations : List Gamma.syms) : Prop :=
  FOL.SentenceEntailment.ImplicationShallowValid
    (job.closedEntailmentOfLists constants relations)

/-
  A kernel-checked negative empty check and an exact
  leancheck proposition prove the source QF entailment.
-/
theorem valid_of_fullProof
    [LinearOrder D]
    (job : CertificateJob D Gamma)
    (hEmpty :
      job.entailment.emptyCounterexample? = false)
    (fullProof : job.ShallowTarget) :
    job.entailment.Valid := by
  apply
    QFEntailment.valid_of_noEmpty_and_toFOLWithSupportAxioms
      job.entailment
  · exact
      QFEntailment.noEmpty_of_emptyCounterexample?_eq_false
        job.entailment hEmpty
  · exact
      job.closedEntailment.valid_of_implicationShallowValid
        fullProof

/-
  The explicit-list target proves the source QF entailment
  once the list equalities are kernel-checked.
-/
theorem valid_of_fullProof_lists
    [LinearOrder D]
    (job : CertificateJob D Gamma)
    {constants :
      List job.entailment.toRelCalcEntailment.constants}
    {relations : List Gamma.syms}
    (hConstants :
      job.entailment.toRelCalcEntailment.constants.attach.sort =
        constants)
    (hRelations : Gamma.syms.attach.sort = relations)
    (hEmpty :
      job.entailment.emptyCounterexample? = false)
    (fullProof :
      job.ShallowTargetOfLists constants relations) :
    job.entailment.Valid := by
  apply job.valid_of_fullProof hEmpty
  unfold ShallowTarget
  rw [job.closedEntailment_eq_ofLists hConstants hRelations]
  exact fullProof

end CertificateJob

end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Exact Job Construction
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace LeveledFamily

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}
variable {body : Cmd D Gamma}

/- Stable job identifier of one initialization root. -/
def initializationJobId (ordinal : Nat) : String :=
  "init_clause_" ++ toString ordinal

/- Stable job identifier of one maintenance root. -/
def maintenanceJobId (ordinal : Nat) : String :=
  "maint_clause_" ++ toString ordinal

/- Stable job identifier of the termination root. -/
def terminationJobId : String :=
  "term_check"

private def initializationCertificateJobs
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard pre : QFAssertExpr D Gamma) :
    List (CertificateJob D Gamma) :=
  family.clauses.zipIdx.map fun row =>
    CertificateJob.ofEntailment
      (initializationJobId row.2)
      (.initialization row.1)
      (family.initVC task guard pre row.1)

private def maintenanceCertificateJobs
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree) :
    List (CertificateJob D Gamma) :=
  family.clauses.zipIdx.map fun row =>
    CertificateJob.ofEntailment
      (maintenanceJobId row.2)
      (.maintenance row.1)
      (family.maintenanceVC task guard hBody row.1)

/-
  Exact N initialization, N maintenance, and one
  termination job, preserving family order.
-/
def certificateJobs
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre post : QFAssertExpr D Gamma) :
    List (CertificateJob D Gamma) :=
  initializationCertificateJobs task family guard pre ++
    maintenanceCertificateJobs task family guard hBody ++
      [CertificateJob.ofEntailment terminationJobId
        .termination
        (family.terminationVC task guard post)]

/- A family of N rows emits exactly 2N+1 jobs. -/
theorem certificateJobs_length
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre post : QFAssertExpr D Gamma) :
    (family.certificateJobs task guard hBody pre post).length =
      2 * family.clauses.length + 1 := by
  simp [certificateJobs, initializationCertificateJobs,
    maintenanceCertificateJobs]
  omega

private theorem map_zipIdx_fst
    {α β : Type} (g : α -> β) :
    ∀ (items : List α) (start : Nat),
      (items.zipIdx start).map (fun pair => g pair.1) =
        items.map g
  | [], _ => rfl
  | item :: items, start => by
      simp only [List.zipIdx_cons, List.map_cons,
        map_zipIdx_fst g items (start + 1)]

/- The jobs carry exactly the literal same-schema roots. -/
theorem certificateJobs_entailments
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre post : QFAssertExpr D Gamma) :
    (family.certificateJobs task guard hBody pre post).map
        CertificateJob.entailment =
      family.entailments task guard hBody pre post := by
  simp only [certificateJobs, initializationCertificateJobs,
    maintenanceCertificateJobs, entailments, List.map_append,
    List.map_map, List.map_cons, List.map_nil,
    Function.comp_def, CertificateJob.ofEntailment]
  rw [map_zipIdx_fst, map_zipIdx_fst]

end LeveledFamily
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Positional Jobs
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace LeveledFamily

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}
variable {body : Cmd D Gamma}

/- The initialization job of family row `i`. -/
def initializationJob
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard pre : QFAssertExpr D Gamma)
    (i : Nat) : CertificateJob D Gamma :=
  CertificateJob.ofEntailment (initializationJobId i)
    (.initialization (family.row i))
    (family.initVC task guard pre (family.row i))

/- The maintenance job of family row `i`. -/
def maintenanceJob
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (i : Nat) : CertificateJob D Gamma :=
  CertificateJob.ofEntailment (maintenanceJobId i)
    (.maintenance (family.row i))
    (family.maintenanceVC task guard hBody (family.row i))

/- The one termination job of a family. -/
def terminationJob
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard post : QFAssertExpr D Gamma) :
    CertificateJob D Gamma :=
  CertificateJob.ofEntailment terminationJobId
    .termination
    (family.terminationVC task guard post)

private theorem length_initializationCertificateJobs
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard pre : QFAssertExpr D Gamma) :
    (initializationCertificateJobs task family guard pre).length =
      family.clauses.length := by
  simp [initializationCertificateJobs]

private theorem length_maintenanceCertificateJobs
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree) :
    (maintenanceCertificateJobs task family guard hBody).length =
      family.clauses.length := by
  simp [maintenanceCertificateJobs]

/- Job `i` of the exact list is the positional init job. -/
theorem certificateJobs_getElem?_initialization
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre post : QFAssertExpr D Gamma)
    {i : Nat}
    (hi : i < family.clauses.length) :
    (family.certificateJobs task guard hBody pre post)[i]? =
      some (family.initializationJob task guard pre i) := by
  simp only [certificateJobs, List.append_assoc]
  rw [List.getElem?_append_left
    (by rw [length_initializationCertificateJobs]; exact hi)]
  simp [initializationCertificateJobs, initializationJob, row,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/- Job `N + i` of the exact list is the positional step job. -/
theorem certificateJobs_getElem?_maintenance
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre post : QFAssertExpr D Gamma)
    {i : Nat}
    (hi : i < family.clauses.length) :
    (family.certificateJobs task guard hBody
      pre post)[family.clauses.length + i]? =
      some (family.maintenanceJob task guard hBody i) := by
  simp only [certificateJobs, List.append_assoc]
  rw [List.getElem?_append_right
    (by rw [length_initializationCertificateJobs]; omega)]
  rw [length_initializationCertificateJobs, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left
    (by rw [length_maintenanceCertificateJobs]; exact hi)]
  simp [maintenanceCertificateJobs, maintenanceJob, row,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/- Job `2N` of the exact list is the termination job. -/
theorem certificateJobs_getElem?_termination
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre post : QFAssertExpr D Gamma) :
    (family.certificateJobs task guard hBody
      pre post)[2 * family.clauses.length]? =
      some (family.terminationJob task guard post) := by
  simp only [certificateJobs, List.append_assoc]
  rw [List.getElem?_append_right
    (by rw [length_initializationCertificateJobs]; omega)]
  rw [List.getElem?_append_right
    (by rw [length_initializationCertificateJobs,
      length_maintenanceCertificateJobs]; omega)]
  rw [length_initializationCertificateJobs,
    length_maintenanceCertificateJobs]
  rw [show 2 * family.clauses.length - family.clauses.length -
    family.clauses.length = 0 by omega]
  rfl

end LeveledFamily
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Lifted-Loop Jobs
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace LeveledFamily

open Concrete

variable {D : Type} [Domain D]
variable {Delta : UnnamedSchema ProgramNames}

/- Initialization job `i` of a level list over a lifted loop. -/
def initJob
    (loop : Hoare.LoopTriple D Delta)
    (levels : List (List (QFAssertExpr D loop.prophecySchema)))
    (i : Nat) : CertificateJob D loop.prophecySchema :=
  (ofLevels levels).initializationJob loop.task
    loop.lift.guard loop.lift.pre i

/- Maintenance job `i` of a level list over a lifted loop. -/
def maintJob
    (loop : Hoare.LoopTriple D Delta)
    (levels : List (List (QFAssertExpr D loop.prophecySchema)))
    (i : Nat) : CertificateJob D loop.prophecySchema :=
  (ofLevels levels).maintenanceJob loop.task loop.lift.guard
    loop.lift.body_loopFree i

/- The termination job of a level list over a lifted loop. -/
def termJob
    (loop : Hoare.LoopTriple D Delta)
    (levels : List (List (QFAssertExpr D loop.prophecySchema))) :
    CertificateJob D loop.prophecySchema :=
  (ofLevels levels).terminationJob loop.task loop.lift.guard
    loop.lift.post

/- The lifted-loop init job is exact job `i`. -/
theorem initJob_eq_getElem?
    (loop : Hoare.LoopTriple D Delta)
    (levels : List (List (QFAssertExpr D loop.prophecySchema)))
    {i : Nat}
    (hi : i < (ofLevels levels).clauses.length) :
    ((ofLevels levels).certificateJobs loop.task loop.lift.guard
      loop.lift.body_loopFree loop.lift.pre loop.lift.post)[i]? =
      some (initJob loop levels i) :=
  (ofLevels levels).certificateJobs_getElem?_initialization
    loop.task loop.lift.guard loop.lift.body_loopFree
    loop.lift.pre loop.lift.post hi

/- The lifted-loop step job is exact job `N + i`. -/
theorem maintJob_eq_getElem?
    (loop : Hoare.LoopTriple D Delta)
    (levels : List (List (QFAssertExpr D loop.prophecySchema)))
    {i : Nat}
    (hi : i < (ofLevels levels).clauses.length) :
    ((ofLevels levels).certificateJobs loop.task loop.lift.guard
      loop.lift.body_loopFree loop.lift.pre
      loop.lift.post)[(ofLevels levels).clauses.length + i]? =
      some (maintJob loop levels i) :=
  (ofLevels levels).certificateJobs_getElem?_maintenance
    loop.task loop.lift.guard loop.lift.body_loopFree
    loop.lift.pre loop.lift.post hi

/- The lifted-loop termination job is exact job `2N`. -/
theorem termJob_eq_getElem?
    (loop : Hoare.LoopTriple D Delta)
    (levels : List (List (QFAssertExpr D loop.prophecySchema))) :
    ((ofLevels levels).certificateJobs loop.task loop.lift.guard
      loop.lift.body_loopFree loop.lift.pre
      loop.lift.post)[2 * (ofLevels levels).clauses.length]? =
      some (termJob loop levels) :=
  (ofLevels levels).certificateJobs_getElem?_termination
    loop.task loop.lift.guard loop.lift.body_loopFree
    loop.lift.pre loop.lift.post

end LeveledFamily
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Clause Proof Spine
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace LeveledFamily

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}
variable {body : Cmd D Gamma}

/- The two exact VC facts for one retained row. -/
def ClauseValidity
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre : QFAssertExpr D Gamma)
    (clause : LeveledClause D Gamma) : Prop :=
  (family.initVC task guard pre clause).Valid ∧
    (family.maintenanceVC task guard hBody clause).Valid

/- Typed proof spine over an exact ordered clause list. -/
inductive ClauseValidityProofsFor
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre : QFAssertExpr D Gamma) :
    List (LeveledClause D Gamma) -> Prop
| nil : ClauseValidityProofsFor
    task family guard hBody pre []
| cons {clause clauses}
    (head : ClauseValidity task family guard hBody
      pre clause)
    (tail : ClauseValidityProofsFor
      task family guard hBody pre clauses) :
    ClauseValidityProofsFor task family guard hBody
      pre (clause :: clauses)

/-
  Proof spine consumed by generated certificate modules: one
  clause fact per row of the level list, in family order.
-/
abbrev ClauseValidityProofs
    (task : Task body)
    (levels : List (List (QFAssertExpr D Gamma)))
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre : QFAssertExpr D Gamma) : Prop :=
  ClauseValidityProofsFor task (ofLevels levels) guard hBody
    pre (ofLevels levels).clauses

private theorem ClauseValidityProofsFor.initialization
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre : QFAssertExpr D Gamma)
    {clauses : List (LeveledClause D Gamma)}
    (proofs : ClauseValidityProofsFor
      task family guard hBody pre clauses) :
    ∀ clause ∈ clauses,
      (family.initVC task guard pre clause).Valid := by
  intro clause hClause
  induction proofs with
  | nil => simp at hClause
  | cons head tail ih =>
      rcases List.mem_cons.mp hClause with rfl | hClause
      · exact head.1
      · exact ih hClause

private theorem ClauseValidityProofsFor.maintenance
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre : QFAssertExpr D Gamma)
    {clauses : List (LeveledClause D Gamma)}
    (proofs : ClauseValidityProofsFor
      task family guard hBody pre clauses) :
    ∀ clause ∈ clauses,
      (family.maintenanceVC task guard hBody
        clause).Valid := by
  intro clause hClause
  induction proofs with
  | nil => simp at hClause
  | cons head tail ih =>
      rcases List.mem_cons.mp hClause with rfl | hClause
      · exact head.2
      · exact ih hClause

/- Recover every initialization fact from the spine. -/
theorem ClauseValidityProofs.initialization
    (task : Task body)
    (levels : List (List (QFAssertExpr D Gamma)))
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre : QFAssertExpr D Gamma)
    (proofs : ClauseValidityProofs
      task levels guard hBody pre) :
    ∀ clause ∈ (ofLevels levels).clauses,
      ((ofLevels levels).initVC task guard pre clause).Valid :=
  ClauseValidityProofsFor.initialization
    task (ofLevels levels) guard hBody pre proofs

/- Recover every maintenance fact from the spine. -/
theorem ClauseValidityProofs.maintenance
    (task : Task body)
    (levels : List (List (QFAssertExpr D Gamma)))
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre : QFAssertExpr D Gamma)
    (proofs : ClauseValidityProofs
      task levels guard hBody pre) :
    ∀ clause ∈ (ofLevels levels).clauses,
      ((ofLevels levels).maintenanceVC task guard hBody
        clause).Valid :=
  ClauseValidityProofsFor.maintenance
    task (ofLevels levels) guard hBody pre proofs

end LeveledFamily

namespace Preproc

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}
variable {inputPre inputPost : AssertExpr D Gamma}
variable {inputCmd : Cmd D Gamma}

/-
  Finish the fixed-ambient assembly theorem from the ordered
  clause-proof spine and the termination fact.
-/
theorem certifyInput_of_clauseProofs
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (task : Task P.loopBody)
    (levels : List (List (QFAssertExpr D P.outSchema)))
    (hPreSymbols :
      (loopPreQF P).symbols ⊆ task.programSymbols)
    (hGuardSymbols :
      P.loopGuard.symbols ⊆ task.programSymbols)
    (hBodySymbols :
      P.loopBody.symbols ⊆ task.programSymbols)
    (hPostSymbols :
      (loopPostQF P).symbols ⊆ task.programSymbols)
    (proofs : LeveledFamily.ClauseValidityProofs
      task levels P.loopGuard P.loopBody_loopFree
      (loopPreQF P))
    (hTerm :
      ((LeveledFamily.ofLevels levels).terminationVC task
        P.loopGuard (loopPostQF P)).Valid) :
    HoareValid inputPre inputCmd inputPost :=
  certifyInput P task (LeveledFamily.ofLevels levels)
    hPreSymbols hGuardSymbols hBodySymbols hPostSymbols
    (proofs.initialization task levels P.loopGuard
      P.loopBody_loopFree (loopPreQF P))
    (proofs.maintenance task levels P.loopGuard
      P.loopBody_loopFree (loopPreQF P))
    hTerm

end Preproc

end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Input-Schema Certificate Entry Point
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace Preproc

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema ProgramNames}
variable {inputPre inputPost : AssertExpr D Gamma}
variable {inputCmd : Cmd D Gamma}

/-
  Certificate entry point over a program-name input: the
  ordered clause-proof spine and termination fact of the
  lifted loop, over the certificate's level list, prove the
  raw input triple over its own schema. The symbol side
  conditions hold by construction of the lift.
-/
theorem certifyProgramInput_of_clauseProofs
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (levels : List (List (QFAssertExpr D (loop P).prophecySchema)))
    (proofs : LeveledFamily.ClauseValidityProofs
      (loop P).task levels (loop P).lift.guard
      (loop P).lift.body_loopFree (loop P).lift.pre)
    (hTerm :
      ((LeveledFamily.ofLevels levels).terminationVC (loop P).task
        (loop P).lift.guard (loop P).lift.post).Valid) :
    HoareValid inputPre inputCmd inputPost :=
  certifyProgramInput P (LeveledFamily.ofLevels levels)
    (proofs.initialization (loop P).task levels
      (loop P).lift.guard (loop P).lift.body_loopFree
      (loop P).lift.pre)
    (proofs.maintenance (loop P).task levels
      (loop P).lift.guard (loop P).lift.body_loopFree
      (loop P).lift.pre)
    hTerm

end Preproc

end FixedAmbient
end FrameworkII
end Synthesis
end Whiel
