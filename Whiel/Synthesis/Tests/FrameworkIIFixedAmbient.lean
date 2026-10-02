-- Author: Jesse Comer
import Whiel.Synthesis.FrameworkII.FixedAmbient.Assembly
import Whiel.Concrete.WhielNames.Notation
import Whiel.Tests.FixedAmbientProphecy

/-
  Type and assembly canary for the same-schema Framework-II
  certificate layer.
-/

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIFixedAmbient

open Concrete
open Whiel.Tests.FixedAmbientProphecyCanary
open FrameworkII.FixedAmbient

def levelZeroClause :
    LeveledClause Data ambientSchema where
  formula := levelZeroFormula
  level := 0

def levelOneClause :
    LeveledClause Data ambientSchema where
  formula := levelOneFormula
  level := 1

def family : LeveledFamily Data ambientSchema where
  clauses := [levelZeroClause, levelOneClause]

/- Wire identity uses only the canonical machine key. -/
def taskIdentity : Lean.Json :=
  Task.identityJson task WhielNames.encode

/- The loop's three writes induce exactly three bindings. -/
theorem exact_binding_count :
    (Task.bindings task).length = 3 := by
  have hSources := Task.bindingSources_eq task
  have hLengths := congrArg List.length hSources
  simpa [loopBody, Cmd.assignedSymbols] using hLengths

/- Every generated root has the literal ambient schema. -/
def initZeroVC :
    QFEntailment (D := Data) ambientSchema :=
  family.initVC task loopGuard levelZeroFormula
    levelZeroClause

def initOneVC :
    QFEntailment (D := Data) ambientSchema :=
  family.initVC task loopGuard levelZeroFormula
    levelOneClause

def maintenanceZeroVC :
    QFEntailment (D := Data) ambientSchema :=
  family.maintenanceVC task loopGuard (by decide)
    levelZeroClause

def maintenanceOneVC :
    QFEntailment (D := Data) ambientSchema :=
  family.maintenanceVC task loopGuard (by decide)
    levelOneClause

def terminationVC :
    QFEntailment (D := Data) ambientSchema :=
  family.terminationVC task loopGuard postFormula

/- The complete list retains the literal ambient schema. -/
def allEntailments :
    List (QFEntailment (D := Data) ambientSchema) :=
  family.entailments task loopGuard (by decide)
    levelZeroFormula postFormula

theorem exact_entailment_count :
    allEntailments.length = 5 := by
  rw [allEntailments, family.entailments_length]
  rfl

/- Two retained clauses have exactly five proof roots. -/
theorem exact_job_count : family.jobs.length = 5 := by
  rw [family.jobs_length]
  rfl

/- The concrete rows recover the semantic canary levels. -/
theorem semanticLevels_eq :
    family.semanticLevels = candidateLevels := by
  funext level
  cases level with
  | zero =>
      rfl
  | succ level =>
      cases level with
      | zero =>
          rfl
      | succ level =>
          simp [family, LeveledFamily.semanticLevels,
            LeveledFamily.atLevel, candidateLevels,
            levelZeroClause, levelOneClause]

/-
  Exact validity proofs for the five same-schema roots are
  sufficient to recover the original ambient loop theorem.
-/
theorem exact_jobs_assemble
    (hInit : ∀ clause ∈ family.clauses,
      (family.initVC task loopGuard levelZeroFormula
        clause).Valid)
    (hStep : ∀ clause ∈ family.clauses,
      (family.maintenanceVC task loopGuard
        (by decide) clause).Valid)
    (hTerm :
      (family.terminationVC task loopGuard
        postFormula).Valid) :
    HoareValid levelZeroFormula.eval inputCmd
      postFormula.eval := by
  unfold inputCmd
  exact family.hoareValid_of_valid_vcs
    task loopGuard (by decide)
    levelZeroFormula postFormula
    (by decide) (by decide) (by decide) (by decide)
    hInit hStep hTerm

/- Preprocessed assembly preserves the input triple. -/
theorem preproc_jobs_assemble
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (task : Task P.loopBody)
    (family : LeveledFamily Data P.outSchema)
    (hPreSymbols :
      (Preproc.loopPreQF P).symbols ⊆
        task.programSymbols)
    (hGuardSymbols :
      P.loopGuard.symbols ⊆ task.programSymbols)
    (hBodySymbols :
      P.loopBody.symbols ⊆ task.programSymbols)
    (hPostSymbols :
      (Preproc.loopPostQF P).symbols ⊆
        task.programSymbols)
    (hInit : ∀ clause ∈ family.clauses,
      (family.initVC task P.loopGuard
        (Preproc.loopPreQF P) clause).Valid)
    (hStep : ∀ clause ∈ family.clauses,
      (family.maintenanceVC task P.loopGuard
        P.loopBody_loopFree clause).Valid)
    (hTerm :
      (family.terminationVC task P.loopGuard
        (Preproc.loopPostQF P)).Valid) :
    HoareValid inputPre inputCmd inputPost :=
  Preproc.certifyInput P task family
    hPreSymbols hGuardSymbols hBodySymbols
      hPostSymbols hInit hStep hTerm

/-
  Program-name assembly: exact jobs of the lifted loop over
  the computed prophecy schema prove the raw program-name
  triple; no symbol side condition is supplied.
-/
theorem program_input_assembles
    (family : LeveledFamily Data
      (Preproc.loop programPreproc).prophecySchema)
    (hInit : ∀ clause ∈ family.clauses,
      (family.initVC (Preproc.loop programPreproc).task
        (Preproc.loop programPreproc).lift.guard
        (Preproc.loop programPreproc).lift.pre
        clause).Valid)
    (hStep : ∀ clause ∈ family.clauses,
      (family.maintenanceVC (Preproc.loop programPreproc).task
        (Preproc.loop programPreproc).lift.guard
        (Preproc.loop programPreproc).lift.body_loopFree
        clause).Valid)
    (hTerm :
      (family.terminationVC (Preproc.loop programPreproc).task
        (Preproc.loop programPreproc).lift.guard
        (Preproc.loop programPreproc).lift.post).Valid) :
    HoareValid programPre programCmd programPost :=
  Preproc.certifyProgramInput programPreproc family
    hInit hStep hTerm

/- The computed schema of the program input is the canary's. -/
example :
    (Preproc.loop programPreproc).prophecySchema.syms =
      ambientSchema.syms := by
  decide

end FrameworkIIFixedAmbient
end Tests
end Synthesis
end Whiel
