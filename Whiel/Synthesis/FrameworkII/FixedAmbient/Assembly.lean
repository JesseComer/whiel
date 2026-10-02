-- Author: Jesse Comer
import Whiel.Hoare.Preproc
import Whiel.Hoare.ProphecySchema
import Whiel.Synthesis.FrameworkII.FixedAmbient.Obligations

/-
  Kernel assembly for exact same-schema Framework-II jobs.
-/

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient

open Concrete
open Hoare.FixedAmbientProphecy

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}
variable {body : Cmd D Gamma}

namespace LeveledFamily

/-
  The exact 2N+1 syntactic jobs prove the ambient loop.
  No schema extension, restriction, or transport occurs.
-/
theorem hoareValid_of_valid_vcs
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre post : QFAssertExpr D Gamma)
    (hPreSymbols :
      pre.symbols ⊆ task.programSymbols)
    (hGuardSymbols :
      guard.symbols ⊆ task.programSymbols)
    (hBodySymbols :
      body.symbols ⊆ task.programSymbols)
    (hPostSymbols :
      post.symbols ⊆ task.programSymbols)
    (hInit : ∀ clause ∈ family.clauses,
      (family.initVC task guard pre clause).Valid)
    (hStep : ∀ clause ∈ family.clauses,
      (family.maintenanceVC task guard hBody
        clause).Valid)
    (hTerm :
      (family.terminationVC task guard post).Valid) :
    HoareValid pre.eval (.while guard body) post.eval := by
  apply hoareValid_while_of_leveled_vcs
    task.programSymbols task.prophecyCollapse
      family.semanticLevels pre post
  · exact hPreSymbols
  · exact hGuardSymbols
  · exact hBodySymbols
  · exact hPostSymbols
  · intro level assertion hAssertion
    rcases (family.mem_semanticLevels_iff
      level assertion).mp hAssertion with
      ⟨clause, hClause, hLevel, hEval⟩
    subst level
    rw [← hEval]
    exact family.initObligation_of_valid
      task guard pre clause (hInit clause hClause)
  · intro level assertion hAssertion
    rcases (family.mem_semanticLevels_iff
      level assertion).mp hAssertion with
      ⟨clause, hClause, hLevel, hEval⟩
    subst level
    rw [← hEval]
    exact family.stepObligation_of_valid
      task guard hBody clause (hStep clause hClause)
  · exact family.termObligation_of_valid
      task guard post hTerm

end LeveledFamily

namespace Preproc

variable {inputPre inputPost : AssertExpr D Gamma}
variable {inputCmd : Cmd D Gamma}

/- Checked QF view of the normalized loop precondition. -/
def loopPreQF
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    QFAssertExpr D P.outSchema :=
  P.loopPre.toQFOfNoBound P.loopPre_noBound

/- Checked QF view of the normalized loop postcondition. -/
def loopPostQF
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    QFAssertExpr D P.outSchema :=
  P.loopPost.toQFOfNoBound P.loopPost_noBound

/-
  Certificate-facing assembly: the exact fixed-ambient jobs
  for a preprocessed loop prove the original input triple.
-/
theorem certifyInput
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (task : Task P.loopBody)
    (family : LeveledFamily D P.outSchema)
    (hPreSymbols :
      (loopPreQF P).symbols ⊆ task.programSymbols)
    (hGuardSymbols :
      P.loopGuard.symbols ⊆ task.programSymbols)
    (hBodySymbols :
      P.loopBody.symbols ⊆ task.programSymbols)
    (hPostSymbols :
      (loopPostQF P).symbols ⊆ task.programSymbols)
    (hInit : ∀ clause ∈ family.clauses,
      (family.initVC task P.loopGuard
        (loopPreQF P) clause).Valid)
    (hStep : ∀ clause ∈ family.clauses,
      (family.maintenanceVC task P.loopGuard
        P.loopBody_loopFree clause).Valid)
    (hTerm :
      (family.terminationVC task P.loopGuard
        (loopPostQF P)).Valid) :
    HoareValid inputPre inputCmd inputPost := by
  have hQF :
      HoareValid (loopPreQF P).eval
        (.while P.loopGuard P.loopBody)
        (loopPostQF P).eval :=
    family.hoareValid_of_valid_vcs task
      P.loopGuard P.loopBody_loopFree
      (loopPreQF P) (loopPostQF P)
      hPreSymbols hGuardSymbols hBodySymbols
      hPostSymbols hInit hStep hTerm
  have hLoop :
      HoareValid P.loopPre P.loopCmd P.loopPost := by
    intro initial final hPre hRun
    apply (AssertExpr.toQFOfNoBound_eval_iff
      P.loopPost P.loopPost_noBound final).mp
    apply hQF initial final
    · exact (AssertExpr.toQFOfNoBound_eval_iff
        P.loopPre P.loopPre_noBound initial).mpr hPre
    · exact hRun
  exact Hoare.Preproc.valid_input P hLoop

end Preproc

end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Input-Schema Assembly Through The Prophecy Lift
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient

open Concrete
open Hoare

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema ProgramNames}

namespace LoopTriple

/- The exact jobs of the lifted loop prove the input loop. -/
theorem valid_of_valid_vcs
    (loop : Hoare.LoopTriple D Gamma)
    (family : LeveledFamily D loop.prophecySchema)
    (hInit : ∀ clause ∈ family.clauses,
      (family.initVC loop.task loop.lift.guard loop.lift.pre
        clause).Valid)
    (hStep : ∀ clause ∈ family.clauses,
      (family.maintenanceVC loop.task loop.lift.guard
        loop.lift.body_loopFree clause).Valid)
    (hTerm :
      (family.terminationVC loop.task loop.lift.guard
        loop.lift.post).Valid) :
    loop.Valid := by
  apply loop.hoareValid_of_lift
  exact family.hoareValid_of_valid_vcs loop.task
    loop.lift.guard loop.lift.body_loopFree
    loop.lift.pre loop.lift.post
    (symbols_liftGuard_subset_programSymbols loop.pre)
    (symbols_liftGuard_subset_programSymbols loop.guard)
    (symbols_liftCmd_subset_programSymbols loop.body)
    (symbols_liftGuard_subset_programSymbols loop.post)
    hInit hStep hTerm

end LoopTriple

namespace Preproc

variable {inputPre inputPost : AssertExpr D Gamma}
variable {inputCmd : Cmd D Gamma}

/- The preprocessed input loop over its own schema. -/
abbrev loop
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    Hoare.LoopTriple D P.outSchema :=
  Hoare.LoopTriple.ofPreproc P

/-
  Certificate-facing assembly over a program-name input: the
  exact fixed-ambient jobs of the lifted loop prove the raw
  input triple over its own schema.
-/
theorem certifyProgramInput
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (family : LeveledFamily D (loop P).prophecySchema)
    (hInit : ∀ clause ∈ family.clauses,
      (family.initVC (loop P).task (loop P).lift.guard
        (loop P).lift.pre clause).Valid)
    (hStep : ∀ clause ∈ family.clauses,
      (family.maintenanceVC (loop P).task (loop P).lift.guard
        (loop P).lift.body_loopFree clause).Valid)
    (hTerm :
      (family.terminationVC (loop P).task (loop P).lift.guard
        (loop P).lift.post).Valid) :
    HoareValid inputPre inputCmd inputPost :=
  Hoare.LoopTriple.valid_input_of_ofPreproc P
    (LoopTriple.valid_of_valid_vcs (loop P) family
      hInit hStep hTerm)

end Preproc

end FixedAmbient
end FrameworkII
end Synthesis
end Whiel
