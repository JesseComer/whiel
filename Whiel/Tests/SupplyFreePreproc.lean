-- Author: Jesse Comer
import Whiel.Concrete.Data
import Whiel.Concrete.Notation
import Whiel.Hoare.Preproc
import Whiel.Hoare.ProphecySchema

/-
  Focused checks for the supply-free strongest postcondition
  the preamble split is built on, over a relation-name
  carrier that deliberately has no fresh-name supply, and
  for the preprocessor's bridge at a source that is not a
  framed loop.
-/

namespace Whiel

namespace Tests

namespace SupplyFreePreproc

open Concrete

------------------------------------------------------------
-- Fixed Ambient Fixture
------------------------------------------------------------

inductive TestName
| source
| prefix
| body
| close
deriving DecidableEq, Repr

instance : RelationNames TestName where
  decEq := inferInstance
  repr := inferInstance

def testSchema : UnnamedSchema TestName where
  syms := {.source, .prefix, .body, .close}
  arity := fun _ => 1

def sourceRelation : testSchema.syms :=
  ⟨.source, by decide⟩

def prefixRelation : testSchema.syms :=
  ⟨.prefix, by decide⟩

def bodyRelation : testSchema.syms :=
  ⟨.body, by decide⟩

def closeRelation : testSchema.syms :=
  ⟨.close, by decide⟩

def sourceEmpty : QFAssertExpr Data testSchema :=
  .eq (RAExpr.rel sourceRelation) (RAExpr.empty 1)

def prefixEmpty : QFAssertExpr Data testSchema :=
  .eq (RAExpr.rel prefixRelation) (RAExpr.empty 1)

def closeEmpty : QFAssertExpr Data testSchema :=
  .eq (RAExpr.rel closeRelation) (RAExpr.empty 1)

def inputPre : AssertExpr Data testSchema :=
  AssertExpr.ofQF sourceEmpty

def inputPrefix : Cmd Data testSchema :=
  .assign prefixRelation (RAExpr.empty 1)

def inputBody : Cmd Data testSchema :=
  .assign bodyRelation (RAExpr.empty 1)

def inputClose : Cmd Data testSchema :=
  .assign closeRelation (RAExpr.empty 1)

def inputCmd : Cmd Data testSchema :=
  Cmd.framedLoopCommand inputPrefix .false
    inputBody inputClose

def inputPost : AssertExpr Data testSchema :=
  AssertExpr.ofQF closeEmpty

------------------------------------------------------------
-- Supply-Free SP Checks
------------------------------------------------------------

def simpleSequence : Cmd Data testSchema :=
  .seq inputPrefix inputClose

def simpleConditional : Cmd Data testSchema :=
  .ite .false inputPrefix inputClose

theorem sequenceSPAccepted :
    (AssertExpr.spLoopFreeNoFresh?
      simpleSequence (by decide) inputPre).isSome := by
  decide

theorem conditionalSPAccepted :
    (AssertExpr.spLoopFreeNoFresh?
      simpleConditional (by decide) inputPre).isSome := by
  decide

def targetReadingPre : AssertExpr Data testSchema :=
  AssertExpr.ofQF prefixEmpty

def targetReadingAssignment : Cmd Data testSchema :=
  .assign prefixRelation (RAExpr.rel prefixRelation)

theorem preTargetRejected :
    (AssertExpr.spLoopFreeNoFresh?
      inputPrefix (by decide) targetReadingPre).isNone := by
  decide

theorem rhsTargetRejected :
    (AssertExpr.spLoopFreeNoFresh?
      targetReadingAssignment (by decide)
        inputPre).isNone := by
  decide

------------------------------------------------------------
-- The Preprocessor At A Nested Source
------------------------------------------------------------

end SupplyFreePreproc

end Tests

end Whiel

namespace Whiel

namespace Tests

namespace SupplyFreePreproc

open Concrete

/-
  A source that is not a framed loop: a loop nested inside a
  loop, with a conditional after it. The preprocessor draws
  flags for it, so the preprocessed loop lives over a strict
  extension of the input schema and the bridge's projection
  is not the identity.
-/
def nestSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, S, T} (arity: 1)
  ]

def nestPre : AssertExpr Data nestSchema :=
  programAssert![ true ]

def nestCmd : Cmd Data nestSchema :=
  programCmd![
    { ExecSchema: nestSchema }
    {
      WHILE (S ≠ T) DO
        WHILE (S ≠ E) DO
          S := E
        END;
        T := S
      END;
      IF (S = T) THEN
        T := E
      ELSE
        S := E
      END
    }
  ]

def nestPost : AssertExpr Data nestSchema :=
  programAssert![ true ]

def nestPreproc :
    Hoare.Preproc nestPre nestCmd nestPost :=
  Hoare.preprocess nestPre nestCmd nestPost

/- The transformation drew flags: the schema really grew. -/
theorem nest_schema_grew :
    nestSchema.syms.card <
      nestPreproc.outSchema.syms.card := by
  decide +kernel

/- Every symbol the transformation added is a flag. -/
theorem nest_new_symbols_are_flags :
    ∀ X ∈ nestPreproc.outSchema.syms,
      X ∉ nestSchema.syms → X.IsFlag := by
  decide +kernel

/- The preprocessed body is a single loop-free command. -/
example : nestPreproc.loopBody.LoopFree :=
  nestPreproc.loopBody_loopFree

/-
  The bridge's loop-head clauses: every loop-head state
  projects to an input state fixed by the post-split prefix.
-/
example :
    forall u : Instance Data nestPreproc.outSchema,
      nestPreproc.loopPre.eval u ->
        nestPre.eval
            (Preprocess.project nestPreproc.outExtends u) ∧
          Cmd.BigStep nestPreproc.sourcePrefix u u :=
  nestPreproc.loopPre_source_fixed

/- Validity of the single loop proves the input triple. -/
example
    (hLoop :
      HoareValid nestPreproc.loopPre nestPreproc.loopCmd
        nestPreproc.loopPost) :
    HoareValid nestPre nestCmd nestPost :=
  nestPreproc.valid_input hLoop

end SupplyFreePreproc

end Tests

end Whiel
