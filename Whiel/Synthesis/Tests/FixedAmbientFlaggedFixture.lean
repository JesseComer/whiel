-- Author: Jesse Comer
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import
  Whiel.Synthesis.FrameworkII.FixedAmbient.CertificateEmitter

set_option linter.hashCommand false

/-
  A test-only dependent program. The second loop reads R,
  which the first loop writes, so preprocessing draws flags.
  True is a sound invariant and postcondition. The emitted
  certificate is checked separately from this source proof.
-/

namespace Whiel.Synthesis.Tests.FixedAmbientFlaggedFixture

open Concrete
open FrameworkII.FixedAmbient

/- Two unary program relations, with no input flags. -/
def inputSchema : UnnamedSchema ProgramNames :=
  programSch![ {R, U} (arity: 1) ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![ { ExecSchema: inputSchema }
    { (WHILE R ≠ ∅ DO R := ∅ END);
      (WHILE R ≠ ∅ DO U := R END) } ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![ true ]

/- The production preprocessing computation. -/
def inputPreproc :
    Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- Independent source soundness; no certificate shortcut. -/
theorem input_valid :
    HoareValid inputPre inputCmd inputPost := by
  intro I J hPre hExec
  exact (AssertExpr.ofQF_eval_iff .true J).mpr trivial

abbrev certifiedLoop :
    Hoare.LoopTriple Data inputPreproc.outSchema :=
  Preproc.loop inputPreproc

abbrev prophecySchema : UnnamedSchema WhielNames :=
  certifiedLoop.prophecySchema

/- The actual output schema contains both control flags. -/
#guard inputSchema.syms.card == 2
#guard inputPreproc.outSchema.syms.card == 4
#guard ProgramNames.flagSymbol 0 0 ∈
  inputPreproc.outSchema.syms
#guard ProgramNames.flagSymbol 1 0 ∈
  inputPreproc.outSchema.syms
#guard WhielNames.ordinary (.flagSymbol 0 0) ∈
  prophecySchema.syms
#guard WhielNames.prophecy (.flagSymbol 0 0) ∈
  prophecySchema.syms
#guard WhielNames.ordinary (.flagSymbol 1 0) ∈
  prophecySchema.syms
#guard WhielNames.prophecy (.flagSymbol 1 0) ∈
  prophecySchema.syms

/- One true row exercises all three certificate roles. -/
def snapshot : Snapshot prophecySchema where
  rows :=
    [ { clauseId := 1
        level := 0
        clause := Clause.ofFormula .true } ]

end Whiel.Synthesis.Tests.FixedAmbientFlaggedFixture
