-- Author: Jesse Comer
import Benchmark.Example0001.Input
import Benchmark.Example0013.Input
import Benchmark.Example0106.Input
import Benchmark.Example4002.Input
import Benchmark.Example4037.Input
import Benchmark.Example4041.Input
import Whiel.Synthesis.Tests.BenchmarkNotationRoundTrip

/-
  Notation round trip for the preprocessed side of the
  Framework II benchmark corpus.

  `#roundTripPreproc N` renders one corpus input's
  preprocessing result --- the loop-head assertion, the four
  components of the framed loop, and the closing assertion
  --- with the library printers, over the flag extension the
  transformation drew, and re-reads the rendered text through
  `programSch!`, `programAssert!`, `programCmd!` and
  `programQF!`. A drawn flag spells `flag_i_n` and the
  notation reads exactly that name back, so a preprocessed
  program is a program the notation accepts rather than a
  display-only rendering.

  This is a separate module from the source round trip
  because it is the slowest Lean gate in the tree: every
  obligation is stated over `inputPreproc.outSchema`, and
  both the notation's arity resolution and the obligation
  itself force the preprocessor's own reduction, chiefly the
  preamble split's strongest postcondition.

  All seven obligations per input are kernel checks: the
  two-way schema extension and the four command and guard
  equalities by `decide +kernel` through
  `Cmd.eq_of_toRaw_eq`/`Guard.eq_of_toRaw_eq`, and the two
  assertion equalities through
  `AssertExpr.eq_of_noBound_toRaw_eq`, whose three
  hypotheses are decidable. Measured, that routing is cost
  neutral against the `by rfl` form it replaced --- the cost
  is computing the preprocessed assertions, not where the
  equality is checked --- and it is kept because it puts an
  assertion equality on the same footing as a command one.

  The rendering runs in the elaborator, so nothing is
  transcribed by hand; the emitted equations are ordinary
  proofs the kernel checks.
-/

------------------------------------------------------------
-- The Preprocessed Round-Trip Command
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkNotationRoundTrip

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term

/- Re-read one rendered fragment through the notation. -/
private def parseTerm
    (text : String) : CommandElabM Term := do
  match Lean.Parser.runParserCategory
      (← getEnv) `term text with
  | .ok stx => pure ⟨stx⟩
  | .error message =>
      throwError
        "rendered text is not notation:\n\
          {message}\n{text}"

syntax (name := roundTripPreprocCommand)
  "#roundTripPreproc " ident : command

/-
  Round trip the preprocessed side of one corpus input: the
  loop-head assertion, the four components of the framed
  loop the preprocessor returns, and the closing assertion,
  all over the flag extension the transformation drew.

  This is the corpus half of the flag spelling: a drawn
  flag renders as `flag_i_n` and the notation reads exactly
  that name back, so a preprocessed program is a program
  the notation accepts, not a display-only rendering.
-/
unsafe def elabRoundTripPreprocUnsafe :
    CommandElab := fun stx => do
  match stx with
  | `(#roundTripPreproc $ns:ident) => do
      let base := ns.getId
      let preprocId := mkIdent (base ++ `inputPreproc)
      let schemaText :=
        (base ++ `inputPreproc).toString ++ ".outSchema"
      let schemaStxTerm ← parseTerm schemaText
      let schemaFn := mkIdent ``schemaSource
      let cmdEq := mkIdent ``Whiel.Cmd.eq_of_toRaw_eq
      let guardEq := mkIdent ``Whiel.Guard.eq_of_toRaw_eq
      let assertEq :=
        mkIdent ``Whiel.AssertExpr.eq_of_noBound_toRaw_eq
      let (schemaBody, preBody, initBody, bodyBody,
          closeBody, guardBody, postBody) ←
        liftTermElabM do
          let stringType := Lean.mkConst ``String
          let render (t : Term) : TermElabM String :=
            Term.evalTerm String stringType t
          let schemaBody ← render
            (← `($schemaFn ($preprocId).outSchema))
          let preBody ← render
            (← `(Whiel.AssertExpr.pretty
              ($preprocId).loopPre))
          let initBody ← render
            (← `(Whiel.Cmd.pretty ($preprocId).sourcePrefix))
          let bodyBody ← render
            (← `(Whiel.Cmd.pretty ($preprocId).loopBody))
          let closeBody ← render
            (← `(Whiel.Cmd.pretty ($preprocId).sourceClose))
          let guardBody ← render
            (← `(Whiel.Guard.pretty ($preprocId).loopGuard))
          let postBody ← render
            (← `(Whiel.AssertExpr.pretty
              ($preprocId).loopPost))
          pure (schemaBody, preBody, initBody, bodyBody,
            closeBody, guardBody, postBody)
      let schemaStx ←
        parseTerm ("programSch![" ++ schemaBody ++ "]")
      let preStx ←
        parseTerm ("programAssert![" ++ preBody ++ "]")
      let postStx ←
        parseTerm ("programAssert![" ++ postBody ++ "]")
      let cmdSyntax (body : String) : CommandElabM Term :=
        parseTerm
          ("programCmd![{ ExecSchema: " ++ schemaText ++
            " }{" ++ body ++ "}]")
      let initStx ← cmdSyntax initBody
      let bodyStx ← cmdSyntax bodyBody
      let closeStx ← cmdSyntax closeBody
      let guardStx ←
        parseTerm ("programQF![" ++ guardBody ++ "]")
      elabCommand (← `(command|
        example :
            UnnamedSchema.extensionOf
                ($schemaStx :
                  UnnamedSchema
                    Whiel.Concrete.ProgramNames)
                $schemaStxTerm ∧
              UnnamedSchema.extensionOf $schemaStxTerm
                ($schemaStx :
                  UnnamedSchema
                    Whiel.Concrete.ProgramNames) := by
          decide +kernel))
      elabCommand (← `(command|
        example :
            ($preStx :
              Whiel.AssertExpr Whiel.Concrete.Data
                $schemaStxTerm) =
              ($preprocId).loopPre :=
          $assertEq (by decide +kernel) (by decide +kernel)
            (by decide +kernel)))
      elabCommand (← `(command|
        example :
            ($postStx :
              Whiel.AssertExpr Whiel.Concrete.Data
                $schemaStxTerm) =
              ($preprocId).loopPost :=
          $assertEq (by decide +kernel) (by decide +kernel)
            (by decide +kernel)))
      elabCommand (← `(command|
        example :
            ($initStx :
              Whiel.Cmd Whiel.Concrete.Data
                $schemaStxTerm) =
              ($preprocId).sourcePrefix :=
          $cmdEq (by decide +kernel)))
      elabCommand (← `(command|
        example :
            ($bodyStx :
              Whiel.Cmd Whiel.Concrete.Data
                $schemaStxTerm) =
              ($preprocId).loopBody :=
          $cmdEq (by decide +kernel)))
      elabCommand (← `(command|
        example :
            ($closeStx :
              Whiel.Cmd Whiel.Concrete.Data
                $schemaStxTerm) =
              ($preprocId).sourceClose :=
          $cmdEq (by decide +kernel)))
      elabCommand (← `(command|
        example :
            ($guardStx :
              Whiel.Guard Whiel.Concrete.Data
                $schemaStxTerm) =
              ($preprocId).loopGuard :=
          $guardEq (by decide +kernel)))
  | _ => throwUnsupportedSyntax

@[implemented_by elabRoundTripPreprocUnsafe]
opaque elabRoundTripPreprocImpl : CommandElab

@[command_elab roundTripPreprocCommand]
def elabRoundTripPreproc : CommandElab :=
  elabRoundTripPreprocImpl

end BenchmarkNotationRoundTrip

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Corpus Round Trips
------------------------------------------------------------

/-
  The six inputs run here are `Example0001`,
  `Example0013`, `Example4002` and `Example4037`, the inputs
  with the first checked-in certificates; the canary candidate `Example0106`;
  and `Example4041`, the corpus input whose
  sequenced programs are dependent, so its preprocessing
  draws flags and the flag spelling is round tripped over a
  corpus input rather than only over a unit-test program.
  They are among the smallest inputs, at about 2.3 s each.

  These six stay in the test root as a fast canary. The
  whole corpus is covered by one generated module per input
  under `BenchmarkPreprocRoundTrip/Cases/`, aggregated in
  `BenchmarkPreprocRoundTripCases.lean`: an input costs from
  a few seconds to a few minutes, so that aggregate is built
  as its own target rather than with the test root.
-/

open Whiel.Synthesis.Tests.BenchmarkNotationRoundTrip

set_option linter.hashCommand false
set_option linter.style.setOption false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

#roundTripPreproc Whiel.Benchmark.Example0001
#roundTripPreproc Whiel.Benchmark.Example0013
#roundTripPreproc Whiel.Benchmark.Example0106
#roundTripPreproc Whiel.Benchmark.Example4002
#roundTripPreproc Whiel.Benchmark.Example4037
#roundTripPreproc Whiel.Benchmark.Example4041
