-- Author: Jesse Comer
import Whiel.Concrete.Notation

/-
  Notation round trip for the benchmark corpus. This module
  defines the `#roundTrip` command; the registry generator
  writes one module per corpus input under
  `BenchmarkNotationRoundTrip/Cases/`, each running the
  command on its input, and the aggregate
  `BenchmarkNotationRoundTripCases.lean`.

  A relation name renders as the text the concrete notation
  reads back as that name, so a printed program is a
  program the notation accepts. `#roundTrip N` states that
  for one corpus input: it renders `N.inputSchema`,
  `N.inputPre`, `N.inputCmd` and `N.inputPost` with the
  library printers, re-reads the rendered text through
  `programSch!`, `programAssert!` and `programCmd!`, and
  emits the equations between what came back and what the
  input file declares.

  Key declarations include:
    * `BenchmarkNotationRoundTrip.schemaSource`
    * the `#roundTrip` command

  The command equation is closed by the library lemma
  `Whiel.Cmd.eq_of_toRaw_eq`: raw syntax determines a typed
  command, so two commands over one schema with the same
  raw form are equal.

  The rendering step runs in the elaborator, so nothing is
  transcribed by hand and no pinned copy of a corpus
  program can drift from the corpus. The emitted equations
  are ordinary proofs the kernel checks, so a printer that
  renders a name the notation reads back as a different
  name fails this module rather than passing it.

  The preprocessed side of a smaller subset round trips in
  the companion module
  `Whiel/Synthesis/Tests/BenchmarkPreprocRoundTrip.lean`,
  which is separate because its obligations are kernel
  checks over the preprocessor's own output schema and cost
  an order of magnitude more than these.

  Commands and assertions over `ProgramNames` are covered.
  The preprocessed loop over `WhielNames` is display-only:
  the notation has no lifted command form (`whielCmd!` is
  the `IndexAlphaName` style, and `programCmd!` fixes the
  `ProgramNames` style), so a `WhielNames` command has
  nothing to be read back by. The parseable form of a
  `WhielNames` clause is the canonical constructor-complete
  source of `FixedAmbient.SurfaceSyntax`, which is checked
  where it is defined.
-/

------------------------------------------------------------
-- Round-Trip Support
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkNotationRoundTrip

open Whiel.Concrete

/-
  The `programSch!` entry list of one input schema. This is
  `UnnamedSchema.pretty` without its enclosing braces, so
  the round trip exercises the schema printer itself.
-/
def schemaSource
    (Γ : UnnamedSchema ProgramNames) : String :=
  DBTPretty.finsetBody (UnnamedSchema.prettySym Γ)
    Γ.syms.attach

end BenchmarkNotationRoundTrip

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- The Round-Trip Command
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkNotationRoundTrip

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term

syntax (name := roundTripCommand)
  "#roundTrip " ident : command

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

/-
  Render one input and emit its round-trip equations.
  Rendering evaluates the library printers while
  elaborating, which needs the compiler, so the elaborator
  itself is `unsafe` and is registered through the opaque
  wrapper below. Only the rendered text comes from that
  evaluation: every claim this command makes is an ordinary
  proof term the kernel checks.
-/
unsafe def elabRoundTripUnsafe :
    CommandElab := fun stx => do
  match stx with
  | `(#roundTrip $ns:ident) => do
      let base := ns.getId
      let schemaId := mkIdent (base ++ `inputSchema)
      let preId := mkIdent (base ++ `inputPre)
      let cmdId := mkIdent (base ++ `inputCmd)
      let postId := mkIdent (base ++ `inputPost)
      let schemaText := (base ++ `inputSchema).toString
      let schemaFn := mkIdent ``schemaSource
      let cmdEq := mkIdent ``Whiel.Cmd.eq_of_toRaw_eq
      let (schemaBody, preBody, cmdBody, postBody) ←
        liftTermElabM do
          let stringType := Lean.mkConst ``String
          let render (t : Term) : TermElabM String :=
            Term.evalTerm String stringType t
          let schemaBody ← render
            (← `($schemaFn $schemaId))
          let preBody ← render
            (← `(Whiel.AssertExpr.pretty $preId))
          let cmdBody ← render
            (← `(Whiel.Cmd.pretty $cmdId))
          let postBody ← render
            (← `(Whiel.AssertExpr.pretty $postId))
          pure (schemaBody, preBody, cmdBody, postBody)
      let schemaStx ←
        parseTerm ("programSch![" ++ schemaBody ++ "]")
      let preStx ←
        parseTerm ("programAssert![" ++ preBody ++ "]")
      let postStx ←
        parseTerm ("programAssert![" ++ postBody ++ "]")
      let cmdStx ←
        parseTerm
          ("programCmd![{ ExecSchema: " ++ schemaText ++
            " }{" ++ cmdBody ++ "}]")
      elabCommand (← `(command|
        example :
            UnnamedSchema.extensionOf
                ($schemaStx :
                  UnnamedSchema
                    Whiel.Concrete.ProgramNames)
                $schemaId ∧
              UnnamedSchema.extensionOf $schemaId
                ($schemaStx :
                  UnnamedSchema
                    Whiel.Concrete.ProgramNames) := by
          decide))
      elabCommand (← `(command|
        example :
            ($preStx :
              Whiel.AssertExpr Whiel.Concrete.Data
                $schemaId) = $preId := by
          rfl))
      elabCommand (← `(command|
        example :
            ($postStx :
              Whiel.AssertExpr Whiel.Concrete.Data
                $schemaId) = $postId := by
          rfl))
      elabCommand (← `(command|
        example :
            ($cmdStx :
              Whiel.Cmd Whiel.Concrete.Data
                $schemaId) = $cmdId :=
          $cmdEq (by decide +kernel)))
  | _ => throwUnsupportedSyntax

@[implemented_by elabRoundTripUnsafe]
opaque elabRoundTripImpl : CommandElab

@[command_elab roundTripCommand]
def elabRoundTrip : CommandElab :=
  elabRoundTripImpl

end BenchmarkNotationRoundTrip

end Tests

end Synthesis

end Whiel
