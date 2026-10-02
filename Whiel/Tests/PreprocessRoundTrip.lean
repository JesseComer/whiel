-- Author: Jesse Comer
import Whiel.Preprocess.Transfer
import Whiel.Concrete.Notation

/-
  Notation round trip for the preprocessor's own output.

  A flag is a relation name like any other, and it now has a
  spelling the concrete notation reads back as that name, so
  a preprocessed program over the flag extension is a
  program the notation accepts. `#preprocRoundTrip Γ C`
  renders `Γ` and `C` with the library printers, re-reads
  the rendered text through `programSch!` and `programCmd!`,
  and emits the equations between what came back and what
  was declared.

  The rendering step runs in the elaborator, so nothing is
  transcribed by hand and no pinned copy of a preprocessed
  program can drift from the transformation. The emitted
  equations are ordinary proofs the kernel checks, so a
  spelling the notation reads back as a different name
  fails this module rather than passing it.

  The command equation is closed by the library lemma
  `Whiel.Cmd.eq_of_toRaw_eq`: raw syntax determines a typed
  command, so two commands over one schema with the same raw
  form are equal. The guard equation is closed by
  `Whiel.Guard.eq_of_toRaw_eq` for the same reason.

  Two round trips are run on every corpus entry.

  `#preprocRoundTrip Γ C` is the whole-command trip, and it
  is run on `Cmd.clean` of the assembled unfolding rather
  than on the unfolding itself: `Framed.unfold` writes the
  prefix, the loop and the suffix as `P; (W; S)`, so when
  the prefix is itself a sequence the assembled command is
  left-nested at that one seam, while the notation's `;`
  reads a printed sequence right-nested.

  `#preprocFramedRoundTrip Γ L` is the component trip, and
  it needs no such repair: it round trips the framed loop's
  `init`, `body` and `close` separately through
  `programCmd!` and its `guard` through `programQF!`, all
  exactly as the transformation leaves them. The
  transformation's own final clean is the last thing
  `normalize` does, so these four are the note's step 6
  output verbatim --- no extra clean and no seam --- and the
  component trip is what shows that that output is itself
  notation the library reads back.
-/

------------------------------------------------------------
-- Round-Trip Support
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace PreprocessRoundTrip

open Whiel.Concrete

/-
  The `programSch!` entry list of one schema. This is
  `UnnamedSchema.pretty` without its enclosing braces, so
  the round trip exercises the schema printer itself.
-/
def schemaSource
    (Γ : UnnamedSchema ProgramNames) : String :=
  DBTPretty.finsetBody (UnnamedSchema.prettySym Γ)
    Γ.syms.attach

end PreprocessRoundTrip

end Tests

end Whiel

------------------------------------------------------------
-- The Round-Trip Command
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace PreprocessRoundTrip

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term

syntax (name := preprocRoundTripCommand)
  "#preprocRoundTrip " ident ident : command

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
  Render one preprocessed program and emit its round-trip
  equations. Rendering evaluates the library printers while
  elaborating, which needs the compiler, so the elaborator
  itself is `unsafe` and is registered through the opaque
  wrapper below. Only the rendered text comes from that
  evaluation.
-/
unsafe def elabPreprocRoundTripUnsafe :
    CommandElab := fun stx => do
  match stx with
  | `(#preprocRoundTrip $sch:ident $cmd:ident) => do
      let schemaText := sch.getId.toString
      let schemaFn := mkIdent ``schemaSource
      let cmdEq := mkIdent ``Whiel.Cmd.eq_of_toRaw_eq
      let (schemaBody, cmdBody) ←
        liftTermElabM do
          let stringType := Lean.mkConst ``String
          let render (t : Term) : TermElabM String :=
            Term.evalTerm String stringType t
          let schemaBody ← render (← `($schemaFn $sch))
          let cmdBody ← render
            (← `(Whiel.Cmd.pretty $cmd))
          pure (schemaBody, cmdBody)
      let schemaStx ←
        parseTerm ("programSch![" ++ schemaBody ++ "]")
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
                $sch ∧
              UnnamedSchema.extensionOf $sch
                ($schemaStx :
                  UnnamedSchema
                    Whiel.Concrete.ProgramNames) := by
          decide))
      elabCommand (← `(command|
        example :
            ($cmdStx :
              Whiel.Cmd Whiel.Concrete.Data $sch) =
              $cmd :=
          $cmdEq (by decide +kernel)))
  | _ => throwUnsupportedSyntax

@[implemented_by elabPreprocRoundTripUnsafe]
opaque elabPreprocRoundTripImpl : CommandElab

@[command_elab preprocRoundTripCommand]
def elabPreprocRoundTrip : CommandElab :=
  elabPreprocRoundTripImpl

syntax (name := preprocFramedRoundTripCommand)
  "#preprocFramedRoundTrip " ident ident : command

/-
  Round trip the four components of one framed loop as the
  transformation leaves them: the prefix, the body and the
  suffix through `programCmd!`, and the guard through
  `programQF!`. No component is cleaned or reassembled
  first, so what round trips here is the output itself.
-/
unsafe def elabPreprocFramedRoundTripUnsafe :
    CommandElab := fun stx => do
  match stx with
  | `(#preprocFramedRoundTrip $sch:ident $loop:ident) => do
      let schemaText := sch.getId.toString
      let cmdEq := mkIdent ``Whiel.Cmd.eq_of_toRaw_eq
      let guardEq := mkIdent ``Whiel.Guard.eq_of_toRaw_eq
      let (initBody, bodyBody, closeBody, guardBody) ←
        liftTermElabM do
          let stringType := Lean.mkConst ``String
          let render (t : Term) : TermElabM String :=
            Term.evalTerm String stringType t
          let initBody ← render
            (← `(Whiel.Cmd.pretty ($loop).init))
          let bodyBody ← render
            (← `(Whiel.Cmd.pretty ($loop).body))
          let closeBody ← render
            (← `(Whiel.Cmd.pretty ($loop).close))
          let guardBody ← render
            (← `(Whiel.Guard.pretty ($loop).guard))
          pure (initBody, bodyBody, closeBody, guardBody)
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
            ($initStx :
              Whiel.Cmd Whiel.Concrete.Data $sch) =
              ($loop).init :=
          $cmdEq (by decide +kernel)))
      elabCommand (← `(command|
        example :
            ($bodyStx :
              Whiel.Cmd Whiel.Concrete.Data $sch) =
              ($loop).body :=
          $cmdEq (by decide +kernel)))
      elabCommand (← `(command|
        example :
            ($closeStx :
              Whiel.Cmd Whiel.Concrete.Data $sch) =
              ($loop).close :=
          $cmdEq (by decide +kernel)))
      elabCommand (← `(command|
        example :
            ($guardStx :
              Whiel.Guard Whiel.Concrete.Data $sch) =
              ($loop).guard :=
          $guardEq (by decide +kernel)))
  | _ => throwUnsupportedSyntax

@[implemented_by elabPreprocFramedRoundTripUnsafe]
opaque elabPreprocFramedRoundTripImpl : CommandElab

@[command_elab preprocFramedRoundTripCommand]
def elabPreprocFramedRoundTrip : CommandElab :=
  elabPreprocFramedRoundTripImpl

end PreprocessRoundTrip

end Tests

end Whiel

------------------------------------------------------------
-- The Preprocessed Corpus
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace PreprocessRoundTrip

open Whiel.Concrete Whiel.Preprocess

/- Five unary program relations. -/
def base : UnnamedSchema ProgramNames :=
  programSch![ {R, T, U, V, W} (arity: 1) ]

/- Two dependent loops: the two-flag general merge. -/
def progMerge : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { (WHILE R ≠ ∅ DO R := ∅ END) ;
      (WHILE R ≠ ∅ DO U := R END) } ]

/- A loop in one branch: the one-sided hoist. -/
def progHoist : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { IF T ≠ ∅ THEN
        WHILE R ≠ ∅ DO R := ∅ END
      ELSE
        U := R
      END } ]

/- A loop inside a loop: the general flattening. -/
def progFlatten : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { WHILE T ≠ ∅ DO
        WHILE R ≠ ∅ DO R := ∅ END
      END } ]

/- The note's Section 5 worked example. -/
def progWorked : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { (WHILE T ≠ ∅ DO
        IF U ≠ ∅ THEN
          WHILE R ≠ ∅ DO R := ∅ END
        ELSE
          V := R
        END
      END) ;
      (WHILE W ≠ ∅ DO T := ∅ END) } ]

/- The flag extensions the normalizer computes. -/
def schMerge : UnnamedSchema ProgramNames :=
  flagExt base (normalize progMerge).ids

def schHoist : UnnamedSchema ProgramNames :=
  flagExt base (normalize progHoist).ids

def schFlatten : UnnamedSchema ProgramNames :=
  flagExt base (normalize progFlatten).ids

def schWorked : UnnamedSchema ProgramNames :=
  flagExt base (normalize progWorked).ids

/- The framed loops themselves, as the normalizer built them. -/
def loopMerge : Framed Data schMerge :=
  (normalize progMerge).loop

def loopHoist : Framed Data schHoist :=
  (normalize progHoist).loop

def loopFlatten : Framed Data schFlatten :=
  (normalize progFlatten).loop

def loopWorked : Framed Data schWorked :=
  (normalize progWorked).loop

/-
  The assembled unfoldings, cleaned.

  `Framed.unfold` writes the prefix, the loop and the suffix
  as `P; (W; S)`, so when the prefix is itself a sequence
  the assembled command is left-nested at that one seam,
  while the notation's `;` reads a printed sequence
  right-nested. The pin is therefore on `Cmd.clean` of the
  assembled command: the repository's own right-associating
  skip-removal, applied once more to the whole unfolding
  rather than to its three components separately. Nothing
  about the flags changes --- what is being checked here is
  that a flag prints as text the notation reads back as
  that same flag.

  The component trips below carry no such repair, so the
  transformation's output round trips as it stands.
-/
def cmdMerge : Cmd Data schMerge :=
  (normalize progMerge).loop.unfold.clean

def cmdHoist : Cmd Data schHoist :=
  (normalize progHoist).loop.unfold.clean

def cmdFlatten : Cmd Data schFlatten :=
  (normalize progFlatten).loop.unfold.clean

def cmdWorked : Cmd Data schWorked :=
  (normalize progWorked).loop.unfold.clean

end PreprocessRoundTrip

end Tests

end Whiel

------------------------------------------------------------
-- The Round Trips
------------------------------------------------------------

open Whiel.Tests.PreprocessRoundTrip

set_option linter.hashCommand false
set_option linter.style.setOption false
set_option maxRecDepth 16384

#preprocRoundTrip schMerge cmdMerge
#preprocRoundTrip schHoist cmdHoist
#preprocRoundTrip schFlatten cmdFlatten
#preprocRoundTrip schWorked cmdWorked

#preprocFramedRoundTrip schMerge loopMerge
#preprocFramedRoundTrip schHoist loopHoist
#preprocFramedRoundTrip schFlatten loopFlatten
#preprocFramedRoundTrip schWorked loopWorked
