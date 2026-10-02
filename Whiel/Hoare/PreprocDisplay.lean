-- Author: Jesse Comer
import Whiel.Cmd.PrettyPrint
import Whiel.Hoare.ProphecySchema

/-
  Readable display of one preprocessing result.

  A corpus input file states a Hoare triple and hands it to
  `Hoare.preprocess`. This module renders both halves of
  that step together: the triple the file states, and the
  framed single-loop triple preprocessing produced from it,
  over the flag extension it drew. For production inputs,
  the displayed schema includes the prophecy extension
  used by Framework II. Relation
  names go through the carrier's `Spelling` instance, so a
  displayed program over a carrier with a concrete notation
  is that notation's own text.

  Key declarations include:
    * `Whiel.Hoare.Preproc.pretty`
    * `Whiel.Hoare.Preproc.display`

  The display is untrusted reader assistance. Nothing reads
  it back, and no identity, digest, or certificate is
  computed from it.
-/

------------------------------------------------------------
-- Preprocessing Display
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace Preproc

/- Choose the schema shown to readers of each carrier. -/
class DisplaySchema (A : Type) [RelationNames A] where
  render : UnnamedSchema A -> Finset A -> String

/- Generic preprocessing has no prophecy naming rule. -/
instance (priority := low) {A : Type} [RelationNames A] :
    DisplaySchema A where
  render schema _ := schema.pretty

/- Production inputs show the existing computed extension. -/
instance : DisplaySchema Concrete.ProgramNames where
  render schema assigned :=
    (Hoare.prophecySchema schema assigned).pretty

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [DisplaySchema A]

/- Render one labelled block of the display. -/
private def block (label body : String) : String :=
  label ++ ":\n" ++ body ++ "\n"

/-
  Render an input triple above the framed single-loop triple
  that preprocessing produced from it.

  Production schemas include ordinary copies of the flag
  extension and prophecy copies of loop-assigned relations.
  Other carriers retain their output schema. The framed
  loop is shown as
  the four components the transformation actually returns:
  the prefix that establishes the loop head, the loop
  itself, and the suffix the closing assertion is the
  weakest precondition of.
-/
def pretty
    {inputPre : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    {inputPost : AssertExpr D Γ}
    (P : Preproc inputPre inputCmd inputPost) :
    String :=
  block "schema" Γ.pretty ++
    "\n" ++
    block "original precondition" inputPre.pretty ++
    block "original command" inputCmd.pretty ++
    block "original postcondition" inputPost.pretty ++
    "\n" ++
    block "preprocessed schema"
      (DisplaySchema.render P.outSchema
        P.loopBody.assignedSymbols) ++
    block "preprocessed precondition" P.loopPre.pretty ++
    block "preprocessed prefix" P.sourcePrefix.pretty ++
    block "preprocessed loop" P.loopCmd.pretty ++
    block "preprocessed suffix" P.sourceClose.pretty ++
    block "preprocessed postcondition" P.loopPost.pretty

/- Render a preprocessing result directly in `#eval`. -/
def display
    {inputPre : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    {inputPost : AssertExpr D Γ}
    (P : Preproc inputPre inputCmd inputPost) :
    DBTPretty.Display :=
  DBTPretty.display ("\n" ++ P.pretty)

end Preproc

end Hoare

end Whiel
