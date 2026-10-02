-- Author: Jesse Comer
import Whiel.Concrete.Data
import Whiel.Concrete.WhielNames
import Whiel.AssertExpr.Syntax

/-
  Lean-notation source for fixed-ambient clauses.

  `render` prints a checked clause exactly as `qfAssert!`
  reads it over an `UnnamedSchema WhielNames`: program
  symbols as `R` or `R_n`, auxiliaries as `T_aux` or
  `T_aux_n` for a positive index `n`, and prophecy copies
  with the postfix `∞`. Index zero has no suffix, matching
  the one spelling the notation accepts. It is the inverse
  of the notation grammar and is separate from the
  canonical ASCII surface syntax of `SurfaceSyntax`.

  A name is spelled by the carrier's own
  `ProgramNames.spell` and `WhielNames.spell`, not by a
  copy of them here, and `renderName_*` pins that. A flag
  is spelled `flag_i_n` like every other name, both
  numerals canonical and neither elided, and the notation
  reads exactly that form back; no base name can produce
  it, since a base is purely alphabetical. Certificates
  built from the current corpus contain no flag, but a
  clause that mentions one now renders as source the
  notation parses rather than failing closed.

  Key declarations include:
    * `ClauseNotation.renderName`
    * `ClauseNotation.renderRaw`
    * `ClauseNotation.render`
    * `ClauseNotation.renderProposalDeclaration`
-/

------------------------------------------------------------
-- Relation Names and Literals
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace ClauseNotation

open Concrete

/-
  Spell a program name as `X`, `X_n`, `X_aux`, `X_aux_n`,
  or `flag_i_n`. The text is the carrier's own
  `ProgramNames.spell`, so a relation has one spelling
  rather than a second copy of it here, and every
  constructor is total: nothing in this module fails
  closed on a name any more.
-/
def renderProgramName :
    ProgramNames → Except String String
| .programSymbol base index =>
    .ok (ProgramNames.spell (.programSymbol base index))
| .auxiliarySymbol base index =>
    .ok (ProgramNames.spell (.auxiliarySymbol base index))
| .flagSymbol id index =>
    .ok (ProgramNames.spell (.flagSymbol id index))

/- Spell a relation name; prophecy copies end in `∞`. -/
def renderName : WhielNames → Except String String
| .ordinary name => renderProgramName name
| .prophecy name => do
    let text ← renderProgramName name
    pure (text ++ "∞")

/-
  What this module emits is exactly the carrier's spelling,
  on every constructor.
-/
theorem renderName_ordinary_programSymbol
    (base : AlphaString)
    (index : Nat) :
    renderName (.ordinary (.programSymbol base index)) =
      .ok (WhielNames.spell
        (.ordinary (.programSymbol base index))) :=
  rfl

theorem renderName_ordinary_auxiliarySymbol
    (base : AlphaString)
    (index : Nat) :
    renderName (.ordinary (.auxiliarySymbol base index)) =
      .ok (WhielNames.spell
        (.ordinary (.auxiliarySymbol base index))) :=
  rfl

theorem renderName_prophecy_programSymbol
    (base : AlphaString)
    (index : Nat) :
    renderName (.prophecy (.programSymbol base index)) =
      .ok (WhielNames.spell
        (.prophecy (.programSymbol base index))) :=
  rfl

theorem renderName_prophecy_auxiliarySymbol
    (base : AlphaString)
    (index : Nat) :
    renderName (.prophecy (.auxiliarySymbol base index)) =
      .ok (WhielNames.spell
        (.prophecy (.auxiliarySymbol base index))) :=
  rfl

theorem renderName_ordinary_flagSymbol
    (id index : Nat) :
    renderName (.ordinary (.flagSymbol id index)) =
      .ok (WhielNames.spell
        (.ordinary (.flagSymbol id index))) :=
  rfl

theorem renderName_prophecy_flagSymbol
    (id index : Nat) :
    renderName (.prophecy (.flagSymbol id index)) =
      .ok (WhielNames.spell
        (.prophecy (.flagSymbol id index))) :=
  rfl

/- Spell a literal as the notation reads it. -/
def renderData : Data → String
| .num value => toString value
| .str value => value.quote
| .bool value => if value then "true" else "false"

/- Spell a selection condition. -/
def renderSelection : Sel Data → String
| .eqIdx left right =>
    "#" ++ toString left ++ " = #" ++ toString right
| .eqConst index value =>
    "#" ++ toString index ++ " = " ++ renderData value
| .and left right =>
    "(" ++ renderSelection left ++ " ∧ " ++
      renderSelection right ++ ")"
| .or left right =>
    "(" ++ renderSelection left ++ " ∨ " ++
      renderSelection right ++ ")"
| .not selection =>
    "¬(" ++ renderSelection selection ++ ")"

end ClauseNotation
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Expressions and Clauses
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace ClauseNotation

open Concrete

/- Spell a raw RA expression; compound forms are bracketed. -/
def renderExpression :
    RawRAExpr WhielNames Data → Except String String
| .top => .ok "⊤"
| .empty arity => .ok ("∅[" ++ toString arity ++ "]")
| .rel relation => renderName relation
| .single value => .ok ("{" ++ renderData value ++ "}")
| .select selection expression => do
    let inner ← renderExpression expression
    pure ("σ[" ++ renderSelection selection ++ "] (" ++
      inner ++ ")")
| .proj indices expression => do
    let inner ← renderExpression expression
    pure ("π[" ++
      String.intercalate ", " (indices.map toString) ++
      "] (" ++ inner ++ ")")
| .prod left right => do
    let leftText ← renderExpression left
    let rightText ← renderExpression right
    pure ("(" ++ leftText ++ " × " ++ rightText ++ ")")
| .union left right => do
    let leftText ← renderExpression left
    let rightText ← renderExpression right
    pure ("(" ++ leftText ++ " ∪ " ++ rightText ++ ")")
| .diff left right => do
    let leftText ← renderExpression left
    let rightText ← renderExpression right
    pure ("(" ++ leftText ++ " ∖ " ++ rightText ++ ")")

/-
  Spell a raw clause. Bare `∅` appears only in the raw
  empty forms, where the guard grammar infers its arity.
-/
def renderRaw :
    RawGuard WhielNames Data → Except String String
| .«true» => .ok "true"
| .«false» => .ok "false"
| .eq left right => do
    let leftText ← renderExpression left
    let rightText ← renderExpression right
    pure ("(" ++ leftText ++ " = " ++ rightText ++ ")")
| .subset left right => do
    let leftText ← renderExpression left
    let rightText ← renderExpression right
    pure ("(" ++ leftText ++ " ⊆ " ++ rightText ++ ")")
| .eqEmptyRight expression => do
    let text ← renderExpression expression
    pure ("(" ++ text ++ " = ∅)")
| .eqEmptyLeft expression => do
    let text ← renderExpression expression
    pure ("(∅ = " ++ text ++ ")")
| .subsetEmptyRight expression => do
    let text ← renderExpression expression
    pure ("(" ++ text ++ " ⊆ ∅)")
| .subsetEmptyLeft expression => do
    let text ← renderExpression expression
    pure ("(∅ ⊆ " ++ text ++ ")")
| .and left right => do
    let leftText ← renderRaw left
    let rightText ← renderRaw right
    pure ("(" ++ leftText ++ " ∧ " ++ rightText ++ ")")
| .or left right => do
    let leftText ← renderRaw left
    let rightText ← renderRaw right
    pure ("(" ++ leftText ++ " ∨ " ++ rightText ++ ")")
| .not formula => do
    let text ← renderRaw formula
    pure ("(¬(" ++ text ++ "))")

/- Spell a checked clause for `qfAssert![ ... ]`. -/
def render
    {Gamma : UnnamedSchema WhielNames}
    (formula : QFAssertExpr Data Gamma) :
    Except String String :=
  renderRaw formula.toRaw

/-
  One `Proposal.lean` clause declaration in the layout of
  `Benchmark/Example0001/Certificate/Proposal.lean`.
-/
def renderProposalDeclaration
    {Gamma : UnnamedSchema WhielNames}
    (name : String)
    (schemaSource : String)
    (formula : QFAssertExpr Data Gamma) :
    Except String String := do
  if name.isEmpty then
    throw "proposal declaration name must be nonempty"
  if schemaSource.isEmpty then
    throw "proposal schema source must be nonempty"
  let text ← render formula
  pure ("def " ++ name ++ " :\n    QFAssertExpr Data " ++
    schemaSource ++ " :=\n  qfAssert![\n    " ++ text ++
    "\n  ]")

end ClauseNotation
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel
