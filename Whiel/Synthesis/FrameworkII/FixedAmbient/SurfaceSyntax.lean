-- Author: Jesse Comer
import Whiel.Concrete.WhielNames.SurfaceSyntax
import Whiel.AssertExpr.Syntax
import Whiel.Synthesis.FrameworkII.SurfaceParser

/-
  Parseable clause source for the fixed-ambient Whiel name
  carrier.

  Canonical source is separate from both opaque solver keys
  and human presentation. Relation identifiers encode every
  constructor and internal index. The formula renderer walks
  Lean's existing guard syntax directly; there is no second
  formula AST.

  `display` is the same formula rendered for a reader, and
  it names a relation the way the input notation spells it
  (`WhielNames.spell`), so everything the agent reads uses
  one convention. It is never a source authority: the
  parseable form is `source`.
-/

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace SurfaceSyntax

open Concrete

------------------------------------------------------------
-- Canonical Relation Identifiers
------------------------------------------------------------

/- Parseable, constructor-complete relation source. -/
abbrev nameSource :=
  Concrete.WhielNames.SurfaceSyntax.source

/- Decode one canonical fixed-ambient relation source. -/
abbrev parseName :=
  Concrete.WhielNames.SurfaceSyntax.parse

@[simp] theorem parseName_nameSource
    (name : WhielNames) :
    parseName (nameSource name) = .ok name :=
  Concrete.WhielNames.SurfaceSyntax.parse_source name

instance : SurfaceParser.NameCodec WhielNames where
  parseName := parseName

------------------------------------------------------------
-- Canonical Formula Source
------------------------------------------------------------

private def hexDigit (value : Nat) : Char :=
  if value < 10 then
    Char.ofNat ('0'.toNat + value)
  else
    Char.ofNat ('a'.toNat + value - 10)

private def sourceChar (value : Char) : List Char :=
  if value = '"' then
    ['\\', '"']
  else if value = '\\' then
    ['\\', '\\']
  else if value.toNat <= 31 || value.toNat = 127 then
    ['\\', 'x', hexDigit (value.toNat / 16),
      hexDigit (value.toNat % 16)]
  else
    [value]

private def sourceData : Data -> String
| .num value => toString value
| .str value =>
    "\"" ++
      String.ofList (value.toList.flatMap sourceChar) ++
      "\""
| .bool value => toString value

private def sourceSelection : Sel Data -> String
| .eqIdx left right =>
    "#" ++ toString left ++ " = #" ++ toString right
| .eqConst index value =>
    "#" ++ toString index ++ " = " ++ sourceData value
| .and left right =>
    "(" ++ sourceSelection left ++ " ∧ " ++
      sourceSelection right ++ ")"
| .or left right =>
    "(" ++ sourceSelection left ++ " ∨ " ++
      sourceSelection right ++ ")"
| .not selection =>
    "¬(" ++ sourceSelection selection ++ ")"

private def joinIndices (indices : List Nat) : String :=
  String.intercalate "," (indices.map toString)

private def sourceExpressionWith
    (renderName : WhielNames -> String) :
    RawRAExpr WhielNames Data -> String
| .top => "⊤"
| .empty arity => "∅[" ++ toString arity ++ "]"
| .rel relation => renderName relation
| .single value => "{" ++ sourceData value ++ "}"
| .select selection expression =>
    "σ[" ++ sourceSelection selection ++ "] (" ++
      sourceExpressionWith renderName expression ++ ")"
| .proj indices expression =>
    "π[" ++ joinIndices indices ++ "] (" ++
      sourceExpressionWith renderName expression ++ ")"
| .prod left right =>
    "(" ++ sourceExpressionWith renderName left ++
      " × " ++ sourceExpressionWith renderName right ++ ")"
| .union left right =>
    "(" ++ sourceExpressionWith renderName left ++
      " ∪ " ++
      sourceExpressionWith renderName right ++ ")"
| .diff left right =>
    "(" ++ sourceExpressionWith renderName left ++
      " ∖ " ++
      sourceExpressionWith renderName right ++ ")"

private def rawSourceWith
    (renderName : WhielNames -> String) :
    RawGuard WhielNames Data -> String
| .«true» => "true"
| .«false» => "false"
| .eq left right =>
    "(" ++ sourceExpressionWith renderName left ++
      " = " ++ sourceExpressionWith renderName right ++ ")"
| .subset left right =>
    "(" ++ sourceExpressionWith renderName left ++
      " ⊆ " ++
      sourceExpressionWith renderName right ++ ")"
| .eqEmptyRight expression =>
    "(" ++ sourceExpressionWith renderName expression ++
      " = ∅)"
| .eqEmptyLeft expression =>
    "(∅ = " ++
      sourceExpressionWith renderName expression ++
      ")"
| .subsetEmptyRight expression =>
    "(" ++ sourceExpressionWith renderName expression ++
      " ⊆ ∅)"
| .subsetEmptyLeft expression =>
    "(∅ ⊆ " ++
      sourceExpressionWith renderName expression ++
      ")"
| .and left right =>
    "(" ++ rawSourceWith renderName left ++ " ∧ " ++
      rawSourceWith renderName right ++ ")"
| .or left right =>
    "(" ++ rawSourceWith renderName left ++ " ∨ " ++
      rawSourceWith renderName right ++ ")"
| .not formula =>
    "(¬(" ++ rawSourceWith renderName formula ++ "))"

/- Canonical, parseable source for one raw clause. -/
def rawSource
    (formula : RawGuard WhielNames Data) : String :=
  rawSourceWith nameSource formula

/- Canonical source for one checked clause. -/
def source
    {Gamma : UnnamedSchema WhielNames}
    (formula : QFAssertExpr Data Gamma) : String :=
  rawSource formula.toRaw

/-
  Human display, never used as source authority. Relations
  are named in the notation spelling, the one convention
  everything the agent reads uses.
-/
def display
    {Gamma : UnnamedSchema WhielNames}
    (formula : QFAssertExpr Data Gamma) : String :=
  rawSourceWith WhielNames.spell formula.toRaw

/- Parse one fixed-ambient clause with explicit bounds. -/
def parseWithLimits
    (limits : SurfaceParser.Limits)
    (text : String) :
    Except SurfaceParser.Error
      (RawGuard WhielNames Data) :=
  SurfaceParser.parseWithLimits limits text

/- Parse one fixed-ambient clause with production bounds. -/
def parse (text : String) :
    Except SurfaceParser.Error
      (RawGuard WhielNames Data) :=
  SurfaceParser.parse text

end SurfaceSyntax
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel
