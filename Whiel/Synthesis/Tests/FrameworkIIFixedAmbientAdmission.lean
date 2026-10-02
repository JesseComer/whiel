-- Author: Jesse Comer
import Whiel.Concrete.Notation
import
  Whiel.Synthesis.FrameworkII.FixedAmbient.Admission

set_option linter.hashCommand false

/-
  Executable checks for fixed-ambient clause source,
  qfAssert elaboration, and structural admission identity.
-/

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIFixedAmbientAdmission

open Concrete
open FrameworkII.FixedAmbient

private def baseR : AlphaString := ⟨"R", by decide⟩
private def baseT : AlphaString := ⟨"T", by decide⟩

private def ordinaryR : WhielNames :=
  .ordinary (.programSymbol baseR 0)

private def ordinaryRNext : WhielNames :=
  .ordinary (.programSymbol baseR 1)

private def auxiliaryT : WhielNames :=
  .ordinary (.auxiliarySymbol baseT 0)

private def prophecyR : WhielNames :=
  .prophecy (.programSymbol baseR 0)

private def prophecyTNext : WhielNames :=
  .prophecy (.auxiliarySymbol baseT 2)

private def ordinaryFlag : WhielNames :=
  .ordinary (.flagSymbol 1 0)

private def prophecyFlagNext : WhielNames :=
  .prophecy (.flagSymbol 1 2)

private def ambientSchema : UnnamedSchema WhielNames where
  syms :=
    { ordinaryR, ordinaryRNext, auxiliaryT,
      prophecyR, prophecyTNext }
  arity := fun _ => 1

------------------------------------------------------------
-- Relation Source Codec
------------------------------------------------------------

#guard SurfaceSyntax.nameSource ordinaryR == "op_zR"

#guard SurfaceSyntax.nameSource ordinaryRNext == "op_szR"

#guard SurfaceSyntax.nameSource auxiliaryT == "oa_zT"

#guard SurfaceSyntax.nameSource prophecyR == "yp_zR"

#guard SurfaceSyntax.nameSource prophecyTNext == "ya_sszT"

#guard SurfaceSyntax.parseName
    (SurfaceSyntax.nameSource ordinaryR) ==
  .ok ordinaryR

#guard SurfaceSyntax.parseName
    (SurfaceSyntax.nameSource ordinaryRNext) ==
  .ok ordinaryRNext

#guard SurfaceSyntax.parseName
    (SurfaceSyntax.nameSource auxiliaryT) ==
  .ok auxiliaryT

#guard SurfaceSyntax.parseName
    (SurfaceSyntax.nameSource prophecyR) ==
  .ok prophecyR

#guard SurfaceSyntax.parseName
    (SurfaceSyntax.nameSource prophecyTNext) ==
  .ok prophecyTNext

#guard SurfaceSyntax.nameSource ordinaryR !=
  WhielNames.encode ordinaryR

------------------------------------------------------------
-- Reserved Flag Names
------------------------------------------------------------

#guard SurfaceSyntax.nameSource ordinaryFlag == "of_z1"

#guard SurfaceSyntax.nameSource prophecyFlagNext ==
  "yf_ssz1"

#guard SurfaceSyntax.parseName
    (SurfaceSyntax.nameSource ordinaryFlag) ==
  .ok ordinaryFlag

#guard SurfaceSyntax.parseName
    (SurfaceSyntax.nameSource prophecyFlagNext) ==
  .ok prophecyFlagNext

#guard WhielNames.encode ordinaryFlag == "o:f::1"

#guard WhielNames.encode prophecyFlagNext == "y:f:ss:1"

#guard WhielNames.parse? (WhielNames.encode ordinaryFlag) ==
  some ordinaryFlag

#guard WhielNames.parse?
    (WhielNames.encode prophecyFlagNext) ==
  some prophecyFlagNext

#guard WhielNames.spell ordinaryFlag == "flag_1_0"

#guard WhielNames.spell prophecyFlagNext ==
  "flag_1_2∞"

#guard !(ProgramNames.flagSymbol 1 0).IsRawInput

#guard !(ProgramNames.programSymbol baseR 1).IsRawInput

#guard (ProgramNames.programSymbol baseR 0).IsRawInput

private def rawInputSchema :
    UnnamedSchema ProgramNames where
  syms := {.programSymbol baseR 0, .auxiliarySymbol baseT 0}
  arity := fun _ => 1

private def flaggedInputSchema :
    UnnamedSchema ProgramNames where
  syms := {.programSymbol baseR 0, .flagSymbol 1 0}
  arity := fun _ => 1

private def indexedInputSchema :
    UnnamedSchema ProgramNames where
  syms := {.programSymbol baseR 0, .programSymbol baseR 1}
  arity := fun _ => 1

example : rawInputSchema.RawIndexZero := by
  decide

example : ¬ flaggedInputSchema.RawIndexZero := by
  decide

example : ¬ indexedInputSchema.RawIndexZero := by
  decide

#guard rawInputSchema.RawIndexZero

#guard !flaggedInputSchema.RawIndexZero

------------------------------------------------------------
-- Formula Source And qfAssert
------------------------------------------------------------

private def rawFormula : RawGuard WhielNames Data :=
  .and
    (.eq
      (.union (.rel ordinaryR) (.rel prophecyR))
      (.diff (.rel ordinaryR) (.rel auxiliaryT)))
    (.not
      (.subset
        (.select (.eqConst 0 (.num 1))
          (.rel prophecyTNext))
        (.proj [0]
          (.prod (.rel ordinaryRNext)
            (.single (.num 2))))))

private def formula : QFAssertExpr Data ambientSchema :=
  rawFormula.toGuard (Γ := ambientSchema)

private def formulaSource : String :=
  SurfaceSyntax.source formula

#guard SurfaceSyntax.parse formulaSource ==
  .ok formula.toRaw

private def notationFormula :
    QFAssertExpr Data ambientSchema :=
  qfAssert![
    ((op_zR ∪ yp_zR) = (op_zR ∖ oa_zT)) ∧
    ¬(σ[#0 = 1] ya_sszT ⊆
      π[0] (op_szR × {2}))]

#guard notationFormula == formula

private def escapedRaw : RawGuard WhielNames Data :=
  let value := Data.str <|
    String.ofList ['a', '\r', '"', '\\', '\u03bb']
  .eq (.single value) (.single value)

private def escapedFormula :
    QFAssertExpr Data ambientSchema :=
  escapedRaw.toGuard (Γ := ambientSchema)

#guard SurfaceSyntax.parse
    (SurfaceSyntax.source escapedFormula) ==
  .ok escapedFormula.toRaw

------------------------------------------------------------
-- Structural Admission Authority
------------------------------------------------------------

private def admissionFixedPoint : Bool :=
  match admitClause ambientSchema formulaSource with
  | .error _ => Bool.false
  | .ok first =>
      match admitClause ambientSchema
          first.canonicalSource with
      | .error _ => Bool.false
      | .ok second =>
          first.identity == second.identity &&
          first.identityJson == second.identityJson &&
          first.canonicalSource == second.canonicalSource &&
          first.formula == second.formula

#guard admissionFixedPoint

private def admittedMetadata : Bool :=
  match admitClause ambientSchema formulaSource with
  | .error _ => Bool.false
  | .ok clause =>
      clause.identity ==
          Runtime.ReferenceProposal.identity formula &&
        clause.canonicalSource == formulaSource &&
        clause.relationKeys ==
          formula.symbols.sort.map WhielNames.encode &&
        clause.mentionsProphecy &&
        clause.minimumLevel == 1

#guard admittedMetadata

private def whitespaceNormalizes : Bool :=
  match admitClause ambientSchema
      " ( op_zR   =   yp_zR ) " with
  | .error _ => Bool.false
  | .ok clause =>
      clause.canonicalSource == "(op_zR = yp_zR)"

#guard whitespaceNormalizes

private def alteredSourceChangesIdentity : Bool :=
  match admitClause ambientSchema "op_zR = yp_zR",
      admitClause ambientSchema "op_zR = op_zR" with
  | .ok left, .ok right => left.identity != right.identity
  | _, _ => Bool.false

#guard alteredSourceChangesIdentity

private def batchDeduplicates : Bool :=
  match admitClauseJson ambientSchema
      [formulaSource, formulaSource] with
  | .ok clauses => clauses.length == 1
  | .error _ => Bool.false

#guard batchDeduplicates

/-
  Pass 7.7b: the parser applies no bound of its own.

  `FrameworkII.SurfaceParser.Limits` is absent by default, so admission
  is unbounded; a run that sets the host limit
  `clause_text_bytes` drives both parse bounds from that one
  value. Reaching either is a disagreement with the host —
  which refuses an oversized clause before submitting it —
  and so fails the batch as infrastructure, never as a
  correctable defect of the clause.
-/
private def defaultLimitsAreAbsent : Bool :=
  (({} : FrameworkII.SurfaceParser.Limits).maxChars? == none) &&
    (({} : FrameworkII.SurfaceParser.Limits).maxTokens? == none)

#guard defaultLimitsAreAbsent

#guard FrameworkII.SurfaceParser.Limits.ofClauseTextBytes? none ==
  ({} : FrameworkII.SurfaceParser.Limits)

#guard FrameworkII.SurfaceParser.Limits.ofClauseTextBytes? (some 8) ==
  { maxChars? := some 8, maxTokens? := some 8 }

/- A long clause admits under no host limit at all. -/
private def longSource : String :=
  "(op_zR = " ++
    String.join (List.replicate 400 "(yp_zR ∪ ") ++
    "yp_zR" ++ String.join (List.replicate 400 ")") ++ ")"

private def longSourceAdmits : Bool :=
  match admitClause ambientSchema longSource with
  | .ok clause => clause.canonicalSource.length > 3600
  | .error _ => Bool.false

#guard longSource.length > 3600

#guard longSourceAdmits

/- The same clause under a byte budget it exceeds is an
   infrastructure failure, not a clause diagnostic. -/
private def overHostLimitIsInfrastructure : Bool :=
  match admitClause ambientSchema longSource
      (FrameworkII.SurfaceParser.Limits.ofClauseTextBytes? (some 16)) with
  | .error (.infrastructure _) => Bool.true
  | _ => Bool.false

#guard overHostLimitIsInfrastructure

/- Within the budget the very same call admits. -/
private def withinHostLimitAdmits : Bool :=
  match admitClause ambientSchema formulaSource
      (FrameworkII.SurfaceParser.Limits.ofClauseTextBytes?
        (some 4096)) with
  | .ok clause => clause.canonicalSource == formulaSource
  | .error _ => Bool.false

#guard withinHostLimitAdmits

/- A genuinely malformed clause is still correctable. -/
private def malformedStaysCorrectable : Bool :=
  match admitClause ambientSchema "not a clause"
      (FrameworkII.SurfaceParser.Limits.ofClauseTextBytes?
        (some 4096)) with
  | .error (.correctable diagnostic) =>
      diagnostic.code == "clause_syntax_error" ||
        diagnostic.code == "clause_lexical_error"
  | _ => Bool.false

#guard malformedStaysCorrectable

/- The batch entry point carries the same limits. -/
private def batchRespectsTheHostLimit : Bool :=
  match admitClauses ambientSchema [longSource]
      (FrameworkII.SurfaceParser.Limits.ofClauseTextBytes? (some 16)) with
  | .error (.infrastructure _) => Bool.true
  | _ => Bool.false

#guard batchRespectsTheHostLimit

end FrameworkIIFixedAmbientAdmission
end Tests
end Synthesis
end Whiel
