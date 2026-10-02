-- Author: Jesse Comer
import Whiel.Concrete.Notation
import Whiel.Hoare.ProphecySchema
import Whiel.Synthesis.FrameworkII.FixedAmbient.ClauseNotation

/-
  Pins for the `WhielNames` name style of `qfAssert!` and
  for the Lean-notation clause printer.

  Over a prophecy schema, `R` and `T_aux` are the ordinary
  copies and `R∞`, `T_aux∞` the prophecy copies; positive
  snapshot indices are spelled `R_n`, `T_aux_n`, `R_n∞`, and
  `T_aux_n∞`. Each clause below is checked three ways: its
  raw syntax equals the hand-built raw value, `render`
  prints the expected text, and re-reading that text with
  `qfAssert!` yields the same typed clause, through
  `Guard.eq_of_toRaw_eq` since typed guards have no
  decidable equality.

  Names are checked against the schema at elaboration, not
  by the notation: a positive-index name the schema lacks
  is rejected as an unknown relation.
-/

open Whiel.Concrete
open Whiel.Synthesis.FrameworkII.FixedAmbient

set_option linter.hashCommand false

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIFixedAmbientClauseNotation

------------------------------------------------------------
-- Prophecy Schema
------------------------------------------------------------

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![ {R, U} (arity: 1), T_aux (arity: 2) ]

def rName : ProgramNames :=
  .programSymbol ⟨"R", by decide⟩ 0

def uName : ProgramNames :=
  .programSymbol ⟨"U", by decide⟩ 0

def tAuxName : ProgramNames :=
  .auxiliarySymbol ⟨"T", by decide⟩ 0

def assigned : Finset ProgramNames :=
  {uName, tAuxName}

/- Ordinary `R`, `U`, `T_aux` and prophecy `U∞`, `T_aux∞`. -/
def ambientSchema : UnnamedSchema WhielNames :=
  Hoare.prophecySchema inputSchema assigned

def oR : RawRAExpr WhielNames Data := .rel (.ordinary rName)
def oU : RawRAExpr WhielNames Data := .rel (.ordinary uName)
def oT : RawRAExpr WhielNames Data :=
  .rel (.ordinary tAuxName)
def pU : RawRAExpr WhielNames Data := .rel (.prophecy uName)
def pT : RawRAExpr WhielNames Data :=
  .rel (.prophecy tAuxName)

#guard ambientSchema.arity? (.ordinary rName) = some 1
#guard ambientSchema.arity? (.prophecy uName) = some 1
#guard ambientSchema.arity? (.prophecy tAuxName) = some 2
#guard ambientSchema.arity? (.prophecy rName) = none

------------------------------------------------------------
-- Clauses
------------------------------------------------------------

def clause0 : QFAssertExpr Data ambientSchema :=
  qfAssert![ R ⊆ U ]

def clause0Raw : RawGuard WhielNames Data :=
  .subset oR oU

def clause0Text : String :=
  "(R ⊆ U)"

def clause0Again : QFAssertExpr Data ambientSchema :=
  qfAssert![ (R ⊆ U) ]

#guard clause0.toRaw = clause0Raw
#guard ClauseNotation.render clause0 = .ok clause0Text
example : clause0Again = clause0 :=
  Guard.eq_of_toRaw_eq (by decide)

def clause1 : QFAssertExpr Data ambientSchema :=
  qfAssert![ U∞ = U ]

def clause1Raw : RawGuard WhielNames Data :=
  .eq pU oU

def clause1Text : String :=
  "(U∞ = U)"

def clause1Again : QFAssertExpr Data ambientSchema :=
  qfAssert![ (U∞ = U) ]

#guard clause1.toRaw = clause1Raw
#guard ClauseNotation.render clause1 = .ok clause1Text
example : clause1Again = clause1 :=
  Guard.eq_of_toRaw_eq (by decide)

def clause2 : QFAssertExpr Data ambientSchema :=
  qfAssert![ T_aux∞ ⊆ (U × U∞) ]

def clause2Raw : RawGuard WhielNames Data :=
  .subset pT (.prod oU pU)

def clause2Text : String :=
  "(T_aux∞ ⊆ (U × U∞))"

def clause2Again : QFAssertExpr Data ambientSchema :=
  qfAssert![ (T_aux∞ ⊆ (U × U∞)) ]

#guard clause2.toRaw = clause2Raw
#guard ClauseNotation.render clause2 = .ok clause2Text
example : clause2Again = clause2 :=
  Guard.eq_of_toRaw_eq (by decide)

def clause3 : QFAssertExpr Data ambientSchema :=
  qfAssert![ (π[0] (σ[#0 = #1] T_aux)) ∪ R = U ]

def clause3Raw : RawGuard WhielNames Data :=
  .eq (.union (.proj [0] (.select (.eqIdx 0 1) oT)) oR) oU

def clause3Text : String :=
  "((π[0] (σ[#0 = #1] (T_aux)) ∪ R) = U)"

def clause3Again : QFAssertExpr Data ambientSchema :=
  qfAssert![ ((π[0] (σ[#0 = #1] (T_aux)) ∪ R) = U) ]

#guard clause3.toRaw = clause3Raw
#guard ClauseNotation.render clause3 = .ok clause3Text
example : clause3Again = clause3 :=
  Guard.eq_of_toRaw_eq (by decide)

/- Typed empties carry their arity in the printed text. -/
def clause4 : QFAssertExpr Data ambientSchema :=
  qfAssert![ (R ∖ U) = ∅ ]

def clause4Raw : RawGuard WhielNames Data :=
  .eq (.diff oR oU) (.empty 1)

def clause4Text : String :=
  "((R ∖ U) = ∅[1])"

def clause4Again : QFAssertExpr Data ambientSchema :=
  qfAssert![ ((R ∖ U) = ∅[1]) ]

#guard clause4.toRaw = clause4Raw
#guard ClauseNotation.render clause4 = .ok clause4Text
example : clause4Again = clause4 :=
  Guard.eq_of_toRaw_eq (by decide)

def clause5 : QFAssertExpr Data ambientSchema :=
  qfAssert![
    (σ[#0 = 3] R ⊆ U) ∧ ({"a"} ⊆ R) ∧
      (σ[#1 = true] T_aux = T_aux∞) ]

def clause5Raw : RawGuard WhielNames Data :=
  .and
    (.and
      (.subset (.select (.eqConst 0 (.num 3)) oR) oU)
      (.subset (.single (.str "a")) oR))
    (.eq (.select (.eqConst 1 (.bool Bool.true)) oT) pT)

def clause5Text : String :=
  "(((σ[#0 = 3] (R) ⊆ U) ∧ ({\"a\"} ⊆ R)) ∧ " ++
    "(σ[#1 = true] (T_aux) = T_aux∞))"

def clause5Again : QFAssertExpr Data ambientSchema :=
  qfAssert![
    (((σ[#0 = 3] (R) ⊆ U) ∧ ({"a"} ⊆ R)) ∧
      (σ[#1 = true] (T_aux) = T_aux∞)) ]

#guard clause5.toRaw = clause5Raw
#guard ClauseNotation.render clause5 = .ok clause5Text
example : clause5Again = clause5 :=
  Guard.eq_of_toRaw_eq (by decide)

def clause6 : QFAssertExpr Data ambientSchema :=
  qfAssert![
    ¬((R = ∅)) ∨
      (σ[(#0 = #1) ∧ ¬(#0 = 2)] T_aux∞ ⊆ ∅[2]) ]

def clause6Raw : RawGuard WhielNames Data :=
  .or
    (.not (.eq oR (.empty 1)))
    (.subset
      (.select
        (.and (.eqIdx 0 1) (.not (.eqConst 0 (.num 2))))
        pT)
      (.empty 2))

def clause6Text : String :=
  "((¬((R = ∅[1]))) ∨ " ++
    "(σ[(#0 = #1 ∧ ¬(#0 = 2))] (T_aux∞) ⊆ ∅[2]))"

def clause6Again : QFAssertExpr Data ambientSchema :=
  qfAssert![
    ((¬((R = ∅[1]))) ∨
      (σ[(#0 = #1 ∧ ¬(#0 = 2))] (T_aux∞) ⊆ ∅[2])) ]

#guard clause6.toRaw = clause6Raw
#guard ClauseNotation.render clause6 = .ok clause6Text
example : clause6Again = clause6 :=
  Guard.eq_of_toRaw_eq (by decide)

def clause7 : QFAssertExpr Data ambientSchema :=
  qfAssert![ true ∨ (⊤ = ∅[0]) ]

def clause7Raw : RawGuard WhielNames Data :=
  .or .«true» (.eq .top (.empty 0))

def clause7Text : String :=
  "(true ∨ (⊤ = ∅[0]))"

def clause7Again : QFAssertExpr Data ambientSchema :=
  qfAssert![ (true ∨ (⊤ = ∅[0])) ]

#guard clause7.toRaw = clause7Raw
#guard ClauseNotation.render clause7 = .ok clause7Text
example : clause7Again = clause7 :=
  Guard.eq_of_toRaw_eq (by decide)

/- The `programQF!` spelling still serves program schemas. -/
def programClause : QFAssertExpr Data inputSchema :=
  programQF![ R ⊆ U ]

#guard programClause.toRaw =
  RawGuard.subset (.rel rName) (.rel uName)

------------------------------------------------------------
-- Proposal Declarations
------------------------------------------------------------

#guard
  ClauseNotation.renderProposalDeclaration
    "candidateClause0" "ambientSchema" clause2 =
  .ok ("def candidateClause0 :\n" ++
    "    QFAssertExpr Data ambientSchema :=\n" ++
    "  qfAssert![\n" ++
    "    (T_aux∞ ⊆ (U × U∞))\n" ++
    "  ]")

#guard
  (ClauseNotation.renderProposalDeclaration
    "" "ambientSchema" clause0).isOk = Bool.false

------------------------------------------------------------
-- Positive Indices
------------------------------------------------------------

def rOne : ProgramNames :=
  .programSymbol ⟨"R", by decide⟩ 1

def tAuxTwo : ProgramNames :=
  .auxiliarySymbol ⟨"T", by decide⟩ 2

/-
  A hand-built schema with snapshot copies `R_1` and
  `T_aux_2` in both the ordinary and the prophecy copy.
-/
def indexedSchema : UnnamedSchema WhielNames where
  syms :=
    {.ordinary rName, .ordinary rOne, .prophecy rOne,
      .ordinary tAuxName, .ordinary tAuxTwo,
      .prophecy tAuxTwo}
  arity := fun relation =>
    match relation.1.programName with
    | .auxiliarySymbol _ _ => 2
    | _ => 1

def oR1 : RawRAExpr WhielNames Data :=
  .rel (.ordinary rOne)
def pR1 : RawRAExpr WhielNames Data :=
  .rel (.prophecy rOne)
def oT2 : RawRAExpr WhielNames Data :=
  .rel (.ordinary tAuxTwo)
def pT2 : RawRAExpr WhielNames Data :=
  .rel (.prophecy tAuxTwo)

#guard indexedSchema.arity? (.ordinary rOne) = some 1
#guard indexedSchema.arity? (.prophecy tAuxTwo) = some 2

def indexed0 : QFAssertExpr Data indexedSchema :=
  qfAssert![ R_1 ⊆ R ]

def indexed0Raw : RawGuard WhielNames Data :=
  .subset oR1 oR

def indexed0Text : String :=
  "(R_1 ⊆ R)"

def indexed0Again : QFAssertExpr Data indexedSchema :=
  qfAssert![ (R_1 ⊆ R) ]

#guard indexed0.toRaw = indexed0Raw
#guard ClauseNotation.render indexed0 = .ok indexed0Text
example : indexed0Again = indexed0 :=
  Guard.eq_of_toRaw_eq (by decide)

def indexed1 : QFAssertExpr Data indexedSchema :=
  qfAssert![ R_1∞ = R_1 ]

def indexed1Raw : RawGuard WhielNames Data :=
  .eq pR1 oR1

def indexed1Text : String :=
  "(R_1∞ = R_1)"

def indexed1Again : QFAssertExpr Data indexedSchema :=
  qfAssert![ (R_1∞ = R_1) ]

#guard indexed1.toRaw = indexed1Raw
#guard ClauseNotation.render indexed1 = .ok indexed1Text
example : indexed1Again = indexed1 :=
  Guard.eq_of_toRaw_eq (by decide)

def indexed2 : QFAssertExpr Data indexedSchema :=
  qfAssert![ T_aux_2 ⊆ (R × R_1∞) ]

def indexed2Raw : RawGuard WhielNames Data :=
  .subset oT2 (.prod oR pR1)

def indexed2Text : String :=
  "(T_aux_2 ⊆ (R × R_1∞))"

def indexed2Again : QFAssertExpr Data indexedSchema :=
  qfAssert![ (T_aux_2 ⊆ (R × R_1∞)) ]

#guard indexed2.toRaw = indexed2Raw
#guard ClauseNotation.render indexed2 = .ok indexed2Text
example : indexed2Again = indexed2 :=
  Guard.eq_of_toRaw_eq (by decide)

def indexed3 : QFAssertExpr Data indexedSchema :=
  qfAssert![ (σ[#0 = #1] T_aux_2∞ = ∅) ∧ (T_aux ⊆ T_aux_2) ]

def indexed3Raw : RawGuard WhielNames Data :=
  .and
    (.eq (.select (.eqIdx 0 1) pT2) (.empty 2))
    (.subset oT oT2)

def indexed3Text : String :=
  "((σ[#0 = #1] (T_aux_2∞) = ∅[2]) ∧ (T_aux ⊆ T_aux_2))"

def indexed3Again : QFAssertExpr Data indexedSchema :=
  qfAssert![
    ((σ[#0 = #1] (T_aux_2∞) = ∅[2]) ∧ (T_aux ⊆ T_aux_2)) ]

#guard indexed3.toRaw = indexed3Raw
#guard ClauseNotation.render indexed3 = .ok indexed3Text
example : indexed3Again = indexed3 :=
  Guard.eq_of_toRaw_eq (by decide)

/- The printer spells every non-flag name, in any copy. -/
#guard ClauseNotation.renderName (.ordinary rName) = .ok "R"
#guard ClauseNotation.renderName (.ordinary rOne) = .ok "R_1"
#guard ClauseNotation.renderName (.prophecy rOne) =
  .ok "R_1∞"
#guard ClauseNotation.renderName (.ordinary tAuxName) =
  .ok "T_aux"
#guard ClauseNotation.renderName (.prophecy tAuxTwo) =
  .ok "T_aux_2∞"
#guard ClauseNotation.renderName
  (.ordinary (.programSymbol ⟨"U", by decide⟩ 12)) =
  .ok "U_12"

------------------------------------------------------------
-- Rejected Spellings
------------------------------------------------------------

/-
  `ambientSchema` has no `R_2`: the notation reads the name,
  and schema membership rejects it at elaboration.
-/
/--
error: unknown relation or non-computable relation arity
-/
#guard_msgs in
def rejectedIndexed :
    QFAssertExpr Data ambientSchema :=
  qfAssert![ R_2 = ∅ ]

/--
error: unknown relation or non-computable relation arity
-/
#guard_msgs in
def rejectedIndexedProphecy :
    QFAssertExpr Data ambientSchema :=
  qfAssert![ U_2∞ = ∅ ]

/- Index zero has exactly one spelling. -/
/--
error: index zero is spelled without a suffix; write 'R' instead of 'R_0'
-/
#guard_msgs in
def rejectedZero :
    QFAssertExpr Data ambientSchema :=
  qfAssert![ R_0 = ∅ ]

/--
error: prophecy names 'X∞' are only available over 'WhielNames' schemas
-/
#guard_msgs in
def rejectedProgramProphecy :
    QFAssertExpr Data inputSchema :=
  programQF![ R∞ = ∅ ]

def positiveIndexRaw : RawGuard WhielNames Data :=
  .eqEmptyRight (.rel (.ordinary rOne))

/-- info: Except.ok "(R_1 = ∅)" -/
#guard_msgs in
#eval ClauseNotation.renderRaw positiveIndexRaw

def flagRaw : RawGuard WhielNames Data :=
  .eqEmptyRight (.rel (.prophecy (.flagSymbol 4 0)))

/-- info: Except.ok "(flag_4_0∞ = ∅)" -/
#guard_msgs in
#eval ClauseNotation.renderRaw flagRaw

def ordinaryFlagRaw : RawGuard WhielNames Data :=
  .eqEmptyRight (.rel (.ordinary (.flagSymbol 4 0)))

/-- info: Except.ok "(flag_4_0 = ∅)" -/
#guard_msgs in
#eval ClauseNotation.renderRaw ordinaryFlagRaw

end FrameworkIIFixedAmbientClauseNotation
end Tests
end Synthesis
end Whiel
