-- Author: Jesse Comer
import Whiel.Vampire.SolverName.Concrete

/-
  Axiom audit for the solver-name class, the string
  escape encoding, and the two production carriers.
-/

------------------------------------------------------------
-- Identifier and Reserved-Shape Lemmas
------------------------------------------------------------

/-- info: 'Whiel.Vampire.legalTptpName_of_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Vampire.legalTptpName_of_toList

/-- info: 'Whiel.Vampire.not_isReservedWord_of_firstChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Vampire.not_isReservedWord_of_firstChar

/-- info: 'Whiel.Vampire.not_isIntroducedShape_of_firstChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.not_isIntroducedShape_of_firstChar

/-- info: 'Whiel.Vampire.ne_of_firstChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Vampire.ne_of_firstChar

------------------------------------------------------------
-- String Escape Encoding
------------------------------------------------------------

/-- info: 'Whiel.Vampire.SolverName.Escape.hexDigitValue_hexDigitChar' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.SolverName.Escape.hexDigitValue_hexDigitChar

/-- info: 'Whiel.Vampire.SolverName.Escape.isAlphanum_hexDigitChar' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.SolverName.Escape.isAlphanum_hexDigitChar

/-- info: 'Whiel.Vampire.SolverName.Escape.unescapeChars_escapeChar_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.SolverName.Escape.unescapeChars_escapeChar_append

/-- info: 'Whiel.Vampire.SolverName.Escape.unescapeChars_escapeChars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.SolverName.Escape.unescapeChars_escapeChars

/-- info: 'Whiel.Vampire.SolverName.Escape.unescape?_escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.SolverName.Escape.unescape?_escape

/-- info: 'Whiel.Vampire.SolverName.Escape.escape_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.SolverName.Escape.escape_injective

/-- info: 'Whiel.Vampire.SolverName.Escape.all_legal_escapeChars' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.SolverName.Escape.all_legal_escapeChars

------------------------------------------------------------
-- Relation Names
------------------------------------------------------------

/-- info: 'Whiel.Vampire.solverName_whielNames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Vampire.solverName_whielNames

/-- info: 'Whiel.Vampire.solverName_whielNames_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Vampire.solverName_whielNames_toList

/-- info: 'Whiel.Vampire.solverName_whielNames_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Vampire.solverName_whielNames_injective

/-- info: 'Whiel.Vampire.legalTptpName_solverName_whielNames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.legalTptpName_solverName_whielNames

------------------------------------------------------------
-- Constant Names
------------------------------------------------------------

/-- info: 'Whiel.Vampire.dataOfSolverName?_solverName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Vampire.dataOfSolverName?_solverName

/-- info: 'Whiel.Vampire.solverName_data_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Vampire.solverName_data_toList

/-- info: 'Whiel.Vampire.solverName_data_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Vampire.solverName_data_injective

/-- info: 'Whiel.Vampire.legalTptpName_solverName_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Vampire.legalTptpName_solverName_data

------------------------------------------------------------
-- Production Obligations
------------------------------------------------------------

/-- info: 'Whiel.Vampire.lawfulSolverNameWhielNames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Vampire.lawfulSolverNameWhielNames

/-- info: 'Whiel.Vampire.lawfulSolverNameData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Vampire.lawfulSolverNameData

------------------------------------------------------------
-- Reserved Shapes and Disjointness
------------------------------------------------------------

/-- info: 'Whiel.Vampire.not_isReservedWord_solverName_whielNames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.not_isReservedWord_solverName_whielNames

/-- info: 'Whiel.Vampire.not_isReservedWord_solverName_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.not_isReservedWord_solverName_data

/-- info: 'Whiel.Vampire.not_isIntroducedShape_solverName_whielNames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.not_isIntroducedShape_solverName_whielNames

/-- info: 'Whiel.Vampire.not_isIntroducedShape_solverName_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.not_isIntroducedShape_solverName_data

/-- info: 'Whiel.Vampire.solverName_whielNames_ne_solverName_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Vampire.solverName_whielNames_ne_solverName_data
