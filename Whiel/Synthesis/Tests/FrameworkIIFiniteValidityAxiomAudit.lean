-- Author: Jesse Comer
import Whiel.Library.FiniteOrder
import Whiel.Synthesis.FrameworkII.FiniteValidity.Transport

/-
  Research-only axiom audit for the dormant finite-validity
  library and its Framework-II transport theorem.
-/

open Whiel.Synthesis.FrameworkII.FiniteValidity

#print axioms
  Whiel.Library.FiniteOrder.FV000001.meaning
#print axioms
  Whiel.Library.FiniteOrder.FV000001.adomValid
#print axioms
  Whiel.Library.FiniteOrder.FV000002.meaning
#print axioms
  Whiel.Library.FiniteOrder.FV000002.adomValid
#print axioms
  Whiel.Library.FiniteOrder.epsilonMaxBinaryDomain_adomValid
#print axioms
  Whiel.Library.FiniteOrder.linearOrderMax_adomValid
#print axioms
  valid_of_prependAxioms_shallowValid
