-- Author: Jesse Comer
import Whiel.Vampire.SolverName.Concrete

set_option linter.hashCommand false

/-
  Executable checks for the solver names of the two
  production carriers: the exact spelling of a relation and
  of a constant, the round trip of the constant decoder, and
  the three properties the renderer will rely on — legality,
  no reserved spelling, no introduced-symbol shape.
-/

namespace Whiel
namespace Synthesis
namespace Tests
namespace SolverNameTest

open Concrete
open Whiel.Vampire

private def baseE : AlphaString := ⟨"E", by decide⟩
private def baseS : AlphaString := ⟨"S", by decide⟩
private def baseT : AlphaString := ⟨"T", by decide⟩

private def programE : WhielNames :=
  .ordinary (.programSymbol baseE 0)

private def auxiliaryS : WhielNames :=
  .ordinary (.auxiliarySymbol baseS 0)

private def prophecyT : WhielNames :=
  .prophecy (.programSymbol baseT 0)

private def flagThree : WhielNames :=
  .ordinary (.flagSymbol 3 0)

private def prophecyAuxiliaryT : WhielNames :=
  .prophecy (.auxiliarySymbol baseT 2)

------------------------------------------------------------
-- Relation Names
------------------------------------------------------------

#guard solverName programE == "op_zE"

#guard solverName auxiliaryS == "oa_zS"

#guard solverName prophecyT == "yp_zT"

#guard solverName flagThree == "of_z3"

#guard solverName prophecyAuxiliaryT == "ya_sszT"

------------------------------------------------------------
-- Constant Names
------------------------------------------------------------

#guard solverName (Data.num 42) == "kn42"

#guard solverName (Data.bool false) == "kbf"

#guard solverName (Data.bool true) == "kbt"

/- A string of alphabet characters is carried through. -/
#guard solverName (Data.str "root") == "ksroot"

/-
  Everything else is escaped: an uppercase letter, the
  underscore itself, a space, a non-ASCII character. The
  empty string leaves only the kind prefix.
-/
#guard solverName (Data.str "Root") == "ks_000052oot"

#guard solverName (Data.str "a_b") == "ksa_00005fb"

#guard solverName (Data.str "a b") == "ksa_000020b"

#guard solverName (Data.str "é") == "ks_0000e9"

#guard solverName (Data.str "") == "ks"

------------------------------------------------------------
-- Decoding
------------------------------------------------------------

#guard dataOfSolverName? (solverName (Data.num 42)) ==
  some (Data.num 42)

#guard dataOfSolverName? (solverName (Data.bool false)) ==
  some (Data.bool false)

#guard dataOfSolverName? (solverName (Data.bool true)) ==
  some (Data.bool true)

#guard
  dataOfSolverName? (solverName (Data.str "Root a_b é")) ==
    some (Data.str "Root a_b é")

#guard dataOfSolverName? (solverName (Data.str "")) ==
  some (Data.str "")

------------------------------------------------------------
-- Legality and Reserved Shapes
------------------------------------------------------------

#guard legalTptpName (solverName programE)

#guard legalTptpName (solverName flagThree)

#guard legalTptpName (solverName (Data.str "Root a_b é"))

#guard !isReservedWord (solverName programE)

#guard !isReservedWord (solverName (Data.num 42))

#guard !isIntroducedShape (solverName prophecyT)

#guard !isIntroducedShape (solverName (Data.str "Kirk"))

/- The two carriers never collide. -/
#guard solverName programE != solverName (Data.str "root")

end SolverNameTest
end Tests
end Synthesis
end Whiel
