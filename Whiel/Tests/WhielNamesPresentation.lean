-- Author: Jesse Comer
import Whiel.Concrete.WhielNames.Notation
import Whiel.Concrete.WhielNames.Order
import Whiel.Concrete.WhielNames.SurfaceSyntax

set_option linter.hashCommand false

/-
  Focused tests for machine encodings, the notation
  spelling, and optional structural orders on `WhielNames`.
  The semantic fixed-ambient canary does not import these
  presentation sidecars.

  A name has two forms and no more: the structural `Repr`,
  from which solver keys and the machine encodings here are
  derived and which is frozen by committed certificates,
  and `spell`, the notation's own text, which is what every
  printer renders and everything a reader or an agent sees
  carries.
-/

------------------------------------------------------------
-- Presentation Fixtures
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace WhielNamesPresentation

open Concrete

def baseR : AlphaString :=
  ⟨"R", by decide⟩

def baseT : AlphaString :=
  ⟨"T", by decide⟩

def programR : ProgramNames :=
  .programSymbol baseR 0

def indexedR : ProgramNames :=
  .programSymbol baseR 1

def auxiliaryT : ProgramNames :=
  .auxiliarySymbol baseT 0

def indexedAuxiliaryT : ProgramNames :=
  .auxiliarySymbol baseT 2

def flagThree : ProgramNames :=
  .flagSymbol 3 0

def indexedFlagThree : ProgramNames :=
  .flagSymbol 3 2

def ordinaryR : WhielNames :=
  .ordinary programR

def ordinaryT : WhielNames :=
  .ordinary auxiliaryT

def prophecyR : WhielNames :=
  .prophecy programR

def prophecyT : WhielNames :=
  .prophecy auxiliaryT

def ordinaryFlag : WhielNames :=
  .ordinary flagThree

def prophecyFlag : WhielNames :=
  .prophecy indexedFlagThree

end WhielNamesPresentation

end Tests

end Whiel

------------------------------------------------------------
-- Canonical Machine Encoding
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace WhielNamesPresentation

open Concrete

theorem program_key_golden :
    programR.encode = "p::R" := by
  decide

theorem auxiliary_key_golden :
    auxiliaryT.encode = "a::T" := by
  decide

theorem indexed_program_key_golden :
    indexedR.encode = "p:s:R" := by
  decide

theorem indexed_auxiliary_key_golden :
    indexedAuxiliaryT.encode = "a:ss:T" := by
  decide

theorem ordinary_key_golden :
    ordinaryR.encode = "o:p::R" := by
  decide

theorem prophecy_key_golden :
    prophecyT.encode = "y:a::T" := by
  decide

theorem program_codec :
    ProgramNames.parse? indexedR.encode =
      some indexedR := by
  simp

theorem auxiliary_codec :
    ProgramNames.parse? indexedAuxiliaryT.encode =
      some indexedAuxiliaryT := by
  simp

theorem ordinary_codec :
    WhielNames.parse? ordinaryR.encode =
      some ordinaryR := by
  simp

theorem prophecy_codec :
    WhielNames.parse? prophecyT.encode =
      some prophecyT := by
  simp

theorem constructors_have_distinct_keys :
    ordinaryR.encode ≠ prophecyR.encode := by
  decide

#guard flagThree.encode == "f::3"

#guard indexedFlagThree.encode == "f:ss:3"

#guard ordinaryFlag.encode == "o:f::3"

#guard prophecyFlag.encode == "y:f:ss:3"

#guard ProgramNames.parse? indexedFlagThree.encode ==
  some indexedFlagThree

#guard WhielNames.parse? ordinaryFlag.encode ==
  some ordinaryFlag

#guard WhielNames.parse? prophecyFlag.encode ==
  some prophecyFlag

#guard WhielNames.parse? "o:f::" == none

#guard WhielNames.parse? "o:f::R" == none

end WhielNamesPresentation

end Tests

end Whiel

------------------------------------------------------------
-- Notation Spelling
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace WhielNamesPresentation

open Concrete

theorem ordinary_program_spelling :
    ordinaryR.spell = "R" := by
  decide

theorem ordinary_auxiliary_spelling :
    ordinaryT.spell = "T_aux" := by
  decide

theorem prophecy_program_spelling :
    prophecyR.spell = "R∞" := by
  decide

theorem prophecy_auxiliary_spelling :
    prophecyT.spell = "T_aux∞" := by
  decide

theorem indexed_program_spelling :
    indexedR.spell = "R_1" := by
  decide

theorem indexed_auxiliary_spelling :
    indexedAuxiliaryT.spell = "T_aux_2" := by
  decide

/-
  A flag spells as `flag_i_n`, both numerals canonical and
  neither elided, and the notation reads exactly that form
  back. No base name can produce it: a base is a purely
  alphabetical `AlphaString`, so a program or auxiliary
  spelling carries at most one numeric suffix and its only
  three-segment form has the literal middle segment `aux`.
  The prophecy copy of a flag carries the same `∞` suffix
  every prophecy name does.
-/
#guard ordinaryFlag.spell == "flag_3_0"

#guard prophecyFlag.spell == "flag_3_2∞"

#guard (WhielNames.ordinary (.flagSymbol 12 0)).spell ==
  "flag_12_0"

end WhielNamesPresentation

end Tests

end Whiel

------------------------------------------------------------
-- Optional Structural Order
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace WhielNamesPresentation

open Concrete

theorem program_before_auxiliary :
    ordinaryR < ordinaryT := by
  decide

theorem ordinary_before_prophecy :
    ordinaryR < prophecyR := by
  decide

theorem base_before_indexed :
    programR < indexedR := by
  decide

theorem auxiliary_before_flag :
    auxiliaryT < flagThree := by
  decide

theorem flag_base_before_indexed :
    flagThree < indexedFlagThree := by
  decide

theorem flag_identity_before_index :
    indexedFlagThree < ProgramNames.flagSymbol 4 0 := by
  decide

end WhielNamesPresentation

end Tests

end Whiel

------------------------------------------------------------
-- Surface Source
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace WhielNamesPresentation

open Concrete

#guard WhielNames.SurfaceSyntax.source ordinaryFlag ==
  "of_z3"

#guard WhielNames.SurfaceSyntax.source prophecyFlag ==
  "yf_ssz3"

#guard WhielNames.SurfaceSyntax.parse
    (WhielNames.SurfaceSyntax.source ordinaryFlag) ==
  .ok ordinaryFlag

#guard WhielNames.SurfaceSyntax.parse
    (WhielNames.SurfaceSyntax.source prophecyFlag) ==
  .ok prophecyFlag

#guard (WhielNames.SurfaceSyntax.parse "of_z").toOption ==
  none

#guard (WhielNames.SurfaceSyntax.parse "of_zR").toOption ==
  none

/- Literal flag sources still elaborate by `decide`. -/
example :
    WhielNames.SurfaceSyntax.ofSource "yf_ssz3" =
      prophecyFlag := by
  decide

end WhielNamesPresentation

end Tests

end Whiel

------------------------------------------------------------
-- Raw Input Names
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace WhielNamesPresentation

open Concrete

example : programR.IsRawInput := by
  decide

example : auxiliaryT.IsRawInput := by
  decide

example : ¬ indexedR.IsRawInput := by
  decide

example : ¬ flagThree.IsRawInput := by
  decide

example : ¬ indexedFlagThree.IsRawInput := by
  simp [indexedFlagThree]

#guard flagThree.IsFlag

#guard !programR.IsFlag

def rawSchema : UnnamedSchema ProgramNames where
  syms := {programR, auxiliaryT}
  arity := fun _ => 1

def indexedSchema : UnnamedSchema ProgramNames where
  syms := {programR, indexedR}
  arity := fun _ => 1

def flaggedSchema : UnnamedSchema ProgramNames where
  syms := {programR, flagThree}
  arity := fun _ => 1

example : rawSchema.RawIndexZero := by
  decide

example : ¬ indexedSchema.RawIndexZero := by
  decide

example : ¬ flaggedSchema.RawIndexZero := by
  decide

#guard rawSchema.RawIndexZero

#guard !flaggedSchema.RawIndexZero

end WhielNamesPresentation

end Tests

end Whiel
