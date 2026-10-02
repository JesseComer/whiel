-- Author: Jesse Comer
import Whiel.Concrete.WhielNames

/-
  Canonical constructor-distinguishing codecs for the
  fixed-ambient Whiel relation-name carrier.

  Key declarations include:
    * `Whiel.Concrete.ProgramNames.encode`
    * `Whiel.Concrete.ProgramNames.parse?`
    * `Whiel.Concrete.WhielNames.encode`
    * `Whiel.Concrete.WhielNames.parse?`

  These machine spellings are independent of the
  human-readable superscript notation.
-/

------------------------------------------------------------
-- Program-Name Encoding
------------------------------------------------------------

namespace Whiel

namespace Concrete

namespace ProgramNames

/-
  Unary index encoding used by the canonical name codec.
  It keeps delimiter parsing independent of decimal syntax.
-/
private def encodeIndex : Nat → List Char
| 0 => []
| index + 1 => 's' :: encodeIndex index

private def parseIndex :
    List Char → Option (Nat × List Char)
| ':' :: suffix => some (0, suffix)
| 's' :: suffix => do
    let (index, rest) ← parseIndex suffix
    pure (index + 1, rest)
| _ => none

private theorem parseIndex_encodeIndex
    (index : Nat)
    (suffix : List Char) :
    parseIndex
        (encodeIndex index ++ ':' :: suffix) =
      some (index, suffix) := by
  induction index with
  | zero =>
      rfl
  | succ index ih =>
      simp [encodeIndex, parseIndex, ih]

private theorem alphaString_ofString?_value
    (base : AlphaString) :
    AlphaString.ofString? base.value = some base := by
  unfold AlphaString.ofString?
  split
  · congr
  · rename_i hNotAlpha
    exact (hNotAlpha base.isAlpha).elim

/-
  Canonical constructor-distinguishing program-name key.
  Flags carry a decimal identity where the other families
  carry an alphabetical base.
-/
def encode (name : ProgramNames) : String :=
  String.ofList <|
    match name with
    | .programSymbol base index =>
        'p' :: ':' ::
          encodeIndex index ++ ':' :: base.value.toList
    | .auxiliarySymbol base index =>
        'a' :: ':' ::
          encodeIndex index ++ ':' :: base.value.toList
    | .flagSymbol id index =>
        'f' :: ':' ::
          encodeIndex index ++ ':' :: id.repr.toList

/- Parse a canonical program-name key. -/
def parse? (encoded : String) : Option ProgramNames :=
  match encoded.toList with
  | 'p' :: ':' :: payload =>
      match parseIndex payload with
      | some (index, baseChars) =>
          (AlphaString.ofString?
              (String.ofList baseChars)).map
            fun base => .programSymbol base index
      | none => none
  | 'a' :: ':' :: payload =>
      match parseIndex payload with
      | some (index, baseChars) =>
          (AlphaString.ofString?
              (String.ofList baseChars)).map
            fun base => .auxiliarySymbol base index
      | none => none
  | 'f' :: ':' :: payload =>
      match parseIndex payload with
      | some (index, idChars) =>
          (String.ofList idChars).toNat?.map
            fun id => .flagSymbol id index
      | none => none
  | _ => none

/- Canonical program-name keys round-trip. -/
@[simp] theorem parse?_encode
    (name : ProgramNames) :
    parse? name.encode = some name := by
  cases name with
  | programSymbol base index =>
      simp [encode, parse?, parseIndex_encodeIndex,
        alphaString_ofString?_value]
  | auxiliarySymbol base index =>
      simp [encode, parse?, parseIndex_encodeIndex,
        alphaString_ofString?_value]
  | flagSymbol id index =>
      simp [encode, parse?, parseIndex_encodeIndex,
        ← Nat.repr_eq_ofList_toDigits]

/- Canonical program-name keys uniquely identify names. -/
theorem encode_injective :
    Function.Injective encode := by
  intro left right hEq
  have hParsed := congrArg parse? hEq
  simpa using hParsed

end ProgramNames

end Concrete

end Whiel

------------------------------------------------------------
-- Whiel-Name Encoding
------------------------------------------------------------

namespace Whiel

namespace Concrete

namespace WhielNames

/- Canonical constructor-distinguishing Whiel-name key. -/
def encode (name : WhielNames) : String :=
  String.ofList <|
    match name with
    | .ordinary programName =>
        'o' :: ':' :: programName.encode.toList
    | .prophecy programName =>
        'y' :: ':' :: programName.encode.toList

/- Parse a canonical Whiel-name key. -/
def parse? (encoded : String) : Option WhielNames :=
  match encoded.toList with
  | 'o' :: ':' :: payload =>
      (ProgramNames.parse? (String.ofList payload)).map
        WhielNames.ordinary
  | 'y' :: ':' :: payload =>
      (ProgramNames.parse? (String.ofList payload)).map
        WhielNames.prophecy
  | _ => none

/- Canonical Whiel-name keys round-trip. -/
@[simp] theorem parse?_encode
    (name : WhielNames) :
    parse? name.encode = some name := by
  cases name <;> simp [encode, parse?]

/- Canonical Whiel-name keys uniquely identify names. -/
theorem encode_injective :
    Function.Injective encode := by
  intro left right hEq
  have hParsed := congrArg parse? hEq
  simpa using hParsed

end WhielNames

end Concrete

end Whiel
