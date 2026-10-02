-- Author: Jesse Comer
import Whiel.Concrete.WhielNames

/-
  Parseable relation identifiers for fixed-ambient Whiel
  source notation.

  These names are distinct from both opaque solver keys and
  human presentation. Every constructor and internal index
  is encoded explicitly in an identifier accepted by Lean.
  Program and auxiliary names carry an alphabetical base;
  flag names carry a decimal identity in its place.
-/

namespace Whiel
namespace Concrete
namespace WhielNames
namespace SurfaceSyntax

private def encodeIndex : Nat -> List Char
| 0 => []
| index + 1 => 's' :: encodeIndex index

private def parseIndex :
    List Char -> Option (Nat × List Char)
| 'z' :: suffix => some (0, suffix)
| 's' :: suffix => do
    let (index, rest) <- parseIndex suffix
    pure (index + 1, rest)
| _ => none

private theorem parseIndex_encodeIndex
    (index : Nat)
    (suffix : List Char) :
    parseIndex (encodeIndex index ++ 'z' :: suffix) =
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
  Decimal flag identities are decoded over characters so
  that literal sources still elaborate by `decide`.
-/
private def parseDecimal (chars : List Char) : Option Nat :=
  match chars with
  | [] => none
  | _ =>
      if chars.all Char.isDigit then
        some (Nat.ofDigitChars 10 chars 0)
      else
        none

private theorem parseDecimal_toDigits
    (id : Nat) :
    parseDecimal (Nat.toDigits 10 id) = some id := by
  have hDigits :
      (Nat.toDigits 10 id).all Char.isDigit = true := by
    rw [List.all_eq_true]
    intro c hc
    exact Nat.isDigit_of_mem_toDigits
      (by decide) (by decide) hc
  unfold parseDecimal
  split
  · exact (Nat.toDigits_ne_nil ‹_›).elim
  · simp [hDigits]

private def taggedSource
    (outer inner : Char)
    (index : Nat)
    (payload : List Char) : String :=
  String.ofList <|
    outer :: inner :: '_' ::
      encodeIndex index ++ 'z' :: payload

/- Family tag and payload of one program name. -/
private def familySource :
    ProgramNames -> Char × Nat × List Char
| .programSymbol base index =>
    ('p', index, base.value.toList)
| .auxiliarySymbol base index =>
    ('a', index, base.value.toList)
| .flagSymbol id index =>
    ('f', index, id.repr.toList)

/- Parseable, constructor-complete relation source. -/
def source : WhielNames -> String
| .ordinary name =>
    let (inner, index, payload) := familySource name
    taggedSource 'o' inner index payload
| .prophecy name =>
    let (inner, index, payload) := familySource name
    taggedSource 'y' inner index payload

private def parseAlphaFamily
    (make : AlphaString -> ProgramNames)
    (baseChars : List Char) :
    Except String ProgramNames :=
  match AlphaString.ofString?
      (String.ofList baseChars) with
  | none => .error "relation base must be alphabetical"
  | some base => .ok (make base)

/- Decode one program name from its tag and payload. -/
private def parseFamily
    (inner : Char)
    (index : Nat)
    (payload : List Char) : Except String ProgramNames :=
  match inner with
  | 'p' =>
      parseAlphaFamily (.programSymbol · index) payload
  | 'a' =>
      parseAlphaFamily (.auxiliarySymbol · index) payload
  | 'f' =>
      match parseDecimal payload with
      | none => .error "flag identity must be decimal"
      | some id => .ok (.flagSymbol id index)
  | _ => .error "invalid relation-family tag"

private def parseTagged
    (outer inner : Char)
    (payload : List Char) : Except String WhielNames :=
  match parseIndex payload with
  | none => .error "invalid relation index encoding"
  | some (index, familyPayload) =>
      match parseFamily inner index familyPayload with
      | .error message => .error message
      | .ok programName =>
          match outer with
          | 'o' => .ok (.ordinary programName)
          | 'y' => .ok (.prophecy programName)
          | _ => .error "invalid ordinary/prophecy tag"

/- Decode one canonical fixed-ambient relation source. -/
def parse (text : String) : Except String WhielNames :=
  match text.toList with
  | outer :: inner :: '_' :: payload =>
      parseTagged outer inner payload
  | _ => .error "expected a fixed-ambient relation name"

@[simp] theorem parse_source
    (name : WhielNames) :
    parse (source name) = .ok name := by
  cases name <;> rename_i name <;> cases name <;>
    simp [parse, source, taggedSource, familySource,
      parseTagged, parseIndex_encodeIndex, parseFamily,
      parseAlphaFamily, alphaString_ofString?_value,
      parseDecimal_toDigits]

------------------------------------------------------------
-- The Characters of a Source
------------------------------------------------------------

/-
  The index run is a run of `s`. Stating it this way lets a
  caller read the run's length without the private encoder.
-/
private theorem encodeIndex_eq_replicate
    (index : Nat) :
    encodeIndex index = List.replicate index 's' := by
  induction index with
  | zero => rfl
  | succ index ih =>
      rw [encodeIndex, ih, List.replicate_succ]

private theorem toList_taggedSource
    (outer inner : Char)
    (index : Nat)
    (payload : List Char) :
    (taggedSource outer inner index payload).toList =
      outer :: inner :: '_' ::
        (List.replicate index 's' ++ 'z' :: payload) := by
  simp [taggedSource, encodeIndex_eq_replicate]

private theorem all_isAlphanum_of_isAlpha
    {chars : List Char}
    (hAlpha : chars.all Char.isAlpha = true) :
    chars.all Char.isAlphanum = true := by
  rw [List.all_eq_true] at hAlpha ⊢
  intro c hMem
  simp [Char.isAlphanum, hAlpha c hMem]

private theorem all_isAlphanum_repr
    (value : Nat) :
    value.repr.toList.all Char.isAlphanum = true := by
  rw [Nat.toList_repr, List.all_eq_true]
  intro c hMem
  have hDigit : c.isDigit :=
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) hMem
  simp [Char.isAlphanum, hDigit]

/-
  Every source is a copy tag, a family tag, `_`, the unary
  index run closed by `z`, and an alphanumeric payload. The
  builders above are private, so this is how a caller outside
  this module reads a source's characters — for instance to
  show that the identifier is legal for a solver.
-/
theorem toList_source
    (name : WhielNames) :
    ∃ (outer inner : Char) (index : Nat)
      (payload : List Char),
      (outer = 'o' ∨ outer = 'y') ∧
      (inner = 'p' ∨ inner = 'a' ∨ inner = 'f') ∧
      payload.all Char.isAlphanum = true ∧
      (source name).toList =
        outer :: inner :: '_' ::
          (List.replicate index 's' ++ 'z' :: payload) := by
  rcases name with name | name <;>
    rcases name with ⟨base, index⟩ | ⟨base, index⟩ |
      ⟨id, index⟩
  · exact ⟨'o', 'p', index, _, Or.inl rfl, Or.inl rfl,
      all_isAlphanum_of_isAlpha base.isAlpha,
      toList_taggedSource _ _ _ _⟩
  · exact ⟨'o', 'a', index, _, Or.inl rfl,
      Or.inr (Or.inl rfl),
      all_isAlphanum_of_isAlpha base.isAlpha,
      toList_taggedSource _ _ _ _⟩
  · exact ⟨'o', 'f', index, _, Or.inl rfl,
      Or.inr (Or.inr rfl), all_isAlphanum_repr id,
      toList_taggedSource _ _ _ _⟩
  · exact ⟨'y', 'p', index, _, Or.inr rfl, Or.inl rfl,
      all_isAlphanum_of_isAlpha base.isAlpha,
      toList_taggedSource _ _ _ _⟩
  · exact ⟨'y', 'a', index, _, Or.inr rfl,
      Or.inr (Or.inl rfl),
      all_isAlphanum_of_isAlpha base.isAlpha,
      toList_taggedSource _ _ _ _⟩
  · exact ⟨'y', 'f', index, _, Or.inr rfl,
      Or.inr (Or.inr rfl), all_isAlphanum_repr id,
      toList_taggedSource _ _ _ _⟩

/- Elaborate a literal canonical identifier to its name. -/
def ofSource
    (text : String)
    (hValid : (parse text).toOption.isSome = true :=
      by decide) : WhielNames :=
  (parse text).toOption.get hValid

end SurfaceSyntax
end WhielNames
end Concrete
end Whiel
