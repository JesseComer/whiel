-- Author: Jesse Comer
import Mathlib.Logic.Function.Defs
import Whiel.Vampire.SolverName

/-
  An injective escape encoding of an arbitrary string into
  the TPTP identifier alphabet `[a-z0-9_]`.

  A lowercase ASCII letter or digit stands for itself.
  Everything else — an uppercase letter, an underscore, a
  space, a control character, any non-ASCII character —
  becomes `_` followed by exactly six lowercase hexadecimal
  digits of its code point. The width is fixed at six
  because a Unicode code point is below `16 ^ 6`, so the
  decoder reads a group of a known size and never looks for
  a terminator. That keeps the decoder structurally
  recursive, and the round-trip theorem below is what makes
  the encoding injective.
-/

namespace Whiel

namespace Vampire

namespace SolverName

namespace Escape

------------------------------------------------------------
-- Hexadecimal Digits
------------------------------------------------------------

/- One lowercase hexadecimal digit. -/
def hexDigitChar (value : Nat) : Char :=
  if value < 10 then
    Char.ofNat ('0'.toNat + value)
  else
    Char.ofNat ('a'.toNat + (value - 10))

/- The value of one lowercase hexadecimal digit. -/
def hexDigitValue (c : Char) : Option Nat :=
  if c.isDigit then
    some (c.toNat - '0'.toNat)
  else if 'a'.toNat ≤ c.toNat && c.toNat ≤ 'f'.toNat then
    some (c.toNat - 'a'.toNat + 10)
  else
    none

theorem hexDigitValue_hexDigitChar
    (value : Nat)
    (hValue : value < 16) :
    hexDigitValue (hexDigitChar value) = some value := by
  have hDigits :
      ∀ value < 16,
        hexDigitValue (hexDigitChar value) = some value := by
    decide
  exact hDigits value hValue

theorem isAlphanum_hexDigitChar
    (value : Nat)
    (hValue : value < 16) :
    (hexDigitChar value).isAlphanum = true := by
  have hDigits :
      ∀ value < 16,
        (hexDigitChar value).isAlphanum = true := by
    decide
  exact hDigits value hValue

/- The two facts above at the residues the encoding uses. -/
private theorem hexDigitValue_hexDigitChar_mod
    (value : Nat) :
    hexDigitValue (hexDigitChar (value % 16)) =
      some (value % 16) :=
  hexDigitValue_hexDigitChar _ (Nat.mod_lt _ (by decide))

private theorem isAlphanum_hexDigitChar_mod
    (value : Nat) :
    (hexDigitChar (value % 16)).isAlphanum = true :=
  isAlphanum_hexDigitChar _ (Nat.mod_lt _ (by decide))

/- The six hexadecimal digits of one code point. -/
def hexValue
    (d5 d4 d3 d2 d1 d0 : Char) : Option Nat :=
  match hexDigitValue d5, hexDigitValue d4,
      hexDigitValue d3, hexDigitValue d2,
      hexDigitValue d1, hexDigitValue d0 with
  | some v5, some v4, some v3, some v2, some v1, some v0 =>
      some (v5 * 1048576 + v4 * 65536 + v3 * 4096 +
        v2 * 256 + v1 * 16 + v0)
  | _, _, _, _, _, _ => none

------------------------------------------------------------
-- The Encoding
------------------------------------------------------------

/- Escape one character into the identifier alphabet. -/
def escapeChar (c : Char) : List Char :=
  if c.isLower || c.isDigit then
    [c]
  else
    ['_',
      hexDigitChar (c.toNat / 1048576 % 16),
      hexDigitChar (c.toNat / 65536 % 16),
      hexDigitChar (c.toNat / 4096 % 16),
      hexDigitChar (c.toNat / 256 % 16),
      hexDigitChar (c.toNat / 16 % 16),
      hexDigitChar (c.toNat % 16)]

/- Escape a whole character list. -/
def escapeChars (chars : List Char) : List Char :=
  chars.flatMap escapeChar

/- Escape a whole string. -/
def escape (text : String) : String :=
  String.ofList (escapeChars text.toList)

------------------------------------------------------------
-- The Decoder
------------------------------------------------------------

/-
  Read an escaped character list back. An unescaped group is
  one self-standing character; an escaped group is `_` and
  six hexadecimal digits. Anything else is rejected, so the
  decoder is total on the alphabet and partial elsewhere.

  It is a left inverse of `escapeChars` only
  (`unescapeChars_escapeChars` below): it accepts every
  character list `escapeChars` can produce, but it is not a
  validator of names, because it also accepts character lists
  `escapeChars` never produces — an escaped group `_000061`
  decodes to the plain letter `a`, for instance, even though
  `escapeChars` would always have left a lowercase letter
  unescaped rather than spelling it out this way.
-/
def unescapeChars : List Char → Option (List Char)
| [] => some []
| c :: rest =>
    if c.isLower || c.isDigit then
      (unescapeChars rest).map (c :: ·)
    else if c = '_' then
      match rest with
      | d5 :: d4 :: d3 :: d2 :: d1 :: d0 :: tail =>
          match hexValue d5 d4 d3 d2 d1 d0 with
          | none => none
          | some value =>
              (unescapeChars tail).map
                (Char.ofNat value :: ·)
      | _ => none
    else
      none

/- Read an escaped string back. -/
def unescape? (text : String) : Option String :=
  (unescapeChars text.toList).map String.ofList

------------------------------------------------------------
-- Round Trip
------------------------------------------------------------

/- Every character's code point is below `16 ^ 6`. -/
private theorem toNat_lt_pow
    (c : Char) :
    c.toNat < 16777216 := by
  have hValid := c.valid
  unfold Nat.isValidChar at hValid
  change c.val.toNat < 16777216
  omega

private theorem hexValue_escapeChar
    (c : Char) :
    hexValue
        (hexDigitChar (c.toNat / 1048576 % 16))
        (hexDigitChar (c.toNat / 65536 % 16))
        (hexDigitChar (c.toNat / 4096 % 16))
        (hexDigitChar (c.toNat / 256 % 16))
        (hexDigitChar (c.toNat / 16 % 16))
        (hexDigitChar (c.toNat % 16)) =
      some c.toNat := by
  have hBound := toNat_lt_pow c
  simp only [hexValue, hexDigitValue_hexDigitChar_mod,
    Option.some.injEq]
  omega

theorem unescapeChars_escapeChar_append
    (c : Char)
    (suffix : List Char) :
    unescapeChars (escapeChar c ++ suffix) =
      (unescapeChars suffix).map (c :: ·) := by
  by_cases hPlain : (c.isLower || c.isDigit) = true
  · simp only [escapeChar, hPlain, if_true,
      List.cons_append, List.nil_append]
    rw [unescapeChars.eq_def]
    simp [hPlain]
  · have hEscaped : (c.isLower || c.isDigit) = false := by
      simpa using hPlain
    simp only [escapeChar, hEscaped, Bool.false_eq_true,
      if_false, List.cons_append, List.nil_append]
    rw [unescapeChars.eq_def]
    simp [hexValue_escapeChar c]

theorem unescapeChars_escapeChars
    (chars : List Char) :
    unescapeChars (escapeChars chars) = some chars := by
  induction chars with
  | nil => rfl
  | cons c rest ih =>
      have hSplit :
          escapeChars (c :: rest) =
            escapeChar c ++ escapeChars rest := by
        simp [escapeChars]
      rw [hSplit, unescapeChars_escapeChar_append, ih]
      rfl

/- Escaped strings read back as themselves. -/
theorem unescape?_escape
    (text : String) :
    unescape? (escape text) = some text := by
  simp [unescape?, escape, unescapeChars_escapeChars]

/- Distinct strings get distinct escapes. -/
theorem escape_injective :
    Function.Injective escape := by
  intro left right hEq
  have hDecoded := congrArg unescape? hEq
  rw [unescape?_escape, unescape?_escape] at hDecoded
  exact Option.some.inj hDecoded

------------------------------------------------------------
-- Legality of the Alphabet
------------------------------------------------------------

private theorem all_legal_escapeChar
    (c : Char) :
    (escapeChar c).all legalTptpChar = true := by
  by_cases hPlain : (c.isLower || c.isDigit) = true
  · have hAlphanum : c.isAlphanum = true := by
      unfold Char.isAlphanum Char.isAlpha
      rcases Bool.or_eq_true _ _ |>.mp hPlain with h | h <;>
        simp [h]
    simp [escapeChar, hPlain, legalTptpChar, hAlphanum]
  · have hEscaped : (c.isLower || c.isDigit) = false := by
      simpa using hPlain
    simp only [escapeChar, hEscaped, Bool.false_eq_true,
      if_false]
    simp [legalTptpChar, isAlphanum_hexDigitChar_mod]

/- Every escaped character list is TPTP-identifier text. -/
theorem all_legal_escapeChars
    (chars : List Char) :
    (escapeChars chars).all legalTptpChar = true := by
  induction chars with
  | nil => rfl
  | cons c rest ih =>
      have hSplit :
          escapeChars (c :: rest) =
            escapeChar c ++ escapeChars rest := by
        simp [escapeChars]
      rw [hSplit]
      simp [all_legal_escapeChar c, ih]

end Escape

end SolverName

end Vampire

end Whiel
