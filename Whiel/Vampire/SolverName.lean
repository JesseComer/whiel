-- Author: Jesse Comer
import Mathlib.Logic.Function.Defs

/-
  Solver-facing names for symbol carriers.

  A symbol has a wire key, a clause source and a display
  spelling. Its solver name is the identifier a solver
  reads, and it is one of those spellings rather than a
  fourth: for the production carriers below it is the clause
  source. This module gives a carrier that name and states
  what the carrier must prove before the renderer may hand
  its names to a solver unchanged, with no freshening pass
  in between.

  The class itself is deliberately lawless. A carrier used
  only by a test or a one-shot encoding supplies a name
  function and is protected by the renderer's refusal.
  `LawfulSolverName` is what a production carrier proves:
  distinct symbols get distinct names, and every name is a
  legal TPTP `lower_word`. Reserved-shape exclusion and
  cross-carrier disjointness are stated here as predicates
  and proved per carrier, because they are properties of a
  pair of carriers rather than of one.
-/

namespace Whiel

namespace Vampire

------------------------------------------------------------
-- The Class
------------------------------------------------------------

/- The solver-facing name of one symbol. -/
class SolverName (α : Type) where
  solverName : α → String

export SolverName (solverName)

/- A carrier with no symbols names nothing. -/
instance : SolverName Empty where
  solverName := Empty.elim

------------------------------------------------------------
-- Legal Identifiers
------------------------------------------------------------

/- The characters a `lower_word` admits after its first. -/
def legalTptpChar (c : Char) : Bool :=
  c.isAlphanum || c = '_'

/-
  A TPTP `lower_word`: nonempty, an ASCII lowercase letter
  first, then ASCII alphanumerics and underscores. In the
  pinned toolchain `Char.isLower`, `Char.isAlpha` and
  `Char.isAlphanum` are all ASCII-only, so no non-ASCII
  character satisfies this.

  This is also the condition the encoding workers apply to
  an incoming name binding
  (`Synthesis/Runtime/FixedAmbientWorker.lean` and
  `Synthesis/Runtime/EncodingWorker.lean`), which call it
  here rather than repeating it.
-/
def legalTptpName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
      first.isLower && rest.all legalTptpChar

/-
  What a production carrier proves. Injectivity is what lets
  the renderer assign names by applying the function, and
  legality is what lets it emit them unquoted.
-/
class LawfulSolverName
    (α : Type) [SolverName α] : Prop where
  solverName_injective :
    Function.Injective (solverName (α := α))
  legalTptpName_solverName :
    ∀ x : α, legalTptpName (solverName x) = true

------------------------------------------------------------
-- A Name For Carriers Without One
------------------------------------------------------------

/- Keep only TPTP-friendly identifier characters. -/
def sanitizeChar (c : Char) : Char :=
  if c.isAlphanum then c else '_'

/- Sanitize a string for use in a generated identifier. -/
def sanitize (s : String) : String :=
  String.ofList (s.toList.map sanitizeChar)

namespace SolverName

/-
  A name for a carrier with no proved naming: a lowercase
  prefix, `_`, and the sanitized `Repr` spelling. This is the
  spelling the renderer produced for every carrier before
  solver names were proved, and it is kept so that a test or
  registry carrier needs no encoding of its own.

  It proves nothing. Two symbols whose spellings differ only
  outside `[A-Za-z0-9_]` receive the same name, so a carrier
  named this way is protected only by the checks on the
  environment it lands in: `NameEnv.wellFormed` decides
  whether the names repeat, and the two consumers that read
  an environment refuse a repeated one. Do not use it for a
  carrier whose names reach a certificate.
-/
def ofRepr
    {α : Type}
    [Repr α]
    (namePrefix : String)
    (x : α) : String :=
  namePrefix ++ "_" ++ sanitize (reprStr x)

end SolverName

------------------------------------------------------------
-- Reserved Shapes
------------------------------------------------------------

/-
  Words whose reading in a TPTP problem depends on position: a
  conservative set of TPTP keywords covering the four language
  selectors this toolchain recognizes, the inclusion directive
  and the two formula roles this project emits. A symbol
  spelled as one of these is readable but invites a
  misreading — and in argument position a `lower_word` cannot
  be misparsed as one of them regardless — so production
  carriers prove they never produce one.

  This list is not decided by `NameEnv.wellFormed`
  (`Vampire/TPTP.lean`); it is proved of each production
  carrier's names as a separate theorem.
-/
def reservedWords : List String :=
  ["fof", "cnf", "tff", "thf", "include", "axiom",
    "conjecture"]

/- Whether a name is one of the reserved words. -/
def isReservedWord (name : String) : Bool :=
  reservedWords.contains name

/-
  Vampire spells the symbols it introduces itself as `s`
  followed by an uppercase letter (`sK12`, `sP3`, `sF7`), so
  a rendered symbol of that shape could be confused with one
  of them when a proof or a countermodel is read back.

  This is not decided by `NameEnv.wellFormed`
  (`Vampire/TPTP.lean`); it is proved of each production
  carrier's names as a separate theorem.
-/
def isIntroducedShape (name : String) : Bool :=
  match name.toList with
  | first :: second :: _ => first = 's' && second.isUpper
  | _ => false

------------------------------------------------------------
-- Reading a Name Off Its Characters
------------------------------------------------------------

/- Legality from the first character and the rest. -/
theorem legalTptpName_of_toList
    {name : String}
    {first : Char}
    {rest : List Char}
    (hChars : name.toList = first :: rest)
    (hFirst : first.isLower = true)
    (hRest : rest.all legalTptpChar = true) :
    legalTptpName name = true := by
  simp [legalTptpName, hChars, hFirst, hRest]

/-
  A name is none of the reserved words as soon as its first
  character is none of theirs.
-/
theorem not_isReservedWord_of_firstChar
    {name : String}
    {first : Char}
    {rest : List Char}
    (hChars : name.toList = first :: rest)
    (hFirst :
      ∀ word ∈ reservedWords,
        word.toList.head? ≠ some first) :
    isReservedWord name = false := by
  have hNotMem : name ∉ reservedWords := by
    intro hMem
    exact hFirst name hMem (by simp [hChars])
  simpa [isReservedWord] using hNotMem

/- No introduced-symbol shape unless the name starts `s`. -/
theorem not_isIntroducedShape_of_firstChar
    {name : String}
    {first : Char}
    {rest : List Char}
    (hChars : name.toList = first :: rest)
    (hFirst : first ≠ 's') :
    isIntroducedShape name = false := by
  unfold isIntroducedShape
  rw [hChars]
  cases rest with
  | nil => rfl
  | cons second tail =>
      simp [hFirst]

/- Different first characters make different names. -/
theorem ne_of_firstChar
    {left right : String}
    {firstLeft firstRight : Char}
    {restLeft restRight : List Char}
    (hLeft : left.toList = firstLeft :: restLeft)
    (hRight : right.toList = firstRight :: restRight)
    (hFirst : firstLeft ≠ firstRight) :
    left ≠ right := by
  intro hEq
  apply hFirst
  have hLists : left.toList = right.toList :=
    congrArg String.toList hEq
  rw [hLeft, hRight] at hLists
  exact (List.cons.inj hLists).1

end Vampire

end Whiel
