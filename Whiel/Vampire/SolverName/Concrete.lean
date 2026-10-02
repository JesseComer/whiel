-- Author: Jesse Comer
import Whiel.Concrete.Data
import Whiel.Concrete.IndexAlphaName
import Whiel.Concrete.WhielNames.SurfaceSyntax
import Whiel.Vampire.SolverName
import Whiel.Vampire.SolverName.Escape

/-
  Solver names for the concrete carriers.

  A relation is named by its clause source, the spelling
  agents already read and write, so the solver, the clause
  text and `Core.json` agree on one identifier. A constant
  is named `k`, a kind letter and an injective encoding of
  the value: decimal for a number, one letter for a Boolean,
  and the escape encoding for an arbitrary string.

  The two letter conventions are what keep the names apart
  from each other and from the shapes a solver reserves for
  itself. A relation name begins with the copy tag `o` or
  `y` and a constant name with `k`, so no reserved word, no
  introduced-symbol shape and no constant name is ever a
  relation name.

  `IndexAlphaName`, the relation carrier of the one-shot
  manifest path, is named by the shared fallback at the end
  of this file and proves nothing; the renderer's refusal is
  what protects it.
-/

namespace Whiel

namespace Vampire

open Concrete

------------------------------------------------------------
-- Relation Names
------------------------------------------------------------

instance solverNameWhielNames : SolverName WhielNames where
  solverName := WhielNames.SurfaceSyntax.source

/- The solver name of a relation is its clause source. -/
theorem solverName_whielNames
    (name : WhielNames) :
    solverName name = WhielNames.SurfaceSyntax.source name :=
  rfl

------------------------------------------------------------
-- Identifier Characters of a Relation Name
------------------------------------------------------------

private theorem all_legalTptpChar_of_isAlphanum
    {chars : List Char}
    (hAlphanum : chars.all Char.isAlphanum = true) :
    chars.all legalTptpChar = true := by
  rw [List.all_eq_true] at hAlphanum ⊢
  intro c hMem
  simp [legalTptpChar, hAlphanum c hMem]

private theorem all_legalTptpChar_repr
    (value : Nat) :
    value.repr.toList.all legalTptpChar = true := by
  rw [Nat.toList_repr, List.all_eq_true]
  intro c hMem
  have hDigit : c.isDigit :=
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) hMem
  simp [legalTptpChar, Char.isAlphanum, hDigit]

private theorem all_legalTptpChar_indexRun
    (index : Nat)
    {payload : List Char}
    (hPayload : payload.all legalTptpChar = true) :
    (List.replicate index 's' ++ 'z' :: payload).all
      legalTptpChar = true := by
  simp [List.all_replicate, legalTptpChar, hPayload]

/-
  Every relation name is a copy tag, a family tag, `_`, and
  identifier characters. That single shape carries legality,
  the exclusion of the reserved spellings, and disjointness
  from the constant names.
-/
theorem solverName_whielNames_toList
    (name : WhielNames) :
    ∃ outer inner rest,
      (outer = 'o' ∨ outer = 'y') ∧
      (inner = 'p' ∨ inner = 'a' ∨ inner = 'f') ∧
      rest.all legalTptpChar = true ∧
      (solverName name).toList =
        outer :: inner :: '_' :: rest := by
  obtain ⟨outer, inner, index, payload, hOuter, hInner,
    hPayload, hChars⟩ :=
      WhielNames.SurfaceSyntax.toList_source name
  exact ⟨outer, inner, _, hOuter, hInner,
    all_legalTptpChar_indexRun index
      (all_legalTptpChar_of_isAlphanum hPayload),
    hChars⟩

------------------------------------------------------------
-- Constant Names
------------------------------------------------------------

/-
  The solver name of one concrete domain value: `k`, a kind
  letter, and an injective ASCII encoding of the value.
-/
def dataSolverName : Data → String
| .num value => "kn" ++ toString value
| .str value => "ks" ++ SolverName.Escape.escape value
| .bool false => "kbf"
| .bool true => "kbt"

/- Decode one constant name back to its value. -/
def dataOfSolverName? (name : String) : Option Data :=
  match name.toList with
  | 'k' :: 'n' :: payload =>
      (String.ofList payload).toNat?.map Data.num
  | 'k' :: 's' :: payload =>
      (SolverName.Escape.unescape?
        (String.ofList payload)).map Data.str
  | ['k', 'b', 'f'] => some (.bool false)
  | ['k', 'b', 't'] => some (.bool true)
  | _ => none

instance solverNameData : SolverName Data where
  solverName := dataSolverName

/- Constant names round-trip through the decoder. -/
theorem dataOfSolverName?_solverName
    (value : Data) :
    dataOfSolverName? (solverName value) = some value := by
  cases value with
  | num value =>
      have hChars :
          (solverName (Data.num value)).toList =
            'k' :: 'n' :: Nat.toDigits 10 value := by
        change ("kn" ++ toString value).toList = _
        rw [String.toList_append]
        simp [Nat.toString_eq_repr, Nat.toList_repr]
      rw [dataOfSolverName?, hChars]
      change Option.map Data.num
        (String.ofList (Nat.toDigits 10 value)).toNat? = _
      rw [← Nat.toString_eq_ofList_toDigits]
      simp [Nat.toString_eq_repr, Nat.toNat?_repr]
  | str value =>
      have hChars :
          (solverName (Data.str value)).toList =
            'k' :: 's' ::
              (SolverName.Escape.escape value).toList := by
        change
          ("ks" ++ SolverName.Escape.escape value).toList = _
        rw [String.toList_append]
        simp
      rw [dataOfSolverName?, hChars]
      change Option.map Data.str
        (SolverName.Escape.unescape?
          (String.ofList
            (SolverName.Escape.escape value).toList)) = _
      simp [SolverName.Escape.unescape?_escape]
  | bool value =>
      cases value <;> rfl

/- Every constant name is `k` and identifier characters. -/
theorem solverName_data_toList
    (value : Data) :
    ∃ rest,
      rest.all legalTptpChar = true ∧
      (solverName value).toList = 'k' :: rest := by
  cases value with
  | num value =>
      refine ⟨'n' :: value.repr.toList, ?_, ?_⟩
      · simp only [List.all_cons, Bool.and_eq_true]
        exact ⟨by decide, all_legalTptpChar_repr value⟩
      · change ("kn" ++ toString value).toList = _
        simp [String.toList_append, Nat.toString_eq_repr]
  | str value =>
      refine ⟨'s' ::
        SolverName.Escape.escapeChars value.toList, ?_, ?_⟩
      · simp only [List.all_cons, Bool.and_eq_true]
        exact ⟨by decide,
          SolverName.Escape.all_legal_escapeChars _⟩
      · change
          ("ks" ++ SolverName.Escape.escape value).toList = _
        simp [String.toList_append, SolverName.Escape.escape]
  | bool value =>
      cases value
      · exact ⟨['b', 'f'], by decide, by decide⟩
      · exact ⟨['b', 't'], by decide, by decide⟩

------------------------------------------------------------
-- The Production Obligations
------------------------------------------------------------

/- Distinct relations get distinct solver names. -/
theorem solverName_whielNames_injective :
    Function.Injective (solverName (α := WhielNames)) := by
  intro left right hEq
  have hParsed := congrArg WhielNames.SurfaceSyntax.parse hEq
  rw [solverName_whielNames, solverName_whielNames,
    WhielNames.SurfaceSyntax.parse_source,
    WhielNames.SurfaceSyntax.parse_source] at hParsed
  exact Except.ok.inj hParsed

/- Every relation name is a legal TPTP `lower_word`. -/
theorem legalTptpName_solverName_whielNames
    (name : WhielNames) :
    legalTptpName (solverName name) = true := by
  obtain ⟨outer, inner, rest, hOuter, hInner, hRest,
    hChars⟩ := solverName_whielNames_toList name
  refine legalTptpName_of_toList hChars ?_ ?_
  · rcases hOuter with rfl | rfl <;> decide
  · rcases hInner with rfl | rfl | rfl <;>
      simpa [legalTptpChar] using hRest

/- Distinct constants get distinct solver names. -/
theorem solverName_data_injective :
    Function.Injective (solverName (α := Data)) := by
  intro left right hEq
  have hDecoded := congrArg dataOfSolverName? hEq
  rw [dataOfSolverName?_solverName,
    dataOfSolverName?_solverName] at hDecoded
  exact Option.some.inj hDecoded

/- Every constant name is a legal TPTP `lower_word`. -/
theorem legalTptpName_solverName_data
    (value : Data) :
    legalTptpName (solverName value) = true := by
  obtain ⟨rest, hRest, hChars⟩ :=
    solverName_data_toList value
  exact legalTptpName_of_toList hChars (by decide)
    (by simpa [legalTptpChar] using hRest)

instance lawfulSolverNameWhielNames :
    LawfulSolverName WhielNames where
  solverName_injective := solverName_whielNames_injective
  legalTptpName_solverName :=
    legalTptpName_solverName_whielNames

instance lawfulSolverNameData : LawfulSolverName Data where
  solverName_injective := solverName_data_injective
  legalTptpName_solverName := legalTptpName_solverName_data

------------------------------------------------------------
-- Reserved Shapes and Disjointness
------------------------------------------------------------

/- No relation name is a reserved TPTP word. -/
theorem not_isReservedWord_solverName_whielNames
    (name : WhielNames) :
    isReservedWord (solverName name) = false := by
  obtain ⟨outer, inner, rest, hOuter, _, _, hChars⟩ :=
    solverName_whielNames_toList name
  refine not_isReservedWord_of_firstChar hChars ?_
  rcases hOuter with rfl | rfl <;> decide

/- No constant name is a reserved TPTP word. -/
theorem not_isReservedWord_solverName_data
    (value : Data) :
    isReservedWord (solverName value) = false := by
  obtain ⟨rest, _, hChars⟩ := solverName_data_toList value
  exact not_isReservedWord_of_firstChar hChars (by decide)

/- No relation name has Vampire's introduced-symbol shape. -/
theorem not_isIntroducedShape_solverName_whielNames
    (name : WhielNames) :
    isIntroducedShape (solverName name) = false := by
  obtain ⟨outer, inner, rest, hOuter, _, _, hChars⟩ :=
    solverName_whielNames_toList name
  refine not_isIntroducedShape_of_firstChar hChars ?_
  rcases hOuter with rfl | rfl <;> decide

/- No constant name has Vampire's introduced-symbol shape. -/
theorem not_isIntroducedShape_solverName_data
    (value : Data) :
    isIntroducedShape (solverName value) = false := by
  obtain ⟨rest, _, hChars⟩ := solverName_data_toList value
  exact not_isIntroducedShape_of_firstChar hChars (by decide)

/- A relation and a constant never share a solver name. -/
theorem solverName_whielNames_ne_solverName_data
    (name : WhielNames)
    (value : Data) :
    solverName name ≠ solverName value := by
  obtain ⟨outer, inner, rest, hOuter, _, _, hName⟩ :=
    solverName_whielNames_toList name
  obtain ⟨restValue, _, hValue⟩ :=
    solverName_data_toList value
  refine ne_of_firstChar hName hValue ?_
  rcases hOuter with rfl | rfl <;> decide

------------------------------------------------------------
-- The One-Shot Manifest Carrier
------------------------------------------------------------

/-
  `IndexAlphaName` carries a schema written by hand rather
  than a fixed-ambient program, so it has no clause source to
  reuse. It keeps the spelling the renderer gave it before
  names were proved, and nothing is claimed about it.

  On the legacy encoding-worker path
  (`Synthesis/Runtime/EncodingWorker.lean`) the names a
  binding carries are Rust's own (`rel:<Base>:<index>` to
  `r_<index>z<Base>`, in
  `whiel_runner/src/encoding/solver_name.rs`), not this
  spelling: that worker checks a bound name's legality and
  the absence of repeats and cross-kind clashes, but does not
  compare it against `solverName` here, so the two are not
  required to agree.
-/
instance solverNameIndexAlphaName :
    SolverName IndexAlphaName where
  solverName := SolverName.ofRepr "r"

end Vampire

end Whiel
