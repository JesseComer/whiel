-- Author: Jesse Comer
import Lean
import Whiel.AssertExpr.Syntax
import Whiel.Cmd.Notation
import Whiel.Concrete.Data
import Whiel.Concrete.IndexAlphaName
import Whiel.Concrete.WhielNames.SurfaceSyntax
import Databases.Core.Notation
import Databases.Datalog.Notation
import Databases.UnnamedModel.Notation

/-
  Concrete syntax for Whiel's standard verification setup.

  Key declarations include:
    * `whielSch![...]`
    * `assert![...]`
    * `qfAssert![...]`
    * `guard![...]`
    * `whielCmd![...]`
    * `whiel![...]`
    * concrete `inst![...]`
    * `programSch![...]`
    * `programAssert![...]`
    * `programQF![...]`
    * `programCmd![...]`

  Literals elaborate to `Whiel.Concrete.Data`. Relation
  identifiers elaborate in one of two name styles, which
  share every parser, expansion, and elaborator.

  In the `whiel`/`assert` style, identifiers elaborate to
  `Whiel.Concrete.IndexAlphaName`.
  A name `X` denotes the base relation name with index `0`.
  A name `X_n`, for `n ≥ 2`, denotes the generated
  relation name with internal index `n - 1`.  Quantified
  generated names inherit arity from their base name in the
  free schema.
  Base names used in the formula must already belong to the
  free schema, and indexed names used in the formula must be
  quantified.

  In the `program` style, identifiers elaborate to
  `Whiel.Concrete.ProgramNames`. A name `X` denotes
  `ProgramNames.programSymbol X 0`, a name `X_aux` denotes
  `ProgramNames.auxiliarySymbol X 0`, and for a canonical
  decimal numeral `n ≥ 1` the names `X_n` and `X_aux_n`
  denote the same constructors at index `n`. Index zero has
  no suffix spelling, so `X_0` is rejected. Flags have no
  spelling. The notation does not enforce the raw index-zero
  discipline of input files; `Hoare.preprocess` decides
  `RawIndexZero` on the schema instead. Quantified names
  must be auxiliary names; they inherit arity from the
  program symbol with the same base in the free schema.

  Over an `UnnamedSchema Whiel.Concrete.WhielNames`, the
  `program` spelling denotes the `ordinary` copy and the
  postfix `∞` token (`R∞`, `T_aux∞`, `R_n∞`, `T_aux_n∞`)
  denotes the `prophecy` copy. `qfAssert!`, `guard!`,
  `assert!`, and their `program` variants select the style
  from the expected schema type; the legacy `IndexAlphaName`
  style is unchanged.

  In every command style, a block command (`WHILE … END`,
  `IF … END`, and the lowercase forms) may be followed
  directly by another command; the juxtaposition means the
  same as `END; …`.
-/

------------------------------------------------------------
-- Schema Extension
------------------------------------------------------------

namespace Whiel

namespace Concrete

namespace Notation

/-
  Which relation names an assertion may bind, and the free
  schema name whose arity each bound name inherits.
-/
class GeneratedNames (A : Type) where
  baseOf : A → A
  isGenerated : A → Bool

/- The base relation name for an indexed relation name. -/
def baseOf (X : IndexAlphaName) : IndexAlphaName where
  baseName := X.baseName
  index := 0

/- Indexed names with positive index are generated. -/
instance : GeneratedNames IndexAlphaName where
  baseOf := baseOf
  isGenerated X := X.index != 0

/-
  Auxiliary names and positive-index names are generated.
  Each inherits arity from the index-zero program symbol
  with the same base string. Flags have no base string and
  are never named by this notation.
-/
instance : GeneratedNames ProgramNames where
  baseOf name :=
    match name.baseName? with
    | some base => .programSymbol base 0
    | none => name
  isGenerated name :=
    match name with
    | .programSymbol _ index => index != 0
    | _ => Bool.true

/-
  Extend a schema by generated relation names. Old names
  keep their arities, and generated names
  inherit arity from their base names.
-/
def extendSchema
    {A : Type} [RelationNames A] [GeneratedNames A]
    (Γ : UnnamedSchema A)
    (extra : Finset A) :
    UnnamedSchema A where
  syms := Γ.syms ∪ extra
  arity := fun X =>
    if hOld : X.1 ∈ Γ.syms then
      Γ.arity ⟨X.1, hOld⟩
    else if hBase :
        GeneratedNames.baseOf X.1 ∈ Γ.syms then
      Γ.arity ⟨GeneratedNames.baseOf X.1, hBase⟩
    else
      0

/-
  Bound names must be generated names with a base name in
  the free schema.
-/
def namesWellFormed
    {A : Type} [RelationNames A] [GeneratedNames A]
    (Γ : UnnamedSchema A)
    (extra : Finset A) : Prop :=
  ∀ X, X ∈ extra →
    GeneratedNames.isGenerated X = Bool.true ∧
      GeneratedNames.baseOf X ∈ Γ.syms

instance
    {A : Type} [RelationNames A] [GeneratedNames A]
    (Γ : UnnamedSchema A)
    (extra : Finset A) :
    Decidable (namesWellFormed Γ extra) := by
  unfold namesWellFormed
  infer_instance

/- The generated schema extends the free schema. -/
theorem extendSchema_extensionOf
    {A : Type} [RelationNames A] [GeneratedNames A]
    (Γ : UnnamedSchema A)
    (extra : Finset A) :
    (extendSchema Γ extra).extensionOf Γ := by
  refine ⟨?_, ?_⟩
  · intro X hX
    exact Finset.mem_union.mpr (Or.inl hX)
  · intro X
    simp [UnnamedSchema.arity?, extendSchema, X.2]

/- Build an assertion from a generated-name extension. -/
def ofFormula
    {A : Type} [RelationNames A] [GeneratedNames A]
    {D : Type} [Domain D]
    {Γ : UnnamedSchema A}
    (extra : Finset A)
    (φ : QFAssertExpr D (extendSchema Γ extra))
    (_hNames : namesWellFormed Γ extra :=
      by decide +kernel) :
    AssertExpr D Γ where
  fullSchema := extendSchema Γ extra
  extendsFree := extendSchema_extensionOf Γ extra
  formula := φ

/- Build typed RA from checked raw RA. -/
def rawExpr
    {D : Type} [Domain D]
    {Γ : UnnamedSchema IndexAlphaName}
    {extra : Finset IndexAlphaName}
    (e : RawRAExpr IndexAlphaName D)
    (n : Nat)
    (h : e.arity? (extendSchema Γ extra) = some n :=
      by decide +kernel) :
    RAExpr D (extendSchema Γ extra) n where
  expr := e
  wf := h

/- Equality between checked raw RA expressions. -/
def eqRaw
    {D : Type} [Domain D]
    {Γ : UnnamedSchema IndexAlphaName}
    {extra : Finset IndexAlphaName}
    (e₁ e₂ : RawRAExpr IndexAlphaName D)
    (hSome :
      (e₁.arity? (extendSchema Γ extra)).isSome =
        Bool.true := by decide +kernel)
    (hEq :
      e₁.arity? (extendSchema Γ extra) =
        e₂.arity? (extendSchema Γ extra) :=
      by decide +kernel) :
    Guard D (extendSchema Γ extra) :=
  match h₁ : e₁.arity? (extendSchema Γ extra) with
  | some n =>
      have h₂ :
          e₂.arity? (extendSchema Γ extra) = some n := by
        rw [h₁] at hEq
        exact hEq.symm
      Guard.eq (rawExpr e₁ n h₁) (rawExpr e₂ n h₂)
  | none =>
      have hFalse : False := by
        simp [h₁] at hSome
      False.elim hFalse

/- Containment between checked raw RA expressions. -/
def subsetRaw
    {D : Type} [Domain D]
    {Γ : UnnamedSchema IndexAlphaName}
    {extra : Finset IndexAlphaName}
    (e₁ e₂ : RawRAExpr IndexAlphaName D)
    (hSome :
      (e₁.arity? (extendSchema Γ extra)).isSome =
        Bool.true := by decide +kernel)
    (hEq :
      e₁.arity? (extendSchema Γ extra) =
        e₂.arity? (extendSchema Γ extra) :=
      by decide +kernel) :
    Guard D (extendSchema Γ extra) :=
  match h₁ : e₁.arity? (extendSchema Γ extra) with
  | some n =>
      have h₂ :
          e₂.arity? (extendSchema Γ extra) = some n := by
        rw [h₁] at hEq
        exact hEq.symm
      Guard.subset
        (rawExpr e₁ n h₁)
        (rawExpr e₂ n h₂)
  | none =>
      have hFalse : False := by
        simp [h₁] at hSome
      False.elim hFalse

/- Equality with an arity-inferred empty relation. -/
def eqEmptyRight
    {D : Type} [Domain D]
    {Γ : UnnamedSchema IndexAlphaName}
    {extra : Finset IndexAlphaName}
    (e : RawRAExpr IndexAlphaName D)
    (hSome :
      (e.arity? (extendSchema Γ extra)).isSome =
        Bool.true := by decide +kernel) :
    Guard D (extendSchema Γ extra) :=
  match h : e.arity? (extendSchema Γ extra) with
  | some n =>
      Guard.eq (rawExpr e n h) (RAExpr.empty n)
  | none =>
      have hFalse : False := by
        simp [h] at hSome
      False.elim hFalse

/- Equality from an arity-inferred empty relation. -/
def eqEmptyLeft
    {D : Type} [Domain D]
    {Γ : UnnamedSchema IndexAlphaName}
    {extra : Finset IndexAlphaName}
    (e : RawRAExpr IndexAlphaName D)
    (hSome :
      (e.arity? (extendSchema Γ extra)).isSome =
        Bool.true := by decide +kernel) :
    Guard D (extendSchema Γ extra) :=
  match h : e.arity? (extendSchema Γ extra) with
  | some n =>
      Guard.eq (RAExpr.empty n) (rawExpr e n h)
  | none =>
      have hFalse : False := by
        simp [h] at hSome
      False.elim hFalse

/- Containment by an arity-inferred empty relation. -/
def subsetEmptyRight
    {D : Type} [Domain D]
    {Γ : UnnamedSchema IndexAlphaName}
    {extra : Finset IndexAlphaName}
    (e : RawRAExpr IndexAlphaName D)
    (hSome :
      (e.arity? (extendSchema Γ extra)).isSome =
        Bool.true := by decide +kernel) :
    Guard D (extendSchema Γ extra) :=
  match h : e.arity? (extendSchema Γ extra) with
  | some n =>
      Guard.subset (rawExpr e n h) (RAExpr.empty n)
  | none =>
      have hFalse : False := by
        simp [h] at hSome
      False.elim hFalse

/- Containment from an arity-inferred empty relation. -/
def subsetEmptyLeft
    {D : Type} [Domain D]
    {Γ : UnnamedSchema IndexAlphaName}
    {extra : Finset IndexAlphaName}
    (e : RawRAExpr IndexAlphaName D)
    (hSome :
      (e.arity? (extendSchema Γ extra)).isSome =
        Bool.true := by decide +kernel) :
    Guard D (extendSchema Γ extra) :=
  match h : e.arity? (extendSchema Γ extra) with
  | some n =>
      Guard.subset (RAExpr.empty n) (rawExpr e n h)
  | none =>
      have hFalse : False := by
        simp [h] at hSome
      False.elim hFalse

end Notation

end Concrete

end Whiel

------------------------------------------------------------
-- Indexed Name Parsing
------------------------------------------------------------

open Lean Macro

namespace Whiel

namespace Concrete

namespace Notation

private def parseIndexedIdent
    (stx : Syntax) :
    MacroM (String × Nat) := do
  let raw := stx.getId.toString
  match raw.splitOn "_" with
  | [base] =>
      if base.toList.all Char.isAlpha then
        pure (base, 0)
      else
        Macro.throwErrorAt stx
          "expected alphabetical relation name '{raw}'"
  | [base, suffix] =>
      if base.toList.all Char.isAlpha then
        match suffix.toNat? with
        | some n =>
            if 2 ≤ n then
              pure (base, n - 1)
            else
              Macro.throwErrorAt stx
                "indexed suffix must be at least 2"
        | none =>
          Macro.throwErrorAt stx
              "expected numeric indexed suffix"
      else
        Macro.throwErrorAt stx
          "expected an alphabetical base name, got '{base}'"
  | _ =>
      Macro.throwErrorAt stx
        "expected relation name X or generated name X_n"

private def indexedNameTerm
    (stx : Syntax) :
    MacroM Term := do
  let (base, index) ← parseIndexedIdent stx
  `(Whiel.Concrete.IndexAlphaName.mk
      (Whiel.Concrete.AlphaString.mk
        $(quote base) (by decide))
      $(quote index))

private def indexedNameTermWithIndex
    (stx : Syntax) :
    MacroM (Term × Nat) := do
  let (base, index) ← parseIndexedIdent stx
  let term ←
    `(Whiel.Concrete.IndexAlphaName.mk
        (Whiel.Concrete.AlphaString.mk
          $(quote base) (by decide))
        $(quote index))
  pure (term, index)

end Notation

end Concrete

end Whiel

------------------------------------------------------------
-- Program Name Parsing
------------------------------------------------------------

namespace Whiel

namespace Concrete

namespace Notation

/-
  A program-style identifier: its alphabetical base, whether
  it names an auxiliary, and its snapshot index.

  The spellings are `X`, `X_aux`, `X_n`, and `X_aux_n` for a
  canonical decimal numeral `n ≥ 1` (no leading zeros).
  Index zero is spelled without a suffix, so `X_0` and
  `X_aux_0` are rejected rather than read as synonyms: each
  name has exactly one spelling, the one the clause printer
  produces, so printed text always re-reads to the same
  name and text comparisons never see two spellings of one
  name.

  A flag is the reserved fourth form `flag_i_n`, read by
  `parseFlagIdent?` below back to exactly
  `ProgramNames.flagSymbol i n`. It cannot be confused with
  a program or auxiliary name, whatever the base: a base is
  a purely alphabetical `AlphaString`, so the three
  spellings above carry at most one numeric suffix, and
  their only three-segment form has the literal middle
  segment `aux`, whereas a flag has three segments whose
  last two are canonical decimal numerals. Both flag
  numerals are written out, index zero included, so a flag
  too has exactly one spelling.
-/
private structure ProgramIdent where
  base : String
  isAuxiliary : Bool
  index : Nat

/- A canonical decimal numeral, leading zeros rejected. -/
private def canonicalNumeral? (text : String) :
    Option Nat :=
  match text.toNat? with
  | some n => if toString n = text then some n else none
  | none => none

/-
  Read the reserved flag spelling `flag_i_n`. Both numerals
  are canonical and neither is elided, so the reading is
  exactly the inverse of `ProgramNames.spell` on a flag.
-/
private def parseFlagIdent? (raw : String) :
    Option (Nat × Nat) :=
  match raw.splitOn "_" with
  | ["flag", idText, indexText] => do
      let id ← canonicalNumeral? idText
      let index ← canonicalNumeral? indexText
      pure (id, index)
  | _ => none

/-
  Read a canonical positive decimal index suffix. `stem` is
  the spelling of the same name at index zero.
-/
private def parseProgramIndex
    (stx : Syntax)
    (raw stem suffix : String) :
    MacroM Nat := do
  match suffix.toNat? with
  | some 0 =>
      Macro.throwErrorAt stx
        s!"index zero is spelled without a suffix; write \
          '{stem}' instead of '{raw}'"
  | some n =>
      if toString n = suffix then
        pure n
      else
        Macro.throwErrorAt stx
          s!"index suffix of '{raw}' must be a canonical \
            decimal numeral without leading zeros"
  | none =>
      Macro.throwErrorAt stx
        s!"expected relation name X, X_n, or auxiliary \
          name X_aux, X_aux_n, got '{raw}'"

private def parseProgramIdent
    (stx : Syntax) :
    MacroM ProgramIdent := do
  let raw := stx.getId.toString
  let alphabetic (base : String) : MacroM String :=
    if !base.isEmpty && base.toList.all Char.isAlpha then
      pure base
    else
      Macro.throwErrorAt stx
        s!"expected an alphabetical relation name, \
          got '{raw}'"
  match raw.splitOn "_" with
  | [base] =>
      pure ⟨← alphabetic base, Bool.false, 0⟩
  | [base, "aux"] =>
      pure ⟨← alphabetic base, Bool.true, 0⟩
  | [base, suffix] =>
      let base ← alphabetic base
      let index ← parseProgramIndex stx raw base suffix
      pure ⟨base, Bool.false, index⟩
  | [base, "aux", suffix] =>
      let base ← alphabetic base
      let index ←
        parseProgramIndex stx raw (base ++ "_aux") suffix
      pure ⟨base, Bool.true, index⟩
  | _ =>
      Macro.throwErrorAt stx
        s!"expected relation name X, X_n, or auxiliary \
          name X_aux, X_aux_n, got '{raw}'"

private def programSpelledNameTerm
    (stx : Syntax) :
    MacroM Term := do
  let ident ← parseProgramIdent stx
  let baseTerm ←
    `(Whiel.Concrete.AlphaString.mk
        $(quote ident.base) (by decide))
  let indexTerm := quote ident.index
  if ident.isAuxiliary then
    `(Whiel.Concrete.ProgramNames.auxiliarySymbol
        $baseTerm $indexTerm)
  else
    `(Whiel.Concrete.ProgramNames.programSymbol
        $baseTerm $indexTerm)

/-
  The shared reader of a program-style relation identifier:
  the reserved flag spelling first, then the ordinary
  `X`, `X_aux`, `X_n` and `X_aux_n` spellings. It is the one
  name parser of the `program` style, used by `programSch!`,
  `programAssert!`, `programQF!` and `programCmd!` here, and
  by `programInst!` in `Whiel/Eval/CounterExample/InstanceNotation.lean`.
-/
def programNameTerm
    (stx : Syntax) :
    MacroM Term := do
  match parseFlagIdent? stx.getId.toString with
  | some (id, index) =>
      `(Whiel.Concrete.ProgramNames.flagSymbol
          $(quote id) $(quote index))
  | none => programSpelledNameTerm stx

private def programBoundNameTerm
    (stx : Syntax) :
    MacroM Term := do
  let ⟨base, isAuxiliary, _⟩ ← parseProgramIdent stx
  unless isAuxiliary do
    Macro.throwErrorAt stx
      s!"bound program-name relations must be auxiliary \
        names such as '{base}_aux'"
  programNameTerm stx

/-
  The ordinary copy of a program-style identifier. The
  canonical constructor-complete source of
  `WhielNames.SurfaceSyntax` is still accepted.
-/
private def whielOrdinaryNameTerm
    (stx : Syntax) :
    MacroM Term := do
  let raw := stx.getId.toString
  match
      Whiel.Concrete.WhielNames.SurfaceSyntax.parse raw with
  | .ok _ =>
      `(Whiel.Concrete.WhielNames.SurfaceSyntax.ofSource
        $(quote raw) (by decide +kernel))
  | .error _ =>
      let name ← programNameTerm stx
      `(Whiel.Concrete.WhielNames.ordinary $name)

/- The prophecy copy `X∞` of a program-style identifier. -/
private def whielProphecyNameTerm
    (stx : Syntax) :
    MacroM Term := do
  let name ← programNameTerm stx
  `(Whiel.Concrete.WhielNames.prophecy $name)

/- Styles without a prophecy copy reject `X∞`. -/
private def noProphecyNameTerm
    (stx : Syntax) :
    MacroM Term :=
  Macro.throwErrorAt stx
    "prophecy names 'X∞' are only available over \
      'WhielNames' schemas"

end Notation

end Concrete

end Whiel

------------------------------------------------------------
-- Name Styles
------------------------------------------------------------

namespace Whiel

namespace Concrete

namespace Notation

/-
  How relation identifiers elaborate in one concrete name
  carrier. `nameTerm` reads schema and free names, and
  `boundNameTerm` reads names bound by `∃`.
-/
private structure NameStyle where
  carrier : Name
  nameTerm : Syntax → MacroM Term
  boundNameTerm : Syntax → MacroM Term
  prophecyNameTerm : Syntax → MacroM Term

private def indexedStyle : NameStyle where
  carrier := ``Whiel.Concrete.IndexAlphaName
  nameTerm := indexedNameTerm
  boundNameTerm := indexedNameTerm
  prophecyNameTerm := noProphecyNameTerm

private def programStyle : NameStyle where
  carrier := ``Whiel.Concrete.ProgramNames
  nameTerm := programNameTerm
  boundNameTerm := programBoundNameTerm
  prophecyNameTerm := noProphecyNameTerm

private def whielNamesStyle : NameStyle where
  carrier := ``Whiel.Concrete.WhielNames
  nameTerm := whielOrdinaryNameTerm
  boundNameTerm := whielOrdinaryNameTerm
  prophecyNameTerm := whielProphecyNameTerm

private def carrierTerm (style : NameStyle) : Term :=
  mkCIdent style.carrier

private def namesFinsetOfTerms
    (style : NameStyle)
    (names : Array Term) :
    MacroM Term := do
  let carrier := carrierTerm style
  `(([$[$names],*] : List $carrier).toFinset)

private def namesFinset
    (style : NameStyle)
    (ids : Array (TSyntax `ident)) :
    MacroM Term := do
  let names ← ids.mapM fun id => style.nameTerm id.raw
  namesFinsetOfTerms style names

end Notation

end Concrete

end Whiel

------------------------------------------------------------
-- Indexed Schema Notation
------------------------------------------------------------

open Whiel.Concrete.Notation

declare_syntax_cat dbt_index_schema_symbols
syntax ident : dbt_index_schema_symbols
syntax "{" ident,* "}" : dbt_index_schema_symbols

declare_syntax_cat dbt_index_schema_entry
syntax "_" " (arity: " term ")" :
  dbt_index_schema_entry
syntax dbt_index_schema_symbols " (arity: " term ")" :
  dbt_index_schema_entry

syntax "whielSyms!{" ident,* "}" : term
syntax "whielSch![" dbt_index_schema_entry,* "]" : term

private inductive IndexSchemaEntry where
  | symbols : Array Term → Term → IndexSchemaEntry
  | fallback : Term → IndexSchemaEntry

private def indexSchemaSymbolsData
    (style : NameStyle)
    (symbols : TSyntax `dbt_index_schema_symbols) :
    MacroM (Array Term) := do
  match symbols with
  | `(dbt_index_schema_symbols| $X:ident) => do
      let XTerm ← style.nameTerm X.raw
      pure #[XTerm]
  | `(dbt_index_schema_symbols| { $[$Xs:ident],* }) => do
      if Xs.isEmpty then
        throwUnsupported
      else
        Xs.mapM fun X => style.nameTerm X.raw
  | _ =>
      throwUnsupported

private def indexSchemaEntryData
    (style : NameStyle)
    (entry : TSyntax `dbt_index_schema_entry) :
    MacroM IndexSchemaEntry := do
  match entry with
  | `(dbt_index_schema_entry| _ (arity: $n:term)) =>
      pure (.fallback n)
  | `(dbt_index_schema_entry|
      $symbols:dbt_index_schema_symbols
        (arity: $n:term)) => do
      let Xs ← indexSchemaSymbolsData style symbols
      pure (.symbols Xs n)
  | _ =>
      throwUnsupported

private partial def collectIndexSchemaEntries :
    List IndexSchemaEntry →
      MacroM (List (Term × Term) × Term)
| [] => do
    let zero ← `(0)
    pure ([], zero)
| [.fallback n] =>
    pure ([], n)
| .fallback _ :: _ =>
    throwUnsupported
| .symbols Xs n :: entries => do
    let (rest, fallback) ←
      collectIndexSchemaEntries entries
    pure (Xs.toList.map (fun X => (X, n)) ++ rest,
      fallback)

private partial def indexSchemaArityBody
    (entries : List (Term × Term))
    (fallback : Term) :
    MacroM Term := do
  match entries with
  | [] =>
      pure fallback
  | (X, n) :: rest => do
      let tail ← indexSchemaArityBody rest fallback
      `(if X.1 = $X then $n else $tail)

private def indexSchemaAritiesMatchFallback
    (entries : List (Term × Term))
    (fallback : Term) : Bool :=
  entries.all (fun entry => entry.2.raw == fallback.raw)

private def expandWhielSchema
    (style : NameStyle)
    (entries : Array (TSyntax `dbt_index_schema_entry)) :
    MacroM Term := do
  let parsed ← entries.mapM (indexSchemaEntryData style)
  let (pairs, fallback) ←
    collectIndexSchemaEntries parsed.toList
  let body ←
    if indexSchemaAritiesMatchFallback pairs fallback then
      pure fallback
    else
      indexSchemaArityBody pairs fallback
  let syms := (pairs.map Prod.fst).toArray
  if syms.isEmpty then
    let carrier := carrierTerm style
    `({ syms := (∅ : Finset $carrier)
        arity := fun X => $body })
  else
    `((let _hNoDup : [$[$syms],*].Nodup :=
          by decide
       { syms := List.toFinset [$[$syms],*]
         arity := fun X => $body }))

macro "whielSyms!{" Xs:ident,* "}" : term => do
    let names ← namesFinset indexedStyle Xs
    pure names

macro "whielSch![" entries:dbt_index_schema_entry,* "]" :
    term => do
  expandWhielSchema indexedStyle entries

macro "programSch![" entries:dbt_index_schema_entry,* "]" :
    term => do
  expandWhielSchema programStyle entries

------------------------------------------------------------
-- Surface Notation
------------------------------------------------------------

private def expandDataLiteral
    (t : Term) :
    MacroM Term := do
  match t with
  | `($s:str) =>
      `(Whiel.Concrete.Data.str $s)
  | `($n:num) =>
      `(Whiel.Concrete.Data.num $n)
  | _ => do
      match t.raw with
      | .ident _ _ id _ =>
          if id == ``Bool.true ||
              id == Name.mkSimple "true" then
            `(Whiel.Concrete.Data.bool Bool.true)
          else if id == ``Bool.false ||
              id == Name.mkSimple "false" then
            `(Whiel.Concrete.Data.bool Bool.false)
          else
            pure t
      | _ =>
          pure t

------------------------------------------------------------
-- Concrete Instance Notation
------------------------------------------------------------

namespace Whiel

namespace Concrete

namespace Notation

/-
  A relation with a numeric arity, before schema checking.
-/
inductive InstanceEntry where
  | empty (baseName : String) (index : Nat)
  | nonempty
      (baseName : String)
      (index : Nat)
      (arity : Nat)
      (relation : FinRelation Data arity)

namespace InstanceEntry

/- Whether an entry names a schema symbol. -/
def matchesName
    (entry : InstanceEntry)
    (X : IndexAlphaName) : Bool :=
  match entry with
  | .empty baseName index =>
      baseName == X.baseName.value && index == X.index
  | .nonempty baseName index _ _ =>
      baseName == X.baseName.value && index == X.index

end InstanceEntry

/- Convert ordinary rows to a numerically typed relation. -/
def relationFromRows
    (n : Nat)
    (rows : List (List Data)) :
    FinRelation Data n :=
  rows.foldl
    (fun R row =>
      if h : row.length = n then
        insert
          (Vector.ofFn fun i =>
            row.get (Fin.cast h.symm i))
          R
      else
        R)
    ∅

/- Build one relation from shallow row-list chunks. -/
def chunkedRelation
    (n : Nat)
    (chunks : List (List (List Data))) :
    FinRelation Data n :=
  chunks.foldl
    (fun R rows => R ∪ relationFromRows n rows)
    ∅

/- Split on one separator; mirrors `String.splitOn`. -/
private def splitCharsOn
    (sep : Char) :
    List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | c :: cs, acc =>
      if c = sep then
        acc.reverse :: splitCharsOn sep cs []
      else
        splitCharsOn sep cs (c :: acc)

/- Digits to a value; mirrors `String.toNat?`. -/
private def natOfDigits?
    (cell : List Char) : Option Nat :=
  match cell with
  | [] => none
  | _ =>
      cell.foldl
        (fun acc c =>
          acc.bind fun value =>
            if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then
              some (10 * value + (c.toNat - 48))
            else
              none)
        (some 0)

private def decodeNaturalRow
    (row : List Char) : Option (List Data) :=
  (splitCharsOn ',' row []).mapM fun cell =>
    (natOfDigits? cell).map Data.num

/-
  Decode the compact form used for all-natural relations.
  Structural recursion only: invalidity certificates must
  kernel-reduce through this decoder, and `String.splitOn`
  or `String.toNat?` would strand the kernel on `Acc.rec`.
-/
def encodedNaturalRelation
    (n : Nat)
    (encoded : String) :
    FinRelation Data n :=
  if n = 0 then
    relationFromRows n [[]]
  else
    relationFromRows n
      ((splitCharsOn ';' encoded.toList []).filterMap
        decodeNaturalRow)

/- Compute schema arities from proof-free parsed names. -/
def schemaAritiesForRawNames
    (Γ : UnnamedSchema IndexAlphaName)
    (names : List (String × Nat)) :
    List (Option Nat) :=
  names.map fun (baseName, index) =>
    match AlphaString.ofString? baseName with
    | none => none
    | some base => Γ.arity? ⟨base, index⟩

/- Build an instance from checked concrete entries. -/
def instanceFromEntries
    (Γ : UnnamedSchema IndexAlphaName)
    (entries : List InstanceEntry) :
    Instance Data Γ :=
  fun X =>
    match entries.find?
        (fun entry => entry.matchesName X.1) with
    | none => ∅
    | some entry =>
        match entry with
        | .empty _ _ => ∅
        | .nonempty _ _ n R =>
            if h : n = Γ.arity X then
              cast (congrArg (FinRelation Data) h) R
            else
              ∅

end Notation

end Concrete

end Whiel

declare_syntax_cat dbt_concrete_inst_update

syntax ident " := " "[" "]" : dbt_concrete_inst_update
syntax ident " := " "[" "[" term,* "]"
  ("," "[" term,* "]")* "]" :
  dbt_concrete_inst_update

syntax (name := whielConcreteInstanceNotation)
  "inst![" term " | " dbt_concrete_inst_update
    ("; " dbt_concrete_inst_update)* "]" :
  term

declare_syntax_cat dbt_index_sel

syntax:max "#" num "=" "#" num : dbt_index_sel
syntax:max "#" num "=" term:70 : dbt_index_sel
syntax:66 dbt_index_sel:66 " ∧ " dbt_index_sel:67 :
  dbt_index_sel
syntax:61 dbt_index_sel:61 " ∨ " dbt_index_sel:62 :
  dbt_index_sel
syntax:70 "¬" dbt_index_sel:70 : dbt_index_sel
syntax:max "(" dbt_index_sel ")" : dbt_index_sel

private partial def expandIndexSel :
    TSyntax `dbt_index_sel → MacroM Term
| `(dbt_index_sel| #$i:num = #$j:num) =>
    `(Sel.eqIdx $i $j)
| `(dbt_index_sel| #$i:num = $c:term) => do
    let c' ← expandDataLiteral c
    `(Sel.eqConst $i $c')
| `(dbt_index_sel|
    $φ:dbt_index_sel ∧ $ψ:dbt_index_sel) => do
    let φt ← expandIndexSel φ
    let ψt ← expandIndexSel ψ
    `(Sel.and $φt $ψt)
| `(dbt_index_sel|
    $φ:dbt_index_sel ∨ $ψ:dbt_index_sel) => do
    let φt ← expandIndexSel φ
    let ψt ← expandIndexSel ψ
    `(Sel.or $φt $ψt)
| `(dbt_index_sel| ¬$φ:dbt_index_sel) => do
    let φt ← expandIndexSel φ
    `(Sel.not $φt)
| `(dbt_index_sel| ( $φ:dbt_index_sel )) =>
    expandIndexSel φ
| _ => Macro.throwUnsupported

declare_syntax_cat dbt_index_ra

syntax:max "⊤" : dbt_index_ra
syntax:max "∅[" term "]" : dbt_index_ra
syntax:max "{" term "}" : dbt_index_ra
syntax:max ident : dbt_index_ra
syntax:max ident "∞" : dbt_index_ra
syntax:80 "σ[" dbt_index_sel "]" dbt_index_ra:80 :
  dbt_index_ra
syntax:80 "π[" term,* "]" dbt_index_ra:80 :
  dbt_index_ra
syntax:71 dbt_index_ra:71 " × " dbt_index_ra:72 :
  dbt_index_ra
syntax:66 dbt_index_ra:66 " ∪ " dbt_index_ra:67 :
  dbt_index_ra
syntax:66 dbt_index_ra:66 " ∖ " dbt_index_ra:67 :
  dbt_index_ra
syntax:max "(" dbt_index_ra ")" : dbt_index_ra

private partial def expandIndexRA
    (style : NameStyle) :
    TSyntax `dbt_index_ra → MacroM Term
| `(dbt_index_ra| ⊤) =>
    `(RawRAExpr.top)
| `(dbt_index_ra| ∅[$n:term]) =>
    `(RawRAExpr.empty $n)
| `(dbt_index_ra| {$d:term}) => do
    let d' ← expandDataLiteral d
    `(RawRAExpr.single $d')
| `(dbt_index_ra| $X:ident) => do
    let XTerm ← style.nameTerm X.raw
    `(RawRAExpr.rel $XTerm)
| `(dbt_index_ra| $X:ident ∞) => do
    let XTerm ← style.prophecyNameTerm X.raw
    `(RawRAExpr.rel $XTerm)
| `(dbt_index_ra|
    σ[$φ:dbt_index_sel] $e:dbt_index_ra) => do
    let φt ← expandIndexSel φ
    let et ← expandIndexRA style e
    `(RawRAExpr.select $φt $et)
| `(dbt_index_ra|
    π[$idxs:term,*] $e:dbt_index_ra) => do
    let et ← expandIndexRA style e
    `(RawRAExpr.proj [$idxs,*] $et)
| `(dbt_index_ra|
    $e₁:dbt_index_ra × $e₂:dbt_index_ra) => do
    let e₁t ← expandIndexRA style e₁
    let e₂t ← expandIndexRA style e₂
    `(RawRAExpr.prod
      $e₁t
      $e₂t)
| `(dbt_index_ra|
    $e₁:dbt_index_ra ∪ $e₂:dbt_index_ra) => do
    let e₁t ← expandIndexRA style e₁
    let e₂t ← expandIndexRA style e₂
    `(RawRAExpr.union
      $e₁t
      $e₂t)
| `(dbt_index_ra|
    $e₁:dbt_index_ra ∖ $e₂:dbt_index_ra) => do
    let e₁t ← expandIndexRA style e₁
    let e₂t ← expandIndexRA style e₂
    `(RawRAExpr.diff
      $e₁t
      $e₂t)
| `(dbt_index_ra| ( $e:dbt_index_ra )) =>
    expandIndexRA style e
| _ => Macro.throwUnsupported

private def typedRelationTerm
    (expected? : Option (Term × Term))
    (XTerm : Term) :
    MacroM Term := do
  match expected? with
  | some (D, Γ) =>
      `(RAExpr.Notation.rel
        (D := $D) (Γ := $Γ)
        $XTerm
        (h := by decide +kernel))
  | none =>
      `(RAExpr.Notation.rel $XTerm
        (h := by decide +kernel))

private partial def expandIndexTypedRA
    (style : NameStyle)
    (expected? : Option (Term × Term)) :
    TSyntax `dbt_index_ra → MacroM Term
| `(dbt_index_ra| ⊤) =>
    match expected? with
    | some (D, Γ) =>
        `(RAExpr.top (D := $D) (Γ := $Γ))
    | none =>
        `(RAExpr.top)
| `(dbt_index_ra| ∅[$n:term]) =>
    match expected? with
    | some (D, Γ) =>
        `(RAExpr.empty (D := $D) (Γ := $Γ) $n)
    | none =>
        `(RAExpr.empty $n)
| `(dbt_index_ra| {$d:term}) => do
    let d' ← expandDataLiteral d
    match expected? with
    | some (D, Γ) =>
        `(RAExpr.single (D := $D) (Γ := $Γ) $d')
    | none =>
        `(RAExpr.single $d')
| `(dbt_index_ra| $X:ident) => do
    let XTerm ← style.nameTerm X.raw
    typedRelationTerm expected? XTerm
| `(dbt_index_ra| $X:ident ∞) => do
    let XTerm ← style.prophecyNameTerm X.raw
    typedRelationTerm expected? XTerm
| `(dbt_index_ra|
    σ[$φ:dbt_index_sel] $e:dbt_index_ra) => do
    let φt ← expandIndexSel φ
    let et ← expandIndexTypedRA style expected? e
    match expected? with
    | some (_D, Γ) =>
        `(RAExpr.select
          (Γ := $Γ)
          $φt
          $et
          (by decide +kernel))
    | none =>
        `(RAExpr.select $φt $et
          (by decide +kernel))
| `(dbt_index_ra|
    π[$idxs:term,*] $e:dbt_index_ra) => do
    let et ← expandIndexTypedRA style expected? e
    match expected? with
    | some (_D, Γ) =>
        `(RAExpr.proj
          (Γ := $Γ)
          [$idxs,*]
          $et
          (by decide +kernel))
    | none =>
        `(RAExpr.proj [$idxs,*] $et
          (by decide +kernel))
| `(dbt_index_ra|
    $e₁:dbt_index_ra × $e₂:dbt_index_ra) => do
    let e₁t ← expandIndexTypedRA style expected? e₁
    let e₂t ← expandIndexTypedRA style expected? e₂
    match expected? with
    | some (_D, Γ) =>
        `(RAExpr.prod (Γ := $Γ) $e₁t $e₂t)
    | none =>
        `(RAExpr.prod $e₁t $e₂t)
| `(dbt_index_ra|
    $e₁:dbt_index_ra ∪ $e₂:dbt_index_ra) => do
    let e₁t ← expandIndexTypedRA style expected? e₁
    let e₂t ← expandIndexTypedRA style expected? e₂
    match expected? with
    | some (_D, Γ) =>
        `(RAExpr.union (Γ := $Γ) $e₁t $e₂t)
    | none =>
        `(RAExpr.union $e₁t $e₂t)
| `(dbt_index_ra|
    $e₁:dbt_index_ra ∖ $e₂:dbt_index_ra) => do
    let e₁t ← expandIndexTypedRA style expected? e₁
    let e₂t ← expandIndexTypedRA style expected? e₂
    match expected? with
    | some (_D, Γ) =>
        `(RAExpr.diff (Γ := $Γ) $e₁t $e₂t)
    | none =>
        `(RAExpr.diff $e₁t $e₂t)
| `(dbt_index_ra| ( $e:dbt_index_ra )) =>
    expandIndexTypedRA style expected? e
| _ => Macro.throwUnsupported

declare_syntax_cat dbt_index_guard (behavior := both)

syntax &"true" : dbt_index_guard
syntax &"false" : dbt_index_guard
syntax dbt_index_ra " = " dbt_index_ra : dbt_index_guard
syntax dbt_index_ra " ⊆ " dbt_index_ra : dbt_index_guard
syntax dbt_index_ra " = " "∅" : dbt_index_guard
syntax "∅" " = " dbt_index_ra : dbt_index_guard
syntax dbt_index_ra " ⊆ " "∅" : dbt_index_guard
syntax "∅" " ⊆ " dbt_index_ra : dbt_index_guard
syntax dbt_index_ra " ≠ " dbt_index_ra : dbt_index_guard
syntax dbt_index_ra " ≠ " "∅" : dbt_index_guard
syntax "∅" " ≠ " dbt_index_ra : dbt_index_guard
syntax:66 dbt_index_guard:66 " ∧ " dbt_index_guard:67 :
  dbt_index_guard
syntax:61 dbt_index_guard:61 " ∨ " dbt_index_guard:62 :
  dbt_index_guard
syntax:70 "¬" dbt_index_guard:70 : dbt_index_guard
syntax:max "(" dbt_index_guard ")" : dbt_index_guard

private partial def expandIndexGuard
    (style : NameStyle)
    (expected? : Option (Term × Term)) :
    TSyntax `dbt_index_guard → MacroM Term
| `(dbt_index_guard| true) =>
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.«true» (D := $D) (Γ := $Γ))
    | none =>
        `(Whiel.Guard.«true»)
| `(dbt_index_guard| false) =>
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.«false» (D := $D) (Γ := $Γ))
    | none =>
        `(Whiel.Guard.«false»)
| `(dbt_index_guard|
    $e₁:dbt_index_ra = $e₂:dbt_index_ra) => do
    let e₁t ← expandIndexTypedRA style expected? e₁
    let e₂t ← expandIndexTypedRA style expected? e₂
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.eq
          (D := $D) (Γ := $Γ)
          $e₁t
          $e₂t)
    | none =>
        `(Whiel.Guard.eq
          $e₁t
          $e₂t)
| `(dbt_index_guard|
    $e₁:dbt_index_ra ⊆ $e₂:dbt_index_ra) => do
    let e₁t ← expandIndexTypedRA style expected? e₁
    let e₂t ← expandIndexTypedRA style expected? e₂
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.subset
          (D := $D) (Γ := $Γ)
          $e₁t
          $e₂t)
    | none =>
        `(Whiel.Guard.subset
          $e₁t
          $e₂t)
| `(dbt_index_guard| $e:dbt_index_ra = ∅) => do
    let et ← expandIndexTypedRA style expected? e
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.eq
          (D := $D) (Γ := $Γ)
          $et
          (RAExpr.empty (D := $D) (Γ := $Γ) _))
    | none =>
        `(Whiel.Guard.eq
          $et
          (RAExpr.empty _))
| `(dbt_index_guard| ∅ = $e:dbt_index_ra) => do
    let et ← expandIndexTypedRA style expected? e
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.eq
          (D := $D) (Γ := $Γ)
          (RAExpr.empty (D := $D) (Γ := $Γ) _)
          $et)
    | none =>
        `(Whiel.Guard.eq
          (RAExpr.empty _)
          $et)
| `(dbt_index_guard| $e:dbt_index_ra ⊆ ∅) => do
    let et ← expandIndexTypedRA style expected? e
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.subset
          (D := $D) (Γ := $Γ)
          $et
          (RAExpr.empty (D := $D) (Γ := $Γ) _))
    | none =>
        `(Whiel.Guard.subset
          $et
          (RAExpr.empty _))
| `(dbt_index_guard| ∅ ⊆ $e:dbt_index_ra) => do
    let et ← expandIndexTypedRA style expected? e
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.subset
          (D := $D) (Γ := $Γ)
          (RAExpr.empty (D := $D) (Γ := $Γ) _)
          $et)
    | none =>
        `(Whiel.Guard.subset
          (RAExpr.empty _)
          $et)
| `(dbt_index_guard|
    $e₁:dbt_index_ra ≠ $e₂:dbt_index_ra) => do
    let e₁t ← expandIndexTypedRA style expected? e₁
    let e₂t ← expandIndexTypedRA style expected? e₂
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.not
          (D := $D) (Γ := $Γ)
          (Whiel.Guard.eq
            (D := $D) (Γ := $Γ)
            $e₁t
            $e₂t))
    | none =>
        `(Whiel.Guard.not
          (Whiel.Guard.eq
            $e₁t
            $e₂t))
| `(dbt_index_guard| $e:dbt_index_ra ≠ ∅) => do
    let et ← expandIndexTypedRA style expected? e
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.not
          (D := $D) (Γ := $Γ)
          (Whiel.Guard.eq
            (D := $D) (Γ := $Γ)
            $et
            (RAExpr.empty (D := $D) (Γ := $Γ) _)))
    | none =>
        `(Whiel.Guard.not
          (Whiel.Guard.eq
            $et
            (RAExpr.empty _)))
| `(dbt_index_guard| ∅ ≠ $e:dbt_index_ra) => do
    let et ← expandIndexTypedRA style expected? e
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.not
          (D := $D) (Γ := $Γ)
          (Whiel.Guard.eq
            (D := $D) (Γ := $Γ)
            (RAExpr.empty (D := $D) (Γ := $Γ) _)
            $et))
    | none =>
        `(Whiel.Guard.not
          (Whiel.Guard.eq
            (RAExpr.empty _)
            $et))
| `(dbt_index_guard|
    $φ:dbt_index_guard ∧ $ψ:dbt_index_guard) => do
    let φt ← expandIndexGuard style expected? φ
    let ψt ← expandIndexGuard style expected? ψ
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.and
          (D := $D) (Γ := $Γ)
          $φt
          $ψt)
    | none =>
        `(Whiel.Guard.and
          $φt
          $ψt)
| `(dbt_index_guard|
    $φ:dbt_index_guard ∨ $ψ:dbt_index_guard) => do
    let φt ← expandIndexGuard style expected? φ
    let ψt ← expandIndexGuard style expected? ψ
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.or
          (D := $D) (Γ := $Γ)
          $φt
          $ψt)
    | none =>
        `(Whiel.Guard.or
          $φt
          $ψt)
| `(dbt_index_guard| ¬$φ:dbt_index_guard) => do
    let φt ← expandIndexGuard style expected? φ
    match expected? with
    | some (D, Γ) =>
        `(Whiel.Guard.not
          (D := $D) (Γ := $Γ)
          $φt)
    | none =>
        `(Whiel.Guard.not $φt)
| `(dbt_index_guard| ( $φ:dbt_index_guard )) =>
    expandIndexGuard style expected? φ
| _ => Macro.throwUnsupported

private partial def expandIndexRawGuard
    (style : NameStyle) :
    TSyntax `dbt_index_guard → MacroM Term
| `(dbt_index_guard| true) =>
    `(Whiel.RawGuard.«true»)
| `(dbt_index_guard| false) =>
    `(Whiel.RawGuard.«false»)
| `(dbt_index_guard|
    $e₁:dbt_index_ra = $e₂:dbt_index_ra) => do
    let e₁t ← expandIndexRA style e₁
    let e₂t ← expandIndexRA style e₂
    `(Whiel.RawGuard.eq $e₁t $e₂t)
| `(dbt_index_guard|
    $e₁:dbt_index_ra ⊆ $e₂:dbt_index_ra) => do
    let e₁t ← expandIndexRA style e₁
    let e₂t ← expandIndexRA style e₂
    `(Whiel.RawGuard.subset $e₁t $e₂t)
| `(dbt_index_guard| $e:dbt_index_ra = ∅) => do
    let et ← expandIndexRA style e
    `(Whiel.RawGuard.eqEmptyRight $et)
| `(dbt_index_guard| ∅ = $e:dbt_index_ra) => do
    let et ← expandIndexRA style e
    `(Whiel.RawGuard.eqEmptyLeft $et)
| `(dbt_index_guard| $e:dbt_index_ra ⊆ ∅) => do
    let et ← expandIndexRA style e
    `(Whiel.RawGuard.subsetEmptyRight $et)
| `(dbt_index_guard| ∅ ⊆ $e:dbt_index_ra) => do
    let et ← expandIndexRA style e
    `(Whiel.RawGuard.subsetEmptyLeft $et)
| `(dbt_index_guard|
    $e₁:dbt_index_ra ≠ $e₂:dbt_index_ra) => do
    let e₁t ← expandIndexRA style e₁
    let e₂t ← expandIndexRA style e₂
    `(Whiel.RawGuard.not
      (Whiel.RawGuard.eq $e₁t $e₂t))
| `(dbt_index_guard| $e:dbt_index_ra ≠ ∅) => do
    let et ← expandIndexRA style e
    `(Whiel.RawGuard.not
      (Whiel.RawGuard.eqEmptyRight $et))
| `(dbt_index_guard| ∅ ≠ $e:dbt_index_ra) => do
    let et ← expandIndexRA style e
    `(Whiel.RawGuard.not
      (Whiel.RawGuard.eqEmptyLeft $et))
| `(dbt_index_guard|
    $φ:dbt_index_guard ∧ $ψ:dbt_index_guard) => do
    let φt ← expandIndexRawGuard style φ
    let ψt ← expandIndexRawGuard style ψ
    `(Whiel.RawGuard.and $φt $ψt)
| `(dbt_index_guard|
    $φ:dbt_index_guard ∨ $ψ:dbt_index_guard) => do
    let φt ← expandIndexRawGuard style φ
    let ψt ← expandIndexRawGuard style ψ
    `(Whiel.RawGuard.or $φt $ψt)
| `(dbt_index_guard| ¬$φ:dbt_index_guard) => do
    let φt ← expandIndexRawGuard style φ
    `(Whiel.RawGuard.not $φt)
| `(dbt_index_guard| ( $φ:dbt_index_guard )) =>
    expandIndexRawGuard style φ
| _ => Macro.throwUnsupported

declare_syntax_cat dbt_index_cmd

syntax "skip" : dbt_index_cmd
syntax "SKIP" : dbt_index_cmd
syntax ident " := " "∅" : dbt_index_cmd
syntax ident " := " dbt_index_ra : dbt_index_cmd
syntax dbt_index_cmd:57 " ; " dbt_index_cmd:56 :
  dbt_index_cmd

/-
  A block command may be followed directly by the rest of
  the sequence, so `END` needs no `;`. The continuation is
  an optional part of the block rule itself rather than a
  trailing juxtaposition rule: it is attempted only after a
  closing `end`/`END`, so `X := R Y := S` is still a parse
  error, and no second leading parser competes for the same
  prefix. The continuation is read at the precedence of the
  right operand of `;`, so `END C; D` and `END; C; D` build
  the same right-nested sequence. A `;`, `}`, `)`, `ELSE`,
  or `END` after the block cannot start a command, so the
  optional part is skipped without consuming input and the
  existing forms parse as before.
-/
syntax
  "if " dbt_index_guard " then " dbt_index_cmd
    " else " dbt_index_cmd " end"
    (dbt_index_cmd:56)? : dbt_index_cmd
syntax
  "IF " dbt_index_guard " THEN " dbt_index_cmd
    " ELSE " dbt_index_cmd " END"
    (dbt_index_cmd:56)? : dbt_index_cmd
syntax
  "while " dbt_index_guard " do " dbt_index_cmd
    " end" (dbt_index_cmd:56)? : dbt_index_cmd
syntax
  "WHILE " dbt_index_guard " DO " dbt_index_cmd
    " END" (dbt_index_cmd:56)? : dbt_index_cmd
syntax "(" dbt_index_cmd ")" : dbt_index_cmd

/- Sequence a block command with its optional continuation. -/
private def sequenceContinuation
    (block : Term)
    (continuation? : Option Term) :
    MacroM Term := do
  match continuation? with
  | some continuation =>
      `(Whiel.RawCmd.seq $block $continuation)
  | none =>
      pure block

private partial def expandIndexCmd
    (style : NameStyle) :
    TSyntax `dbt_index_cmd → MacroM Term
| `(dbt_index_cmd| skip) =>
    `(Whiel.RawCmd.skip)
| `(dbt_index_cmd| SKIP) =>
    `(Whiel.RawCmd.skip)
| `(dbt_index_cmd| $X:ident := ∅) => do
    let XTerm ← style.nameTerm X.raw
    `(Whiel.RawCmd.assignEmpty $XTerm)
| `(dbt_index_cmd| $X:ident := $E:dbt_index_ra) => do
    let XTerm ← style.nameTerm X.raw
    let ERaw ← expandIndexRA style E
    `(Whiel.RawCmd.assign $XTerm $ERaw)
| `(dbt_index_cmd|
    $C₁:dbt_index_cmd ; $C₂:dbt_index_cmd) => do
    let C₁Raw ← expandIndexCmd style C₁
    let C₂Raw ← expandIndexCmd style C₂
    `(Whiel.RawCmd.seq $C₁Raw $C₂Raw)
| `(dbt_index_cmd|
    if $G:dbt_index_guard then
      $C₁:dbt_index_cmd
    else
      $C₂:dbt_index_cmd
    end $[$rest?:dbt_index_cmd]?) => do
    let GRaw ← expandIndexRawGuard style G
    let C₁Raw ← expandIndexCmd style C₁
    let C₂Raw ← expandIndexCmd style C₂
    let restRaw? ← rest?.mapM (expandIndexCmd style)
    sequenceContinuation
      (← `(Whiel.RawCmd.ite $GRaw $C₁Raw $C₂Raw))
      restRaw?
| `(dbt_index_cmd|
    IF $G:dbt_index_guard THEN
      $C₁:dbt_index_cmd
    ELSE
      $C₂:dbt_index_cmd
    END $[$rest?:dbt_index_cmd]?) => do
    let GRaw ← expandIndexRawGuard style G
    let C₁Raw ← expandIndexCmd style C₁
    let C₂Raw ← expandIndexCmd style C₂
    let restRaw? ← rest?.mapM (expandIndexCmd style)
    sequenceContinuation
      (← `(Whiel.RawCmd.ite $GRaw $C₁Raw $C₂Raw))
      restRaw?
| `(dbt_index_cmd|
    while $G:dbt_index_guard do $B:dbt_index_cmd end
      $[$rest?:dbt_index_cmd]?) => do
    let GRaw ← expandIndexRawGuard style G
    let BRaw ← expandIndexCmd style B
    let restRaw? ← rest?.mapM (expandIndexCmd style)
    sequenceContinuation
      (← `(Whiel.RawCmd.«while» $GRaw $BRaw))
      restRaw?
| `(dbt_index_cmd|
    WHILE $G:dbt_index_guard DO $B:dbt_index_cmd END
      $[$rest?:dbt_index_cmd]?) => do
    let GRaw ← expandIndexRawGuard style G
    let BRaw ← expandIndexCmd style B
    let restRaw? ← rest?.mapM (expandIndexCmd style)
    sequenceContinuation
      (← `(Whiel.RawCmd.«while» $GRaw $BRaw))
      restRaw?
| `(dbt_index_cmd| ( $B:dbt_index_cmd )) =>
    expandIndexCmd style B
| _ =>
    Macro.throwUnsupported

syntax (name := whielAssertQFNotation)
  "assert!" "[" dbt_index_guard "]" : term

syntax (name := programAssertQFNotation)
  "programAssert!" "[" dbt_index_guard "]" : term

macro "rawAssert!" "[" φ:dbt_index_guard "]" : term => do
    expandIndexRawGuard indexedStyle φ

syntax (name := whielGuardNotation)
  "guard!" "[" dbt_index_guard "]" : term

syntax (name := programGuardNotation)
  "programQF!" "[" dbt_index_guard "]" : term

macro "qfAssert!" "[" G:dbt_index_guard "]" : term =>
  `(guard![$G])

open Lean Elab Term Meta

private def expectedAssertComponents?
    (expectedType? : Option Expr) :
    TermElabM (Option (Expr × Expr)) := do
  let some expectedType := expectedType?
    | return none
  let expectedType ← whnf (← instantiateMVars expectedType)
  unless expectedType.getAppFn.isConstOf ``Whiel.AssertExpr do
    return none
  let args := expectedType.getAppArgs
  match args[2]?, args[4]? with
  | some D, some Γ =>
      return some (D, Γ)
  | _, _ =>
      return none

private def expectedGuardComponents?
    (expectedType? : Option Expr) :
    TermElabM (Option (Expr × Expr)) := do
  let some expectedType := expectedType?
    | return none
  let expectedType ← whnf (← instantiateMVars expectedType)
  unless expectedType.getAppFn.isConstOf ``Whiel.Guard do
    return none
  let args := expectedType.getAppArgs
  match args[2]?, args[4]? with
  | some D, some Γ =>
      return some (D, Γ)
  | _, _ =>
      return none

private def explicitExpectedTerms?
    (expected? : Option (Expr × Expr)) :
    TermElabM (Option (Term × Term)) := do
  match expected? with
  | some (D, Γ) => do
      let DTerm ← Term.exprToSyntax D
      let ΓTerm ← Term.exprToSyntax Γ
      return some (DTerm, ΓTerm)
  | none =>
      return none

private def natTerm (n : Nat) : Term :=
  ⟨Syntax.mkNumLit (toString n)⟩

private def optionSomePayload? (e : Expr) : Option Expr :=
  let e := e.consumeMData
  let (fn, args) := e.getAppFnArgs
  if toString fn = "Option.some" then
    args.back?
  else
    none

private partial def natValue? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  match e with
  | .lit (.natVal n) => some n
  | _ =>
      match e.nat? with
      | some n => some n
      | none =>
          let (fn, args) := e.getAppFnArgs
          if toString fn = "OfNat.ofNat" then
            args.findSome? natValue?
          else
            none

private def reduceToNat? (e : Expr) :
    TermElabM (Option Nat) := do
  let e ← instantiateMVars e
  let e ←
    withTransparency .all <|
      Lean.Meta.reduce e Bool.false Bool.true Bool.false
  return natValue? e

private def reduceToOptionNat? (e : Expr) :
    TermElabM (Option Nat) := do
  let e ← instantiateMVars e
  let e ←
    withTransparency .all <|
      Lean.Meta.reduce e Bool.false Bool.true Bool.false
  match optionSomePayload? e with
  | some value =>
      reduceToNat? value
  | none =>
      return none

private def canProveOptionNat
    (e : Expr)
    (n : Nat) :
    TermElabM Bool := do
  let someN ← mkAppM ``Option.some #[mkNatLit n]
  let prop ← mkEq e someN
  let prop ← instantiateMVars prop
  if prop.hasMVar then
    return Bool.false
  let decision ← mkAppM ``Decidable.decide #[prop]
  let decision ←
    withTransparency .all <|
      Lean.Meta.reduce decision
        Bool.false Bool.true Bool.false
  if decision.isConstOf ``Bool.true then
    return Bool.true
  else
    return Bool.false

private partial def findOptionNat
    (e : Expr)
    (n fuel : Nat) :
    TermElabM (Option Nat) := do
  if fuel = 0 then
    return none
  else
    let ok ← canProveOptionNat e n
    if ok then
      return some n
    else
      findOptionNat e (n + 1) (fuel - 1)

private def elabNatTermValue (t : Term) :
    TermElabM Nat := do
  let e ←
    Term.elabTermEnsuringType t (some (mkConst ``Nat))
  match ← reduceToNat? e with
  | some n =>
      return n
  | none =>
      throwErrorAt t
        "expected projection/arity index to reduce to a numeral"

private def relationArity
    (ΓExpr : Expr)
    (XTerm : Term) :
    TermElabM Nat := do
  let XExpr ←
    Term.elabTerm XTerm none
  Term.synthesizeSyntheticMVarsNoPostponing
  let XExpr ← instantiateMVars XExpr
  let arity? ←
    mkAppM ``UnnamedSchema.arity? #[ΓExpr, XExpr]
  let n? ← reduceToOptionNat? arity?
  let n? : Option Nat ←
    match n? with
    | some n => pure (some n)
    | none => findOptionNat arity? 0 129
  match n? with
  | some n =>
      return n
  | none =>
      throwErrorAt XTerm
        "unknown relation or non-computable relation arity"

private def relationNameTerm
    (style : NameStyle)
    (prophecy : Bool)
    (stx : Syntax) : TermElabM Term :=
  liftMacroM <|
    if prophecy then
      style.prophecyNameTerm stx
    else
      style.nameTerm stx

/-
  Select the name style from the carrier of an expected
  schema. Unknown carriers keep the macro's own style.
-/
private def styleForSchema
    (style : NameStyle)
    (ΓExpr : Expr) :
    TermElabM NameStyle := do
  let schemaType ← whnf (← inferType ΓExpr)
  let some carrier := schemaType.getAppArgs[0]?
    | return style
  let carrier ← whnf (← instantiateMVars carrier)
  if carrier.isConstOf ``Whiel.Concrete.WhielNames then
    return whielNamesStyle
  if carrier.isConstOf ``Whiel.Concrete.ProgramNames then
    return programStyle
  if carrier.isConstOf ``Whiel.Concrete.IndexAlphaName then
    return indexedStyle
  return style

private def elabConcreteData
    (t : Term) :
    TermElabM Expr := do
  if let some n := t.raw.isNatLit? then
    return mkApp
      (mkConst ``Whiel.Concrete.Data.num)
      (mkNatLit n)
  if let some s := t.raw.isStrLit? then
    return mkApp
      (mkConst ``Whiel.Concrete.Data.str)
      (mkStrLit s)
  match t.raw with
  | .ident _ _ id _ =>
      if id == ``Bool.true ||
          id == Name.mkSimple "true" then
        return mkApp
          (mkConst ``Whiel.Concrete.Data.bool)
          (mkConst ``Bool.true)
      if id == ``Bool.false ||
          id == Name.mkSimple "false" then
        return mkApp
          (mkConst ``Whiel.Concrete.Data.bool)
          (mkConst ``Bool.false)
  | _ =>
      pure ()
  Term.elabTermEnsuringType t
    (some (mkConst ``Whiel.Concrete.Data))

private def elabConcreteRow
    (terms : Array Term) :
    TermElabM Expr := do
  let values ← terms.mapM elabConcreteData
  Meta.mkListLit
    (mkConst ``Whiel.Concrete.Data)
    values.toList

private def naturalRow?
    (terms : Array Term) : Option (List Nat) :=
  terms.toList.mapM fun term =>
    term.raw.isNatLit?

private def encodeNaturalRows
    (rows : List (List Nat)) : String :=
  String.intercalate ";" <|
    rows.map fun row =>
      String.intercalate "," <|
        row.map toString

private structure ElaboratedInstanceEntry where
  key : String × Nat
  relationArity? : Option Nat
  value : Expr

private def elabConcreteInstanceEntry
    (entry : TSyntax `dbt_concrete_inst_update) :
    TermElabM ElaboratedInstanceEntry := do
  match entry with
  | `(dbt_concrete_inst_update| $X:ident := []) => do
      let key ← liftMacroM <| parseIndexedIdent X.raw
      let packed ←
        mkAppM
          ``Whiel.Concrete.Notation.InstanceEntry.empty
          #[mkStrLit key.1, mkNatLit key.2]
      return ⟨key, none, packed⟩
  | `(dbt_concrete_inst_update|
      $X:ident := [[$xs:term,*] $[,
        [$xss:term,*]]*]) => do
      let key ← liftMacroM <| parseIndexedIdent X.raw
      let n := xs.getElems.size
      for tuple in xss do
        if tuple.getElems.size != n then
          throwErrorAt entry
            "relation tuples must have the same arity"
      let relation ← do
        let rowTerms :=
          xs.getElems ::
            (xss.map fun tuple => tuple.getElems).toList
        match rowTerms.mapM naturalRow? with
        | some naturalRows =>
            mkAppM
              ``Whiel.Concrete.Notation.encodedNaturalRelation
              #[mkNatLit n,
                mkStrLit (encodeNaturalRows naturalRows)]
        | none => do
            let firstRow ← elabConcreteRow xs.getElems
            let restRows ← xss.mapM fun tuple =>
              elabConcreteRow tuple.getElems
            let listData :=
              mkApp (mkConst ``List [Level.zero])
                (mkConst ``Whiel.Concrete.Data)
            let rows := firstRow :: restRows.toList
            let rowChunks := rows.toChunks 8
            let chunks ← rowChunks.mapM fun chunk =>
              Meta.mkListLit listData chunk
            let listListData :=
              mkApp (mkConst ``List [Level.zero]) listData
            let chunks ←
              Meta.mkListLit listListData chunks
            mkAppM
              ``Whiel.Concrete.Notation.chunkedRelation
              #[mkNatLit n, chunks]
      let packed ←
        mkAppM
          ``Whiel.Concrete.Notation.InstanceEntry.nonempty
          #[mkStrLit key.1, mkNatLit key.2,
            mkNatLit n, relation]
      return ⟨key, some n, packed⟩
  | _ =>
      throwUnsupportedSyntax

private def ensureDistinctConcreteInstanceNames
    (entries : List ElaboratedInstanceEntry)
    (seen : List (String × Nat) := []) :
    TermElabM Unit := do
  match entries with
  | [] =>
      pure ()
  | entry :: rest =>
      if seen.contains entry.key then
        throwError
          "duplicate relation name in concrete instance"
      else
        ensureDistinctConcreteInstanceNames
          rest (entry.key :: seen)

private unsafe def checkConcreteInstanceArities
    (ΓExpr : Expr)
    (entries : List ElaboratedInstanceEntry) :
    TermElabM Unit := do
  let rawNameTypeStx ← `(String × Nat)
  let rawNameType ← Term.elabType rawNameTypeStx
  let rawNames ← entries.mapM fun entry =>
    mkAppM ``Prod.mk
      #[mkStrLit entry.key.1, mkNatLit entry.key.2]
  let rawNames ← Meta.mkListLit rawNameType rawNames
  let aritiesExpr ←
    mkAppM
      ``Whiel.Concrete.Notation.schemaAritiesForRawNames
      #[ΓExpr, rawNames]
  let aritiesTypeStx ← `(List (Option Nat))
  let aritiesType ← Term.elabType aritiesTypeStx
  let arities ←
    Meta.evalExpr (List (Option Nat))
      aritiesType aritiesExpr
  for (entry, actual?) in entries.zip arities do
    match actual?, entry.relationArity? with
    | none, _ =>
        throwError
          "unknown relation in concrete instance: \
            {entry.key.1}"
    | some actual, some expected =>
        if actual != expected then
          throwError
            "relation arity mismatch for {entry.key.1}: \
              schema has {actual}, notation has {expected}"
    | some _, none =>
        pure ()

@[term_elab whielConcreteInstanceNotation]
unsafe def elabWhielConcreteInstance :
    TermElab := fun stx _expectedType? => do
  match stx with
  | `(inst![$Γ:term | $entry:dbt_concrete_inst_update
      $[; $entries:dbt_concrete_inst_update]*]) => do
      let schemaTypeStx ←
        `(UnnamedSchema
          Whiel.Concrete.IndexAlphaName)
      let schemaType ← Term.elabType schemaTypeStx
      let ΓExpr ←
        Term.elabTermEnsuringType Γ (some schemaType)
      Term.synthesizeSyntheticMVarsNoPostponing
      let ΓExpr ← instantiateMVars ΓExpr
      let first ←
        elabConcreteInstanceEntry entry
      let rest ← entries.mapM fun next =>
        elabConcreteInstanceEntry next
      let packed := first :: rest.toList
      ensureDistinctConcreteInstanceNames packed
      checkConcreteInstanceArities ΓExpr packed
      let entryExprs := packed.map
        ElaboratedInstanceEntry.value
      let entryType :=
        Lean.mkConst
          ``Whiel.Concrete.Notation.InstanceEntry
      let entriesExpr ←
        Meta.mkListLit entryType entryExprs
      let result ←
        mkAppM
          ``Whiel.Concrete.Notation.instanceFromEntries
          #[ΓExpr, entriesExpr]
      return result
  | _ =>
      throwUnsupportedSyntax

private def typedRelationTermWithArity
    (D Γ : Term)
    (ΓExpr : Expr)
    (XTerm : Term) :
    TermElabM (Nat × Term) := do
  let n ← relationArity ΓExpr XTerm
  let nStx := natTerm n
  return (n, ←
    `(let XName := $XTerm
        let h : XName ∈ ($Γ).syms :=
          by decide +kernel
        RAExpr.castArity
          (D := $D) (Γ := $Γ) (m := $nStx)
          (by decide +kernel)
          (RAExpr.rel
            (D := $D) (Γ := $Γ)
            (UnnamedSchema.sym $Γ XName h))))

private partial def expandIndexTypedRAWithArity
    (style : NameStyle)
    (D Γ : Term)
    (ΓExpr : Expr) :
    TSyntax `dbt_index_ra → TermElabM (Nat × Term)
| `(dbt_index_ra| ⊤) =>
    return (0, ← `(RAExpr.top (D := $D) (Γ := $Γ)))
| `(dbt_index_ra| ∅[$n:term]) => do
    let nValue ← elabNatTermValue n
    return (nValue,
      ← `(RAExpr.empty (D := $D) (Γ := $Γ) $n))
| `(dbt_index_ra| {$d:term}) => do
    let d' ← liftMacroM <| expandDataLiteral d
    return (1,
      ← `(RAExpr.single (D := $D) (Γ := $Γ) $d'))
| `(dbt_index_ra| $X:ident) => do
    let XTerm ← relationNameTerm style Bool.false X.raw
    typedRelationTermWithArity D Γ ΓExpr XTerm
| `(dbt_index_ra| $X:ident ∞) => do
    let XTerm ← relationNameTerm style Bool.true X.raw
    typedRelationTermWithArity D Γ ΓExpr XTerm
| `(dbt_index_ra|
    σ[$φ:dbt_index_sel] $e:dbt_index_ra) => do
    let φt ← liftMacroM <| expandIndexSel φ
    let (n, et) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e
    return (n,
      ← `(RAExpr.select
          (Γ := $Γ)
          $φt
          $et
          (by decide +kernel)))
| `(dbt_index_ra|
    π[$idxs:term,*] $e:dbt_index_ra) => do
    let (_n, et) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e
    let outArity := idxs.getElems.size
    return (outArity,
      ← `(RAExpr.proj
          (Γ := $Γ)
          [$idxs,*]
          $et
          (by decide +kernel)))
| `(dbt_index_ra|
    $e₁:dbt_index_ra × $e₂:dbt_index_ra) => do
    let (n₁, e₁t) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e₁
    let (n₂, e₂t) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e₂
    return (n₁ + n₂,
      ← `(RAExpr.prod (Γ := $Γ) $e₁t $e₂t))
| `(dbt_index_ra|
    $e₁:dbt_index_ra ∪ $e₂:dbt_index_ra) => do
    let (n₁, e₁t) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e₁
    let (n₂, e₂t) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e₂
    if n₁ != n₂ then
      throwErrorAt e₂
        "union arity mismatch: left arity {n₁}, right arity {n₂}"
    return (n₁,
      ← `(RAExpr.union (Γ := $Γ) $e₁t $e₂t))
| `(dbt_index_ra|
    $e₁:dbt_index_ra ∖ $e₂:dbt_index_ra) => do
    let (n₁, e₁t) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e₁
    let (n₂, e₂t) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e₂
    if n₁ != n₂ then
      throwErrorAt e₂
        "difference arity mismatch: left arity {n₁}, right arity {n₂}"
    return (n₁,
      ← `(RAExpr.diff (Γ := $Γ) $e₁t $e₂t))
| `(dbt_index_ra| ( $e:dbt_index_ra )) =>
    expandIndexTypedRAWithArity style D Γ ΓExpr e
| _ =>
    throwUnsupportedSyntax

private partial def expandIndexGuardWithArity
    (style : NameStyle)
    (D Γ : Term)
    (ΓExpr : Expr) :
    TSyntax `dbt_index_guard → TermElabM Term
| `(dbt_index_guard| true) =>
    `(Whiel.Guard.«true» (D := $D) (Γ := $Γ))
| `(dbt_index_guard| false) =>
    `(Whiel.Guard.«false» (D := $D) (Γ := $Γ))
| `(dbt_index_guard|
    $e₁:dbt_index_ra = $e₂:dbt_index_ra) => do
    let (n₁, e₁t) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e₁
    let (n₂, e₂t) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e₂
    if n₁ != n₂ then
      throwErrorAt e₂
        "equality arity mismatch: left arity {n₁}, right arity {n₂}"
    `(Whiel.Guard.eq
      (D := $D) (Γ := $Γ)
      $e₁t
      $e₂t)
| `(dbt_index_guard|
    $e₁:dbt_index_ra ⊆ $e₂:dbt_index_ra) => do
    let (n₁, e₁t) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e₁
    let (n₂, e₂t) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e₂
    if n₁ != n₂ then
      throwErrorAt e₂
        "containment arity mismatch: left arity {n₁}, right arity {n₂}"
    `(Whiel.Guard.subset
      (D := $D) (Γ := $Γ)
      $e₁t
      $e₂t)
| `(dbt_index_guard| $e:dbt_index_ra = ∅) => do
    let (n, et) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e
    let nStx := natTerm n
    `(Whiel.Guard.eq
      (D := $D) (Γ := $Γ)
      $et
      (RAExpr.empty (D := $D) (Γ := $Γ) $nStx))
| `(dbt_index_guard| ∅ = $e:dbt_index_ra) => do
    let (n, et) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e
    let nStx := natTerm n
    `(Whiel.Guard.eq
      (D := $D) (Γ := $Γ)
      (RAExpr.empty (D := $D) (Γ := $Γ) $nStx)
      $et)
| `(dbt_index_guard| $e:dbt_index_ra ⊆ ∅) => do
    let (n, et) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e
    let nStx := natTerm n
    `(Whiel.Guard.subset
      (D := $D) (Γ := $Γ)
      $et
      (RAExpr.empty (D := $D) (Γ := $Γ) $nStx))
| `(dbt_index_guard| ∅ ⊆ $e:dbt_index_ra) => do
    let (n, et) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e
    let nStx := natTerm n
    `(Whiel.Guard.subset
      (D := $D) (Γ := $Γ)
      (RAExpr.empty (D := $D) (Γ := $Γ) $nStx)
      $et)
| `(dbt_index_guard|
    $e₁:dbt_index_ra ≠ $e₂:dbt_index_ra) => do
    let (n₁, e₁t) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e₁
    let (n₂, e₂t) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e₂
    if n₁ != n₂ then
      throwErrorAt e₂
        "disequality arity mismatch: left arity {n₁}, right arity {n₂}"
    `(Whiel.Guard.not
      (D := $D) (Γ := $Γ)
      (Whiel.Guard.eq
        (D := $D) (Γ := $Γ)
        $e₁t
        $e₂t))
| `(dbt_index_guard| $e:dbt_index_ra ≠ ∅) => do
    let (n, et) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e
    let nStx := natTerm n
    `(Whiel.Guard.not
      (D := $D) (Γ := $Γ)
      (Whiel.Guard.eq
        (D := $D) (Γ := $Γ)
        $et
        (RAExpr.empty (D := $D) (Γ := $Γ) $nStx)))
| `(dbt_index_guard| ∅ ≠ $e:dbt_index_ra) => do
    let (n, et) ←
      expandIndexTypedRAWithArity style D Γ ΓExpr e
    let nStx := natTerm n
    `(Whiel.Guard.not
      (D := $D) (Γ := $Γ)
      (Whiel.Guard.eq
        (D := $D) (Γ := $Γ)
        (RAExpr.empty (D := $D) (Γ := $Γ) $nStx)
        $et))
| `(dbt_index_guard|
    $φ:dbt_index_guard ∧ $ψ:dbt_index_guard) => do
    let φt ←
      expandIndexGuardWithArity style D Γ ΓExpr φ
    let ψt ←
      expandIndexGuardWithArity style D Γ ΓExpr ψ
    `(Whiel.Guard.and
      (D := $D) (Γ := $Γ)
      $φt
      $ψt)
| `(dbt_index_guard|
    $φ:dbt_index_guard ∨ $ψ:dbt_index_guard) => do
    let φt ←
      expandIndexGuardWithArity style D Γ ΓExpr φ
    let ψt ←
      expandIndexGuardWithArity style D Γ ΓExpr ψ
    `(Whiel.Guard.or
      (D := $D) (Γ := $Γ)
      $φt
      $ψt)
| `(dbt_index_guard| ¬$φ:dbt_index_guard) => do
    let φt ←
      expandIndexGuardWithArity style D Γ ΓExpr φ
    `(Whiel.Guard.not
      (D := $D) (Γ := $Γ)
      $φt)
| `(dbt_index_guard| ( $φ:dbt_index_guard )) =>
    expandIndexGuardWithArity style D Γ ΓExpr φ
| _ =>
    throwUnsupportedSyntax

private def elabAssertQF
    (style : NameStyle)
    (φ : TSyntax `dbt_index_guard)
    (expectedType? : Option Expr) :
    TermElabM Expr := do
  let expected? ← expectedAssertComponents? expectedType?
  match expected? with
  | some (D, Γ) => do
      let some (DTerm, ΓTerm) ←
          explicitExpectedTerms? expected?
        | throwUnsupportedSyntax
      let style ← styleForSchema style Γ
      let φt ←
        expandIndexGuardWithArity style DTerm ΓTerm Γ φ
      let expectedQF ←
        mkAppM ``Whiel.QFAssertExpr #[D, Γ]
      let φExpr ←
        Term.elabTermEnsuringType φt (some expectedQF)
      mkAppM ``Whiel.AssertExpr.ofQF #[φExpr]
  | none => do
      let φt ←
        liftMacroM <| expandIndexGuard style none φ
      let t ←
        `(Whiel.AssertExpr.ofQF
          $φt)
      Term.elabTerm t expectedType?

@[term_elab whielAssertQFNotation] def elabWhielAssertQF :
    TermElab := fun stx expectedType? => do
  match stx with
  | `(assert![$φ:dbt_index_guard]) =>
      elabAssertQF indexedStyle φ expectedType?
  | _ =>
      throwUnsupportedSyntax

@[term_elab programAssertQFNotation]
def elabProgramAssertQF :
    TermElab := fun stx expectedType? => do
  match stx with
  | `(programAssert![$φ:dbt_index_guard]) =>
      elabAssertQF programStyle φ expectedType?
  | _ =>
      throwUnsupportedSyntax

private def elabGuard
    (style : NameStyle)
    (G : TSyntax `dbt_index_guard)
    (expectedType? : Option Expr) :
    TermElabM Expr := do
  let expected? ← expectedGuardComponents? expectedType?
  let Gt ←
    match expected? with
    | some (_D, Γ) => do
        let some (DTerm, ΓTerm) ←
            explicitExpectedTerms? expected?
          | throwUnsupportedSyntax
        let style ← styleForSchema style Γ
        expandIndexGuardWithArity style DTerm ΓTerm Γ G
    | none =>
        liftMacroM <| expandIndexGuard style none G
  Term.elabTermEnsuringType Gt expectedType?

@[term_elab whielGuardNotation] def elabWhielGuard :
    TermElab := fun stx expectedType? => do
  match stx with
  | `(guard![$G:dbt_index_guard]) =>
      elabGuard indexedStyle G expectedType?
  | _ =>
      throwUnsupportedSyntax

@[term_elab programGuardNotation] def elabProgramGuard :
    TermElab := fun stx expectedType? => do
  match stx with
  | `(programQF![$G:dbt_index_guard]) =>
      elabGuard programStyle G expectedType?
  | _ =>
      throwUnsupportedSyntax

private def expandCmdNotation
    (style : NameStyle)
    (Γ : Term)
    (C : TSyntax `dbt_index_cmd) :
    MacroM Term := do
  let raw ← expandIndexCmd style C
  let carrier := carrierTerm style
  `(let Γ : UnnamedSchema $carrier := $Γ
    (Whiel.RawCmd.toCmd (Γ := Γ) $raw))

macro
  "whielCmd![" "{" "ExecSchema" ":"
      entries:dbt_index_schema_entry,* "}"
    "{" C:dbt_index_cmd "}" "]" : term => do
  let Γ ← expandWhielSchema indexedStyle entries
  expandCmdNotation indexedStyle Γ C

macro
  "whielCmd![" "{" "ExecSchema" ":" Γ:term "}"
    "{" C:dbt_index_cmd "}" "]" : term => do
  expandCmdNotation indexedStyle Γ C

macro
  "programCmd![" "{" "ExecSchema" ":"
      entries:dbt_index_schema_entry,* "}"
    "{" C:dbt_index_cmd "}" "]" : term => do
  let Γ ← expandWhielSchema programStyle entries
  expandCmdNotation programStyle Γ C

macro
  "programCmd![" "{" "ExecSchema" ":" Γ:term "}"
    "{" C:dbt_index_cmd "}" "]" : term => do
  expandCmdNotation programStyle Γ C

macro
  "whiel![" "{" "ExecSchema" ":" Γ:term "}"
    "{" "Input" ":" Δ:term "}"
    "{" C:dbt_index_cmd "}"
    "{" "Return" ":" Λ:term "}" "]" : term => do
  let raw ← expandIndexCmd indexedStyle C
  `(let Γ :
      UnnamedSchema Whiel.Concrete.IndexAlphaName := $Γ
    Whiel.Program.Notation.ofExec
      (Γ := Γ) (Δ := $Δ) (Λ := $Λ)
      (by decide) (by decide)
      (Whiel.RawCmd.toCmd (Γ := Γ) $raw))

macro
  "whiel![" "{" "ExecSchema" ":" Γ:term "}"
    "{" "Input" ":" "{" inputs:ident,* "}" "}"
    "{" "Return" ":" "{" outputs:ident,* "}" "}"
    "{" C:dbt_index_cmd "}" "]" : term => do
  let inputSyms ← namesFinset indexedStyle inputs
  let outputSyms ← namesFinset indexedStyle outputs
  let raw ← expandIndexCmd indexedStyle C
  `(let Γ :
      UnnamedSchema Whiel.Concrete.IndexAlphaName := $Γ
    Whiel.Program.Notation.ofExec
      (Γ := Γ)
      (Δ :=
        UnnamedSchema.restrict Γ $inputSyms (by decide))
      (Λ :=
        UnnamedSchema.restrict Γ $outputSyms (by decide))
      (UnnamedSchema.extensionOf_restrict
        Γ $inputSyms (by decide))
      (UnnamedSchema.extensionOf_restrict
        Γ $outputSyms (by decide))
      (Whiel.RawCmd.toCmd (Γ := Γ) $raw))

macro
  "whiel![" "{" "ExecSchema" ":"
      entries:dbt_index_schema_entry,* "}"
    "{" "Input" ":" "{" inputs:ident,* "}" "}"
    "{" "Return" ":" "{" outputs:ident,* "}" "}"
    "{" C:dbt_index_cmd "}" "]" : term => do
  let Γ ← expandWhielSchema indexedStyle entries
  let inputSyms ← namesFinset indexedStyle inputs
  let outputSyms ← namesFinset indexedStyle outputs
  let raw ← expandIndexCmd indexedStyle C
  `(let Γ :
      UnnamedSchema Whiel.Concrete.IndexAlphaName := $Γ
    Whiel.Program.Notation.ofExec
      (Γ := Γ)
      (Δ :=
        UnnamedSchema.restrict Γ $inputSyms (by decide))
      (Λ :=
        UnnamedSchema.restrict Γ $outputSyms (by decide))
      (UnnamedSchema.extensionOf_restrict
        Γ $inputSyms (by decide))
      (UnnamedSchema.extensionOf_restrict
        Γ $outputSyms (by decide))
      (Whiel.RawCmd.toCmd (Γ := Γ) $raw))

syntax (name := whielAssertBoundNotation)
  "assert!" "[" "∃" ident "." dbt_index_guard "]" : term

syntax (name := whielAssertBoundSetNotation)
  "assert!" "[" "∃" "{" ident,* "}" "."
    dbt_index_guard "]" : term

syntax (name := programAssertBoundNotation)
  "programAssert!" "[" "∃" ident "."
    dbt_index_guard "]" : term

syntax (name := programAssertBoundSetNotation)
  "programAssert!" "[" "∃" "{" ident,* "}" "."
    dbt_index_guard "]" : term

/-
  Elaborate a bound-symbol assertion. With a known expected
  type, the extended schema is elaborated first so that the
  formula is checked against concrete arities; otherwise
  the formula is left to unification.
-/
private def elabBoundAssert
    (style : NameStyle)
    (Xs : Array (TSyntax `ident))
    (φ : TSyntax `dbt_index_guard)
    (expectedType? : Option Expr) :
    TermElabM Expr := do
  let names ← liftMacroM <|
    Xs.mapM fun X => style.boundNameTerm X.raw
  let extra ← liftMacroM <| namesFinsetOfTerms style names
  let expected? ← expectedAssertComponents? expectedType?
  match expected? with
  | some (_D, Γ) => do
      let some (DTerm, ΓTerm) ←
          explicitExpectedTerms? expected?
        | throwUnsupportedSyntax
      let extendedTerm ← `(extendSchema $ΓTerm $extra)
      let extendedExpr ←
        Term.elabTermEnsuringType extendedTerm
          (some (← inferType Γ))
      Term.synthesizeSyntheticMVarsNoPostponing
      let extendedExpr ← instantiateMVars extendedExpr
      let extendedStx ← Term.exprToSyntax extendedExpr
      let φt ←
        expandIndexGuardWithArity style
          DTerm extendedStx extendedExpr φ
      let t ←
        `(ofFormula (D := $DTerm) (Γ := $ΓTerm)
          $extra $φt)
      Term.elabTerm t expectedType?
  | none => do
      let φt ←
        liftMacroM <| expandIndexGuard style none φ
      let t ←
        `(ofFormula
          (extra := $extra)
          (φ :=
            ($φt :
              Whiel.QFAssertExpr _
                (extendSchema _ $extra))))
      Term.elabTerm t expectedType?

@[term_elab whielAssertBoundNotation]
def elabWhielAssertBound :
    TermElab := fun stx expectedType? => do
  match stx with
  | `(assert![∃ $X:ident . $φ:dbt_index_guard]) =>
      elabBoundAssert indexedStyle #[X] φ expectedType?
  | _ =>
      throwUnsupportedSyntax

@[term_elab whielAssertBoundSetNotation]
def elabWhielAssertBoundSet :
    TermElab := fun stx expectedType? => do
  match stx with
  | `(assert![∃ { $[$Xs:ident],* } .
        $φ:dbt_index_guard]) =>
      elabBoundAssert indexedStyle Xs φ expectedType?
  | _ =>
      throwUnsupportedSyntax

@[term_elab programAssertBoundNotation]
def elabProgramAssertBound :
    TermElab := fun stx expectedType? => do
  match stx with
  | `(programAssert![∃ $X:ident . $φ:dbt_index_guard]) =>
      elabBoundAssert programStyle #[X] φ expectedType?
  | _ =>
      throwUnsupportedSyntax

@[term_elab programAssertBoundSetNotation]
def elabProgramAssertBoundSet :
    TermElab := fun stx expectedType? => do
  match stx with
  | `(programAssert![∃ { $[$Xs:ident],* } .
        $φ:dbt_index_guard]) =>
      elabBoundAssert programStyle Xs φ expectedType?
  | _ =>
      throwUnsupportedSyntax
