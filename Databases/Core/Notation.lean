-- Author: Jesse Comer
import Databases.Core.NamedSchema
import Databases.Core.Signature

/-
  Typed notation for shared database examples.

  Key declarations include:
    * `tuple![...]`
    * `finrel![...]`
    * `sch![...]`
    * `namedSch![...]`
    * `sig![...]`
    * `DBLib.Notation.Literal`
    * `DBLib.Notation.PrettyLiteral`
-/

------------------------------------------------------------
-- Tuple And Relation Literals
------------------------------------------------------------

syntax "tuple![" term,* "]" : term

macro_rules
| `(tuple![$[$xs:term],*]) =>
    `(Vector.mk #[ $[$xs],* ] (by decide))

syntax "finrel![" term,* "]" : term

macro_rules
| `(finrel![]) =>
    `(∅)
| `(finrel![$[$ts:term],*]) =>
    `(List.toFinset [$[$ts],*])

------------------------------------------------------------
-- Unnamed Schema Literals
------------------------------------------------------------

open Lean Macro

declare_syntax_cat dbt_arity_entry
syntax term " (arity: " term ")" : dbt_arity_entry

declare_syntax_cat dbt_schema_symbols
syntax term : dbt_schema_symbols
syntax "{" term,* "}" : dbt_schema_symbols

declare_syntax_cat dbt_schema_entry
syntax "_" " (arity: " term ")" : dbt_schema_entry
syntax dbt_schema_symbols " (arity: " term ")" :
  dbt_schema_entry

namespace UnnamedSchema

namespace Notation

variable {A : Type} [RelationNames A]

/- Build a duplicate-free unnamed schema. -/
def fromList
    (entries : List (A × Nat))
    (_hNoDup : (entries.map Prod.fst).Nodup) :
    UnnamedSchema A where
  syms := (entries.map Prod.fst).toFinset
  arity := fun X =>
    match entries.find? (fun entry => entry.1 = X.1) with
    | some entry => entry.2
    | none => 0

end Notation

end UnnamedSchema

private inductive SchemaEntry where
  | symbols : Array Term → Term → SchemaEntry
  | fallback : Term → SchemaEntry

private def commaListTerms (stx : Syntax) :
    Array Term :=
  stx.getArgs.filterMap fun arg =>
    match arg with
    | .atom _ "," => none
    | other => some ⟨other⟩

private def arityEntryPair
    (entry : TSyntax `dbt_arity_entry) :
    MacroM Term := do
  match entry with
  | `(dbt_arity_entry| $X:term (arity: $n:term)) =>
      `(($X, $n))
  | _ =>
      throwUnsupported

/-
  Brace groups are ambiguous with term syntax, so Lean
  stores them as parser choices.
-/
private partial def schemaSymbolsData
    (symbols : TSyntax `dbt_schema_symbols) :
    MacroM (Array Term) := do
  match symbols.raw with
  | .node _ `choice choices =>
      match choices.back? with
      | some symbols' =>
          return ← schemaSymbolsData ⟨symbols'⟩
      | none =>
          throwUnsupported
  | .node _ `«dbt_schema_symbols{_}» args =>
      match args[1]? with
      | some rawTerms =>
          let Xs := commaListTerms rawTerms
          if Xs.isEmpty then
            throwUnsupported
          else
            return Xs
      | none =>
          throwUnsupported
  | _ =>
      pure ()
  match symbols with
  | `(dbt_schema_symbols| $X:term) =>
      pure #[X]
  | `(dbt_schema_symbols| { $[$Xs:term],* }) =>
      if Xs.isEmpty then
        throwUnsupported
      else
        pure Xs
  | _ =>
      throwUnsupported

private def schemaEntryData
    (entry : TSyntax `dbt_schema_entry) :
    MacroM SchemaEntry := do
  match entry with
  | `(dbt_schema_entry| _ (arity: $n:term)) =>
      pure (.fallback n)
  | `(dbt_schema_entry|
      $symbols:dbt_schema_symbols (arity: $n:term)) => do
      pure (.symbols (← schemaSymbolsData symbols) n)
  | _ =>
      throwUnsupported

private partial def collectSchemaEntries :
    List SchemaEntry →
      MacroM (List (Term × Term) × Term)
| [] => do
    let zero ← `(0)
    pure ([], zero)
| [.fallback n] =>
    pure ([], n)
| .fallback _ :: _ =>
    throwUnsupported
| .symbols Xs n :: entries => do
    let (rest, fallback) ← collectSchemaEntries entries
    pure (Xs.toList.map (fun X => (X, n)) ++ rest,
      fallback)

private partial def schemaArityBody
    (entries : List (Term × Term))
    (fallback : Term) :
    MacroM Term := do
  match entries with
  | [] =>
      pure fallback
  | (X, n) :: rest => do
      let tail ← schemaArityBody rest fallback
      `(if X.1 = $X then $n else $tail)

private def allAritiesMatchFallback
    (entries : List (Term × Term))
    (fallback : Term) : Bool :=
  entries.all (fun entry => entry.2.raw == fallback.raw)

macro "sch![" entries:dbt_schema_entry,* "]" : term => do
    let parsed ← entries.getElems.mapM schemaEntryData
    let (pairs, fallback) ←
      collectSchemaEntries parsed.toList
    let body ←
      if allAritiesMatchFallback pairs fallback then
        pure fallback
      else
        schemaArityBody pairs fallback
    let syms := (pairs.map Prod.fst).toArray
    if syms.isEmpty then
      `({ syms := ∅
          arity := fun X => $body })
    else
      `((let _hNoDup : [$[$syms],*].Nodup :=
            by decide
         { syms := List.toFinset [$[$syms],*]
           arity := fun X => $body }))

------------------------------------------------------------
-- Named Schema Literals
------------------------------------------------------------

declare_syntax_cat dbt_named_schema_entry
syntax term:max " [" term,* "]" : dbt_named_schema_entry

namespace NamedSchema

namespace Notation

variable {A α : Type}
variable [RelationNames A] [Attributes α]

/- Build a named schema from duplicate-free entry lists. -/
def fromList
    (entries : List (A × List α))
    (_hNoDup : (entries.map Prod.fst).Nodup)
    (_hAttrsNoDup :
      ∀ entry ∈ entries, entry.2.Nodup) :
    NamedSchema A α where
  syms := (entries.map Prod.fst).toFinset
  attrs := fun X =>
    match entries.find? (fun entry => entry.1 = X.1) with
    | some entry => entry.2.toFinset
    | none => ∅

end Notation

end NamedSchema

private def namedSchemaEntryPair
    (entry : TSyntax `dbt_named_schema_entry) :
    MacroM Term := do
  match entry with
  | `(dbt_named_schema_entry| $X:term [$[$attrs:term],*]) =>
      `(($X, [$[$attrs],*]))
  | _ =>
      throwUnsupported

syntax "namedSch![" dbt_named_schema_entry,* "]" : term

macro_rules
| `(namedSch![$[$entries:dbt_named_schema_entry],*]) => do
    let pairs ← entries.mapM namedSchemaEntryPair
    `(NamedSchema.Notation.fromList
      [$[$pairs],*]
      (by decide)
      (by decide))

------------------------------------------------------------
-- Signature Literals
------------------------------------------------------------

namespace Signature

namespace Notation

variable {A F : Type}
variable [RelationNames A] [FunctionNames F]

/- Build a duplicate-free signature. -/
def fromLists
    (relEntries : List (A × Nat))
    (funEntries : List (F × Nat))
    (hRelNoDup : (relEntries.map Prod.fst).Nodup)
    (_hFunNoDup : (funEntries.map Prod.fst).Nodup) :
    Signature A F where
  toUnnamedSchema :=
    UnnamedSchema.Notation.fromList relEntries hRelNoDup
  funs := (funEntries.map Prod.fst).toFinset
  funArity := fun f =>
    match funEntries.find? (fun entry => entry.1 = f.1) with
    | some entry => entry.2
    | none => 0

end Notation

end Signature

syntax
  "sig![" "rels:" dbt_arity_entry,*
    "funs:" dbt_arity_entry,* "]" :
  term

macro_rules
| `(sig![
      rels: $[$relEntries:dbt_arity_entry],*
      funs: $[$funEntries:dbt_arity_entry],*
    ]) => do
    let relPairs ← relEntries.mapM arityEntryPair
    let funPairs ← funEntries.mapM arityEntryPair
    `(Signature.Notation.fromLists
      [$[$relPairs],*]
      [$[$funPairs],*]
      (by decide)
      (by decide))

------------------------------------------------------------
-- Domain Notation Typeclasses
------------------------------------------------------------

namespace DBLib

namespace Notation

open Lean Macro

/-
  `Literal α β` lets notation treat a surface literal of type
  `α` as a value of the target type `β`.
-/
class Literal (α β : Type) where
  toTarget : α → β

/-
  Convert a surface literal through the target-specific
  hook.
-/
def literal
    {α β : Type}
    [Literal α β]
    (a : α) : β :=
  Literal.toTarget a

/-
  `PrettyLiteral α` renders values in the surface syntax
  accepted by notation when that is possible.
-/
class PrettyLiteral (α : Type) where
  pretty : α → String

/-
  Render a value through the notation-oriented pretty
  hook.
-/
def prettyLiteral
    {α : Type}
    [PrettyLiteral α]
    (a : α) : String :=
  PrettyLiteral.pretty a

/-
  Preserve the old `reprStr` behavior by default. Concrete
  domains can override this with an explicit instance.
-/
instance (priority := 100) prettyLiteralOfRepr
    {α : Type}
    [Repr α] :
    PrettyLiteral α where
  pretty := reprStr

private def boolLiteral? (t : Term) : Option Bool :=
  match t.raw with
  | .ident _ _ id _ =>
      if id == ``Bool.true ||
          id == Name.mkSimple "true" then
        some true
      else if id == ``Bool.false ||
          id == Name.mkSimple "false" then
        some false
      else
        none
  | _ =>
      none

/-
  Rewrite string, natural-number, and Boolean literal syntax
  through `DBLib.Notation.literal`. Non-literal terms are left
  unchanged.
-/
def expandLiteralTerm
    (t : Term) :
    MacroM Term := do
  match t with
  | `($s:str) =>
      `(DBLib.Notation.literal $s)
  | `($n:num) =>
      `(DBLib.Notation.literal $n)
  | _ =>
      match boolLiteral? t with
      | some true =>
          `(DBLib.Notation.literal true)
      | some false =>
          `(DBLib.Notation.literal false)
      | none =>
          pure t

end Notation

end DBLib
