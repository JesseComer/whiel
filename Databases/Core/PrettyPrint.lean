-- Author: Jesse Comer
import Databases.Core.NamedSchema
import Databases.Core.Notation
import Databases.Core.UnnamedSchema
import Databases.Core.Signature
import Databases.UnnamedModel.RelAtom
import Mathlib.Data.List.Lex
import Mathlib.Data.Multiset.Sort

/-
  Pretty-printers for shared database primitives.

  Key declarations include:
    * `DBTPretty.display`
    * `DBTPretty.varName`
    * `Var.pretty`
    * `Var.display`
    * `Finset.pretty`
    * `Finset.display`
    * `RelTerm.pretty`
    * `RelAtom.pretty`
    * `Tuple.prettyKey`
    * `Tuple.pretty`
    * `FinRelation.pretty`
    * `UnnamedSchema.pretty`
    * `NamedSchema.pretty`
    * `Signature.pretty`
-/

------------------------------------------------------------
-- Shared Pretty-Printing Helpers
------------------------------------------------------------

namespace DBTPretty

/- Wrapper for rendering strings directly in `#eval`. -/
structure Display where
  text : String

instance : Repr Display where
  reprPrec d _ := Std.Format.text d.text

/- Render a string directly in `#eval` output. -/
def display (s : String) : Display :=
  ⟨s⟩

/- Join strings with a separator. -/
def joinSep (sep : String) : List String → String
| [] => ""
| [x] => x
| x :: xs => x ++ sep ++ joinSep sep xs

/- Render variables as `x1`, `y1`, `z1`, and so on. -/
def varName (x : Var) : String :=
  let stem :=
    match x % 3 with
    | 0 => "x"
    | 1 => "y"
    | _ => "z"
  stem ++ toString (x / 3 + 1)

/- Render an already sorted finite display body. -/
def sortedBody (xs : List String) : String :=
  joinSep ", " xs

/- Render a finite set body with a custom printer. -/
def finsetBody
    {α : Type}
    (pretty : α → String)
    (S : Finset α) : String :=
  sortedBody ((S.val.map pretty).sort (· ≤ ·))

/- Render a finite set with a custom printer. -/
def finset
    {α : Type}
    (pretty : α → String)
    (S : Finset α) : String :=
  "{" ++ finsetBody pretty S ++ "}"

/- Render an optional value using the supplied printer. -/
def option
    {α : Type}
    (pretty : α → String) :
    Option α → String
| none => "none"
| some x => "some " ++ pretty x

end DBTPretty

namespace Var

/- Render a shared variable identifier. -/
def pretty (x : Var) : String :=
  DBTPretty.varName x

/- Render a shared variable directly in `#eval` output. -/
def display (x : Var) : DBTPretty.Display :=
  DBTPretty.display x.pretty

end Var

------------------------------------------------------------
-- Finite Set Pretty-Printing
------------------------------------------------------------

namespace Finset

variable {α : Type} [Repr α]

/- Render a finite set using `reprStr` for elements. -/
def pretty (S : Finset α) : String :=
  DBTPretty.finset reprStr S

/- Render a finite set directly in `#eval` output. -/
def display (S : Finset α) : DBTPretty.Display :=
  DBTPretty.display S.pretty

end Finset

------------------------------------------------------------
-- Relational Syntax Pretty-Printing
------------------------------------------------------------

namespace RelTerm

variable {D : Type} [Domain D]
variable [DBLib.Notation.PrettyLiteral D]

/- Render a function-free relational term. -/
def pretty : RelTerm D → String
| .var x => DBTPretty.varName x
| .const d => DBLib.Notation.prettyLiteral d

/- Render a relational term list. -/
def prettyList (ts : List (RelTerm D)) : String :=
  DBTPretty.joinSep ", " (ts.map pretty)

/- Render a relational term directly in `#eval`. -/
def display (t : RelTerm D) : DBTPretty.Display :=
  DBTPretty.display t.pretty

end RelTerm

namespace RelAtom

variable {A D : Type} [RelationNames A] [Domain D]
variable [DBLib.Notation.PrettyLiteral D]
variable {Γ : UnnamedSchema A}

/- Render a relational atom. -/
def pretty (a : RelAtom D Γ) : String :=
  reprStr a.rel.1 ++ "(" ++
    RelTerm.prettyList a.args.toList ++ ")"

/- Render a relational atom directly in `#eval`. -/
def display (a : RelAtom D Γ) : DBTPretty.Display :=
  DBTPretty.display a.pretty

end RelAtom

------------------------------------------------------------
-- Tuple Pretty-Printing
------------------------------------------------------------

namespace Tuple

variable {D : Type} [DBLib.Notation.PrettyLiteral D]

/- Key used for tuple display and lexicographic sorting. -/
def prettyKey {n : Nat} (t : Tuple D n) : List String :=
  t.toList.map DBLib.Notation.prettyLiteral

/- Render an already computed tuple display key. -/
def prettyFromKey (key : List String) : String :=
  "(" ++ DBTPretty.joinSep ", " key ++ ")"

/- Render a tuple as `(d₁, ..., dₙ)`. -/
def pretty {n : Nat} (t : Tuple D n) : String :=
  prettyFromKey t.prettyKey

/- Render a tuple directly in `#eval` output. -/
def display {n : Nat} (t : Tuple D n) :
    DBTPretty.Display :=
  DBTPretty.display t.pretty

end Tuple

------------------------------------------------------------
-- Finite Relation Pretty-Printing
------------------------------------------------------------

namespace FinRelation

variable {D : Type} [DBLib.Notation.PrettyLiteral D]

/- Sorted tuple display keys for a finite relation. -/
def prettyKeys {n : Nat} (R : FinRelation D n) :
    List (List String) :=
  (R.val.map (fun t => Tuple.prettyKey t)).sort (· ≤ ·)

/- Render a finite relation as a set of tuples. -/
def pretty {n : Nat} (R : FinRelation D n) : String :=
  "{" ++
    DBTPretty.sortedBody
      ((prettyKeys R).map Tuple.prettyFromKey) ++
    "}"

/- Render the arity of a finite relation. -/
def prettyArity {n : Nat} (_R : FinRelation D n) : String :=
  "arity: " ++ toString n

/- Render the cardinality of a finite relation. -/
def prettyCardinality {n : Nat}
    (R : FinRelation D n) : String :=
  "cardinality: " ++ toString R.card

/- Render a finite relation directly in `#eval` output. -/
def display {n : Nat} (R : FinRelation D n) :
    DBTPretty.Display :=
  DBTPretty.display R.pretty

/- Render a relation arity directly in `#eval` output. -/
def displayArity {n : Nat} (R : FinRelation D n) :
    DBTPretty.Display :=
  DBTPretty.display R.prettyArity

/- Render a relation cardinality directly in `#eval`. -/
def displayCardinality {n : Nat} (R : FinRelation D n) :
    DBTPretty.Display :=
  DBTPretty.display R.prettyCardinality

end FinRelation

------------------------------------------------------------
-- Schema Pretty-Printing
------------------------------------------------------------

namespace UnnamedSchema

variable {A : Type} [RelationNames A]

/- Render one relation symbol with its arity. -/
def prettySym (Γ : UnnamedSchema A) (X : Γ.syms) :
    String :=
  spellName X.1 ++ " (arity: " ++
    toString (Γ.arity X) ++ ")"

/- Render an unnamed schema as `{R (arity: n), ...}`. -/
def pretty (Γ : UnnamedSchema A) : String :=
  DBTPretty.finset (prettySym Γ) Γ.syms.attach

/- Render an unnamed schema directly in `#eval` output. -/
def display (Γ : UnnamedSchema A) : DBTPretty.Display :=
  DBTPretty.display Γ.pretty

/- Render a partial arity lookup. -/
def prettyArity? (Γ : UnnamedSchema A) (X : A) : String :=
  DBTPretty.option toString (Γ.arity? X)

/- Render a partial arity lookup directly in `#eval`. -/
def displayArity? (Γ : UnnamedSchema A) (X : A) :
    DBTPretty.Display :=
  DBTPretty.display (Γ.prettyArity? X)

end UnnamedSchema

namespace NamedSchema

variable {A α : Type}
variable [RelationNames A] [Attributes α]

/- Render one relation symbol with its attribute set. -/
def prettySym (Γ : NamedSchema A α) (X : Γ.syms) :
    String :=
  reprStr X.1 ++ "[" ++
    DBTPretty.finsetBody reprStr (Γ.attrs X) ++
    "]"

/- Render a named schema as `{R[a, b], ...}`. -/
def pretty (Γ : NamedSchema A α) : String :=
  DBTPretty.finset (prettySym Γ) Γ.syms.attach

/- Render a named schema directly in `#eval` output. -/
def display (Γ : NamedSchema A α) : DBTPretty.Display :=
  DBTPretty.display Γ.pretty

/- Render a partial attribute lookup. -/
def prettyAttrs? (Γ : NamedSchema A α) (X : A) :
    String :=
  DBTPretty.option
    (fun S =>
      DBTPretty.finset reprStr S)
    (Γ.attrs? X)

/- Render a partial attribute lookup directly in `#eval`. -/
def displayAttrs? (Γ : NamedSchema A α) (X : A) :
    DBTPretty.Display :=
  DBTPretty.display (Γ.prettyAttrs? X)

end NamedSchema

namespace Signature

variable {A F : Type}
variable [RelationNames A] [FunctionNames F]

/- Render one function symbol with its arity. -/
def prettyFun (Λ : Signature A F) (f : Λ.funs) :
    String :=
  reprStr f.1 ++ " (arity: " ++
    toString (Λ.funArity f) ++ ")"

/- Render a first-order signature. -/
def pretty (Λ : Signature A F) : String :=
  "rels " ++ Λ.toUnnamedSchema.pretty ++
    "; funs " ++
    DBTPretty.finset (prettyFun Λ) Λ.funs.attach

/- Render a signature directly in `#eval` output. -/
def display (Λ : Signature A F) : DBTPretty.Display :=
  DBTPretty.display Λ.pretty

/- Render a partial function-arity lookup. -/
def prettyFunArity? (Λ : Signature A F) (f : F) :
    String :=
  DBTPretty.option toString (Λ.funArity? f)

/- Render a partial function lookup directly in `#eval`. -/
def displayFunArity? (Λ : Signature A F) (f : F) :
    DBTPretty.Display :=
  DBTPretty.display (Λ.prettyFunArity? f)

end Signature
