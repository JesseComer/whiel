-- Author: Jesse Comer
import Databases.UnnamedModel.RelAtom
import Mathlib.Data.Vector.Basic

/-
  This file specifies the syntax of Datalog.

  Key declarations are:
    * `Atom`
    * `Body`
    * `Rule`
    * `Program`
    * `Program.adom`
    * `Query`

  Datalog uses the shared `RelTerm` and `RelAtom`
  declarations from `DBLib.UnnamedModel.RelAtom`.

  IDBs are inferred from the syntax of the program.
  Key helper declarations related to the schema include:
    * `Program.idb`
    * `Program.edb`
    * `Program.idbNames`
    * `Program.edbNames`
    * `Program.edbSchema`
    * `Program.ambient_extension_edbSchema`

  Other declarations here are bookkeeping for finite sets,
  program-schema views, arity casts, and computable support.
-/

------------------------------------------------------------
-- Datalog Atoms
------------------------------------------------------------

namespace Datalog

/- Datalog atoms are relational atoms or equality atoms. -/
inductive Atom
    (D : Type) [Domain D]
    {A : Type} [RelationNames A]
    (Γ : UnnamedSchema A) where
| rel : RelAtom D Γ → Atom D Γ
| eq : RelTerm D → RelTerm D → Atom D Γ
deriving DecidableEq, Repr

namespace Atom

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Variables in an atom, with duplicates and in
  argument order.
-/
def varList : Atom D Γ → List Var
| .rel a => a.varList
| .eq lhs rhs => [lhs, rhs].filterMap RelTerm.var?

/-
  Variables appearing in relational atoms only.
-/
def relVarList : Atom D Γ → List Var
| .rel a => a.varList
| .eq _ _ => []

/-
  Constants in an atom, with duplicates and in
  argument order.
-/
private def constList : Atom D Γ → List D
| .rel a => a.constList
| .eq lhs rhs => [lhs, rhs].filterMap RelTerm.const?

/- Variables in a list of atoms, with duplicates. -/
def listVarList (body : List (Atom D Γ)) : List Var :=
  (body.map varList).flatten

/- Variables in relational atoms in a list of atoms. -/
def listRelVarList (body : List (Atom D Γ)) : List Var :=
  (body.map relVarList).flatten

/- Variables occurring in a list of atoms. -/
def vars (body : List (Atom D Γ)) : Finset Var :=
  listVarList body |>.toFinset

/- Variables occurring in relational atoms in a list of atoms. -/
def relVars (body : List (Atom D Γ)) : Finset Var :=
  listRelVarList body |>.toFinset

/- Variables occurring in a list of atoms. -/
def listVars (body : List (Atom D Γ)) : Finset Var :=
  vars body

/- Variables occurring in relational atoms in a list of atoms. -/
def listRelVars (body : List (Atom D Γ)) : Finset Var :=
  relVars body

/- Constants in a list of atoms, with duplicates. -/
private def listConstList (body : List (Atom D Γ)) : List D :=
  (body.map constList).flatten

end Atom

------------------------------------------------------------
-- Datalog Rule Bodies
------------------------------------------------------------

/-
  A Datalog body is a list of atoms.
-/
abbrev Body
    (D : Type) [Domain D]
    {A : Type} [RelationNames A]
    (Γ : UnnamedSchema A) :=
  List (Atom D Γ)

namespace Body

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Variables in a rule body, with duplicates and in body
  order.
-/
def varList (body : Body D Γ) : List Var :=
  Atom.listVarList body

/-
  Variables occurring in relational atoms.
-/
def relVarList (body : Body D Γ) : List Var :=
  Atom.listRelVarList body

/- Variables occurring in a rule body. -/
def vars (body : Body D Γ) : Finset Var :=
  Atom.vars body

/- Variables occurring in relational atoms. -/
def relVars (body : Body D Γ) : Finset Var :=
  Atom.relVars body

/-
  Constants in a rule body, with duplicates and in body
  order.
-/
private def constList (body : Body D Γ) : List D :=
  Atom.listConstList body

/-
  `body.HasRelVar x` means `x` occurs in a relational
  atom.
-/
def HasRelVar (body : Body D Γ) (x : Var) : Prop :=
  x ∈ relVars body

instance
    (body : Body D Γ)
    (x : Var) :
    Decidable (HasRelVar body x) := by
  unfold HasRelVar
  infer_instance

end Body

------------------------------------------------------------
-- Datalog Rules
------------------------------------------------------------

/-
  A Datalog rule. Rule heads are constant-free relational
  atoms, and safety requires that all variables in either
  the head or the body must occur in some relational atom.
-/
structure Rule
    (D : Type) [Domain D]
    {A : Type} [RelationNames A]
    (Γ : UnnamedSchema A) where
  head : RelAtom D Γ
  body : Body D Γ
  noHeadConst : RelAtom.ConstFree head
  safe : ∀ x : Var,
    x ∈ head.vars ∪ Body.vars body →
      x ∈ Body.relVars body

namespace Rule

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Variables in a rule, deduplicated in first-occurrence
  order.
-/
def varList (r : Rule D Γ) : List Var :=
  (r.head.varList ++ Body.varList r.body).dedup

/-
  Constants occurring in a rule, with duplicates and in
  body order.
-/
private def constList (r : Rule D Γ) : List D :=
  Body.constList r.body

/- Head variables occur in the rule variable list. -/
theorem head_var_mem_varList
    (r : Rule D Γ)
    {x : Var}
    (hx : x ∈ r.head.varList) :
    x ∈ r.varList := by
  unfold varList
  exact List.mem_dedup.mpr
    (List.mem_append.mpr (Or.inl hx))

/- Body variables occur in the rule variable list. -/
private theorem body_var_mem_varList
    (r : Rule D Γ)
    {x : Var}
    (hx : x ∈ Body.varList r.body) :
    x ∈ r.varList := by
  unfold varList
  exact List.mem_dedup.mpr
    (List.mem_append.mpr (Or.inr hx))

/-
  Variables in an atom occur in the rule variable
  list.
-/
theorem atom_in_body_var_mem_varList
    (r : Rule D Γ)
    {b : Atom D Γ}
    (hb : b ∈ r.body)
    {x : Var}
    (hx : x ∈ b.varList) :
    x ∈ r.varList := by
  apply r.body_var_mem_varList
  unfold Body.varList Atom.listVarList
  rw [List.mem_flatten]
  refine ⟨b.varList, ?_, hx⟩
  exact List.mem_map.mpr ⟨b, hb, rfl⟩

end Rule

end Datalog

------------------------------------------------------------
-- Datalog Programs
------------------------------------------------------------

namespace Datalog

/- A Datalog program is a finite list of rules. -/
structure Program
    (D : Type) [Domain D]
    {A : Type} [RelationNames A]
    (Γ : UnnamedSchema A) where
  rules : List (Rule D Γ)

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Head symbols, with duplicates and in rule order. -/
def headSymbolList (P : Program D Γ) : List Γ.syms :=
  P.rules.map (fun r => r.head.rel)

/-
  Constants occurring in a program, with duplicates and in
  rule order.
-/
private def constList (P : Program D Γ) : List D :=
  (P.rules.map Rule.constList).flatten

/- Constants occurring in a program. -/
def constants (P : Program D Γ) : Finset D :=
  P.constList.toFinset

/-
  The active domain of an input instance, plus program
  constants.
-/
def adom
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (I : Instance D Δ) :
    Finset D :=
  I.Adom ∪ P.constants

/- IDB symbols are exactly the head symbols. -/
def idb (P : Program D Γ) : Finset Γ.syms :=
  P.headSymbolList.toFinset

/- IDB symbols as a subtype. -/
abbrev IDBSym (P : Program D Γ) : Type :=
  {X : Γ.syms // X ∈ P.idb}

/- IDB symbols in first-head-occurrence order. -/
def idbList (P : Program D Γ) : List Γ.syms :=
  P.headSymbolList.eraseDups

/- Membership in `idbList` gives membership in `P.idb`. -/
theorem idbList_mem_idb
    (P : Program D Γ)
    {X : Γ.syms}
    (hX : X ∈ P.idbList) :
    X ∈ P.idb := by
  simpa [idbList, idb] using hX

/- IDB symbols as typed witnesses. -/
def idbSymList (P : Program D Γ) : List (P.IDBSym) :=
  P.idbList.attach.map
    (fun X => ⟨X.1, P.idbList_mem_idb X.2⟩)

/- EDB symbols are schema symbols which are not IDBs. -/
def edb (P : Program D Γ) : Finset Γ.syms :=
  Γ.syms.attach.filter (fun X => X ∉ P.idb)

/- Forget schema-symbol proofs in a finite symbol set. -/
def symbolNames (S : Finset Γ.syms) : Finset A :=
  S.image Subtype.val

/- Raw IDB relation names. -/
def idbNames (P : Program D Γ) : Finset A :=
  symbolNames P.idb

/- Raw EDB relation names. -/
def edbNames (P : Program D Γ) : Finset A :=
  symbolNames P.edb

/- A non-IDB schema name is an EDB name. -/
theorem edbName_of_schema_not_idbName
    (P : Program D Γ)
    {x : A}
    (hx : x ∈ Γ.syms)
    (hNotIdb : x ∉ P.idbNames) :
    x ∈ P.edbNames := by
  have hNotSym : (⟨x, hx⟩ : Γ.syms) ∉ P.idb := by
    intro hSym
    exact hNotIdb
      (Finset.mem_image.mpr ⟨⟨x, hx⟩, hSym, rfl⟩)
  unfold edbNames symbolNames edb
  exact
    Finset.mem_image.mpr
      ⟨⟨x, hx⟩, by simp [hNotSym], rfl⟩

/- Raw program relation names are program-schema names. -/
def symbolNamesOf (_ : Program D Γ) : Finset A :=
  Γ.syms

/- Symbol-name erasure stays inside the program schema. -/
private theorem symbolNames_subset_schema
    (S : Finset Γ.syms) :
    symbolNames S ⊆ Γ.syms := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨s, _hs, rfl⟩
  exact s.2

/- Every EDB symbol is in the program schema. -/
private theorem edb_subset_schema
    (P : Program D Γ) :
    P.edbNames ⊆ Γ.syms :=
  symbolNames_subset_schema P.edb

/-
  A rule head symbol is an IDB symbol of a program
  containing the rule.
-/
theorem head_mem_idb
    (P : Program D Γ)
    {r : Rule D Γ}
    (hr : r ∈ P.rules) :
    r.head.rel ∈ P.idb := by
  have hList : r.head.rel ∈ P.headSymbolList := by
    unfold headSymbolList
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  simpa [idb] using hList

/- A rule head name is in the raw program schema. -/
theorem head_mem_symbolNames
    (P : Program D Γ)
    {r : Rule D Γ}
    (_hr : r ∈ P.rules) :
    r.head.rel.1 ∈ P.symbolNamesOf :=
  r.head.rel.2

/-
  A relational atom name from a rule body is in the raw program
  schema.
-/
theorem body_rel_atom_mem_symbolNames
    (P : Program D Γ)
    {r : Rule D Γ}
    (_hr : r ∈ P.rules)
    {a : RelAtom D Γ}
    (_ha : Atom.rel a ∈ r.body) :
    a.rel.1 ∈ P.symbolNamesOf := by
  exact a.rel.2

/- EDB and IDB symbols are disjoint. -/
theorem disjoint_edb_idb
    (P : Program D Γ) :
    Disjoint P.edbNames P.idbNames := by
  rw [Finset.disjoint_left]
  intro x hxE hxI
  rcases Finset.mem_image.mp hxE with ⟨e, he, heq⟩
  rcases Finset.mem_image.mp hxI with ⟨i, hi, hiq⟩
  have hSub : e = i :=
    Subtype.ext (heq.trans hiq.symm)
  subst hSub
  exact (Finset.mem_filter.mp he).2 hi

/- The schema restricted to `edb(P)`. -/
def edbSchema (P : Program D Γ) : UnnamedSchema A :=
  Γ.restrict P.edbNames P.edb_subset_schema

/-
  The schema restricted to the symbols of program `P`.
-/
def progSchema (_ : Program D Γ) : UnnamedSchema A :=
  Γ

/- The program schema extends `edb(P)`. -/
private theorem progSchema_extension_edbSchema
    (P : Program D Γ) :
    P.progSchema.extensionOf P.edbSchema := by
  exact
    UnnamedSchema.extensionOf_restrict
      Γ P.edbNames P.edb_subset_schema

/- The program schema extends `edb(P)`. -/
theorem ambient_extension_edbSchema
    (P : Program D Γ) :
    Γ.extensionOf P.edbSchema :=
  P.progSchema_extension_edbSchema

/-
  The arity of a program-schema symbol agrees with the
  underlying schema symbol.
-/
theorem prog_arity_eq
    (P : Program D Γ)
    (X : Γ.syms)
    (hX : X.1 ∈ P.symbolNamesOf) :
    P.progSchema.arity ⟨X.1, hX⟩ = Γ.arity X := by
  rfl

/-
  View a tuple over the underlying schema as a tuple over the
  program schema.
-/
def tupleToProg
    (P : Program D Γ)
    (X : Γ.syms)
    (hX : X.1 ∈ P.symbolNamesOf)
    (t : Tuple D (Γ.arity X)) :
    Tuple D (P.progSchema.arity ⟨X.1, hX⟩) :=
  cast
    (congrArg (Tuple D) (P.prog_arity_eq X hX).symm)
    t

/- View a rule head symbol inside the program schema. -/
def headSym
    (P : Program D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules}) :
    P.progSchema.syms :=
  r.1.head.rel

end Program

end Datalog

------------------------------------------------------------
-- Datalog Queries
------------------------------------------------------------

namespace Datalog

/-
  A Datalog query designates one IDB output symbol of a
  program.
-/
structure Query
    (D : Type) [Domain D]
    {A : Type} [RelationNames A]
    (Γ : UnnamedSchema A)
    (n : Nat) where
  program : Program D Γ
  output : program.idb
  arity : Γ.arity output.val = n

namespace Query

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {n : Nat}

/- The output symbol viewed inside the program schema. -/
def outputSym (q : Query D Γ n) :
    q.program.progSchema.syms :=
  q.output.val

/- Output arity of a query. -/
abbrev outputArity
    (_ : Query D Γ n) : Nat :=
  n

end Query

end Datalog
