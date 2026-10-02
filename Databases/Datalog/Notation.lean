-- Author: Jesse Comer
import Databases.Core.Notation
import Databases.Datalog.PrettyPrint

/-
  Typed notation for Datalog examples.

  Key declarations: `datalog![...]` and
  `dlQuery![...]`.
-/

------------------------------------------------------------
-- Surface Notation
------------------------------------------------------------

declare_syntax_cat dbt_dterm
declare_syntax_cat dbt_dvar
declare_syntax_cat dbt_datom
declare_syntax_cat dbt_drule_atom
declare_syntax_cat dbt_dhead
declare_syntax_cat dbt_drule
declare_syntax_cat dbt_dprog_rule

syntax ident : dbt_dvar
syntax term:80 : dbt_dterm
syntax term:80 "(" dbt_dterm,* ")" : dbt_datom
syntax dbt_datom : dbt_drule_atom
syntax dbt_dterm " = " dbt_dterm : dbt_drule_atom
syntax term:80 "(" dbt_dvar,* ")" : dbt_dhead
syntax dbt_dhead " :- " dbt_drule_atom,* : dbt_drule
syntax dbt_drule ";" : dbt_dprog_rule

syntax "datalog![" dbt_dprog_rule* "]" : term
syntax
  "dlQuery![" "{" "Program" ":" term "}"
    "{" "Return" ":" term "}" "]" :
  term

namespace Datalog

namespace Notation

open Lean Macro

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Build an atom from a checked raw name. -/
def atom
    (R : A)
    (h : R ∈ Γ.syms := by decide)
    (args :
      Vector (RelTerm D) (Γ.arity (Γ.sym R h))) :
    RelAtom D Γ where
  rel := Γ.sym R h
  args := args

/- Build a rule head atom from a checked raw name. -/
def head
    (R : A)
    (h : R ∈ Γ.syms := by decide)
    (args : Vector Var (Γ.arity (Γ.sym R h))) :
    RelAtom D Γ where
  rel := Γ.sym R h
  args := args.map RelTerm.var

/- Heads built from variables are constant-free. -/
theorem head_constFree
    (R : A)
    (h : R ∈ Γ.syms := by decide)
    (args : Vector Var (Γ.arity (Γ.sym R h))) :
    (head (D := D) (Γ := Γ) R (h := h) args).ConstFree := by
  intro i
  simp [head, RelTerm.ConstFree, Vector.get]

/- Build a query from a program and raw output name. -/
def query
    {n : Nat}
    (P : Datalog.Program D Γ)
    (R : A)
    (h : R ∈ Γ.syms := by decide)
    (hIdb : Γ.sym R h ∈ P.idb := by decide)
    (hAr : Γ.arity (Γ.sym R h) = n := by decide) :
    Datalog.Query D Γ n where
  program := P
  output := (⟨Γ.sym R h, hIdb⟩ : P.idb)
  arity := hAr

private def parseVarString (s : String) : Option Nat := do
  let cs := s.toList
  let (offset, digits) ←
    match cs with
    | 'x' :: rest => some (0, rest)
    | 'y' :: rest => some (1, rest)
    | 'z' :: rest => some (2, rest)
    | _ => none
  let digitsString := String.ofList digits
  let k ← digitsString.toNat?
  if k = 0 then
    none
  else if digitsString = toString k then
    some (3 * (k - 1) + offset)
  else
    none

private def natTerm (n : Nat) : Lean.Term :=
  ⟨Syntax.mkNumLit (toString n)⟩

private def varOfIdent? (id : Ident) : Option Nat :=
  parseVarString (toString id.getId.eraseMacroScopes)

private def varOfTerm? (t : Lean.Term) : Option Nat :=
  if t.raw.isIdent then
    let id : Ident := ⟨t.raw⟩
    varOfIdent? id
  else
    none

private def mkVar
    (v : TSyntax `dbt_dvar) :
    MacroM Lean.Term := do
  match v with
  | `(dbt_dvar| $id:ident) =>
      match varOfIdent? id with
      | some x => pure (natTerm x)
      | none =>
          Macro.throwErrorAt id.raw
            "expected one of x1, y1, z1, x2, ..."
  | _ =>
      throwUnsupported

private partial def preferDChoice (stx : Syntax) :
    Syntax :=
  match stx with
  | .node _ `choice choices =>
      match choices.back? with
      | some stx' => preferDChoice stx'
      | none => stx
  | _ => stx

private def termOfDTerm?
    (t : TSyntax `dbt_dterm) :
    Option Lean.Term :=
  match preferDChoice t.raw with
  | .node _ `dbt_dterm_ args =>
      match args[0]? with
      | some t => some ⟨t⟩
      | none => none
  | _ => none

private def expandDTerm
    (t : TSyntax `dbt_dterm) :
    MacroM Lean.Term := do
  match termOfDTerm? t with
  | some term =>
      match varOfTerm? term with
      | some x =>
          let xTerm := natTerm x
          `(RelTerm.var $xTerm)
      | none => do
          let term' ← DBLib.Notation.expandLiteralTerm term
          `(RelTerm.const $term')
  | none =>
      throwUnsupported

private def isAtom (stx : Syntax) (s : String) : Bool :=
  match stx with
  | .atom _ a => a == s
  | _ => false

private def sepElems (stx : Syntax) : Array Syntax :=
  match stx with
  | .node _ _ args =>
      args.filter (fun a => !isAtom a ",")
  | _ => #[]

private def expandDAtom
    (a : TSyntax `dbt_datom) :
    MacroM Lean.Term := do
  match a.raw with
  | .node _ `«dbt_datom_(_)» args =>
      match args[0]?, args[2]? with
      | some R, some tsRaw => do
          let R : Lean.Term := ⟨R⟩
          let ts := (sepElems tsRaw).map
            (fun t => (⟨t⟩ : TSyntax `dbt_dterm))
          let ts' ← ts.mapM expandDTerm
          `(Datalog.Notation.atom $R
            (h := by decide)
            (Vector.mk #[
              $ts',*] (by decide)))
      | _, _ => throwUnsupported
  | _ =>
      throwUnsupported

private def expandDAtomInBody
    (b : TSyntax `dbt_drule_atom) :
    MacroM Lean.Term := do
  match b with
  | `(dbt_drule_atom| $a:dbt_datom) => do
      let a' ← expandDAtom a
      `(Datalog.Atom.rel $a')
  | `(dbt_drule_atom| $lhs:dbt_dterm = $rhs:dbt_dterm) => do
      let lhs' ← expandDTerm lhs
      let rhs' ← expandDTerm rhs
      `(Datalog.Atom.eq $lhs' $rhs')
  | _ =>
      throwUnsupported

private def expandDHead
    (h : TSyntax `dbt_dhead) :
    MacroM Lean.Term := do
  match h.raw with
  | .node _ `«dbt_dhead_(_)» args =>
      match args[0]?, args[2]? with
      | some R, some xsRaw => do
          let R : Lean.Term := ⟨R⟩
          let xs := (sepElems xsRaw).map
            (fun x => (⟨x⟩ : TSyntax `dbt_dvar))
          let xs' ← xs.mapM mkVar
          let headTerm ← `(Datalog.Notation.head $R
            (h := by decide)
            (Vector.mk #[
              $xs',*] (by decide)))
          pure headTerm
      | _, _ => throwUnsupported
  | _ =>
      throwUnsupported

private def expandDRule
    (r : TSyntax `dbt_drule) :
    MacroM Lean.Term := do
  match r.raw with
  | .node _ `«dbt_drule_:-_» args =>
      match args[0]?, args[2]? with
      | some h, some bodyRaw => do
          let h' ← expandDHead ⟨h⟩
          let hSyntax : TSyntax `dbt_dhead := ⟨h⟩
          let hConstFree ←
            match hSyntax.raw with
            | .node _ `«dbt_dhead_(_)» hArgs =>
                match hArgs[0]?, hArgs[2]? with
                | some R, some xsRaw => do
                    let R : Lean.Term := ⟨R⟩
                    let xs := (sepElems xsRaw).map
                      (fun x => (⟨x⟩ : TSyntax `dbt_dvar))
                    let xs' ← xs.mapM mkVar
                    `(Datalog.Notation.head_constFree $R
                      (h := by decide)
                      (Vector.mk #[
                        $xs',*] (by decide)))
                | _, _ => throwUnsupported
            | _ => throwUnsupported
          let body := (sepElems bodyRaw).map
            (fun b => (⟨b⟩ : TSyntax `dbt_drule_atom))
          let body' ← body.mapM expandDAtomInBody
          let hSafe ← `(by
            intro x hx
            simp [Datalog.Body.HasRelVar, Datalog.Body.relVars,
              Datalog.Body.vars, Datalog.Body.relVarList,
              Datalog.Body.varList, Datalog.Atom.relVarList,
              Datalog.Atom.varList, Datalog.Atom.vars,
              Datalog.Atom.relVars, Datalog.Atom.listVars,
              Datalog.Atom.listRelVars, Datalog.Atom.listVarList,
              Datalog.Atom.listRelVarList,
              RelAtom.vars, RelAtom.varList,
              RelTerm.tupleVars, RelTerm.tupleVarList,
              RelTerm.listVars, RelTerm.listVarList, RelTerm.vars,
              RelTerm.varList, RelTerm.var?, Datalog.Notation.head,
              Datalog.Notation.atom] at hx ⊢
            try tauto)
          `(({ head := $h'
               body := [$body',*]
               noHeadConst := $hConstFree
               safe := $hSafe } :
              Datalog.Rule _ _))
      | _, _ => throwUnsupported
  | _ =>
      throwUnsupported

private def expandDProgramRule
    (r : TSyntax `dbt_dprog_rule) :
    MacroM Lean.Term := do
  match r.raw with
  | .node _ `«dbt_dprog_rule_;» args =>
      match args[0]? with
      | some r => expandDRule ⟨r⟩
      | none => throwUnsupported
  | _ =>
      throwUnsupported

macro "datalog![" rs:dbt_dprog_rule* "]" : term => do
  let rs' ← rs.mapM expandDProgramRule
  `(({ rules := [$rs',*] } :
      Datalog.Program _ _))

macro
  "dlQuery![" "{" "Program" ":" P:term "}"
    "{" "Return" ":" R:term "}" "]" : term =>
  `(Datalog.Notation.query $P $R
    (h := by decide) (hIdb := by decide) (hAr := by decide))

end Notation

end Datalog
