-- Author: Jesse Comer
import Databases.Core.Notation
import Databases.RelCalc.PrettyPrint

/-
  Typed notation for relational calculus examples.

  Key declarations: `relcalc![...]` and
  `relcalcQuery![...]`.
-/

namespace RelCalc

namespace Notation

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Build a relation atom from a checked raw name. -/
def rel
    (X : A)
    (h : X ∈ Γ.syms := by decide)
    (ts : Vector (RelTerm D) (Γ.arity (Γ.sym X h))) :
    Formula D Γ :=
  .rel
    { rel := Γ.sym X h
      args := ts }

/- Build a query from explicit output variables. -/
def query
    (vars : List Var)
    (φ : Formula D Γ)
    (hFree : φ.freeVars = vars.toFinset) :
    Query D Γ vars.length where
  vars := Vector.mk vars.toArray (by simp)
  form := φ
  freeVars_eq := by
    simpa using hFree

end Notation

end RelCalc

------------------------------------------------------------
-- Surface Notation
------------------------------------------------------------

declare_syntax_cat dbt_rc_term
declare_syntax_cat dbt_rc_var

syntax ident : dbt_rc_var
syntax term:80 : dbt_rc_term

open Lean Macro

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

private def natTerm (n : Nat) : Term :=
  ⟨Syntax.mkNumLit (toString n)⟩

private def varOfIdent? (id : Ident) : Option Nat :=
  parseVarString (toString id.getId.eraseMacroScopes)

private def varOfTerm? (t : Term) : Option Nat :=
  if t.raw.isIdent then
    let id : Ident := ⟨t.raw⟩
    varOfIdent? id
  else
    none

private def rcVarTerm
    (v : TSyntax `dbt_rc_var) :
    MacroM Term := do
  match v with
  | `(dbt_rc_var| $id:ident) =>
      match varOfIdent? id with
      | some x => pure (natTerm x)
      | none =>
          Macro.throwErrorAt id.raw
            "expected one of x1, y1, z1, x2, ..."
  | _ =>
      throwUnsupported

private def termOfRCTerm?
    (t : TSyntax `dbt_rc_term) :
    Option Term :=
  match t.raw with
  | .node _ `dbt_rc_term_ args =>
      match args[0]? with
      | some raw => some ⟨raw⟩
      | none => none
  | _ => none

private def rcTermTerm
    (t : TSyntax `dbt_rc_term) :
    MacroM Term := do
  let some t := termOfRCTerm? t
    | throwUnsupported
  match varOfTerm? t with
  | some x =>
      let xTerm := natTerm x
      `(RelTerm.var $xTerm)
  | none => do
      let t' ← DBLib.Notation.expandLiteralTerm t
      `(RelTerm.const $t')

declare_syntax_cat dbt_rc

syntax "⊤" : dbt_rc
syntax "⊥" : dbt_rc
syntax dbt_rc_term " = " dbt_rc_term : dbt_rc
syntax term:80 "(" dbt_rc_term,* ")" : dbt_rc
syntax dbt_rc:66 " ∧ " dbt_rc:67 : dbt_rc
syntax dbt_rc:61 " ∨ " dbt_rc:62 : dbt_rc
syntax "¬" dbt_rc:70 : dbt_rc
syntax dbt_rc:55 " → " dbt_rc:56 : dbt_rc
syntax dbt_rc:50 " ↔ " dbt_rc:51 : dbt_rc
syntax "∀ " dbt_rc_var ". " dbt_rc : dbt_rc
syntax "∃ " dbt_rc_var ". " dbt_rc : dbt_rc
syntax "(" dbt_rc ")" : dbt_rc

syntax "relcalc![" dbt_rc "]" : term

private partial def preferRCChoice (stx : Syntax) :
    Syntax :=
  match stx with
  | .node _ `choice choices =>
      match choices.back? with
      | some stx' => preferRCChoice stx'
      | none => stx
  | _ => stx

private def commaRCTerms (stx : Syntax) :
    Array (TSyntax `dbt_rc_term) :=
  stx.getArgs.filterMap fun arg =>
    match arg with
    | .atom _ "," => none
    | other => some ⟨other⟩

private partial def expandRC
    (φ : TSyntax `dbt_rc) :
    MacroM Term := do
  let raw := preferRCChoice φ.raw
  match raw with
  | .node _ `«dbt_rc⊤» _ =>
      `(RelCalc.Formula.top)
  | .node _ `«dbt_rc⊥» _ =>
      `(RelCalc.Formula.bot)
  | .node _ `«dbt_rc_=_» args =>
      match args[0]?, args[2]? with
      | some t₁, some t₂ => do
          let t₁Stx : TSyntax `dbt_rc_term := ⟨t₁⟩
          let t₂Stx : TSyntax `dbt_rc_term := ⟨t₂⟩
          let t₁' ← rcTermTerm t₁Stx
          let t₂' ← rcTermTerm t₂Stx
          `(RelCalc.Formula.eq
            $t₁' $t₂')
      | _, _ => throwUnsupported
  | .node _ `«dbt_rc_(_)» args =>
      match args[0]?, args[2]? with
      | some X, some tsRaw => do
          let XTerm : Term := ⟨X⟩
          let ts := commaRCTerms tsRaw
          let ts' ← ts.mapM rcTermTerm
          `(RelCalc.Notation.rel $XTerm
            (h := by decide)
            (Vector.mk #[ $ts',* ] (by decide)))
      | _, _ => throwUnsupported
  | .node _ `«dbt_rc_∧_» args =>
      match args[0]?, args[2]? with
      | some φ, some ψ => do
          let φ' ← expandRC ⟨φ⟩
          let ψ' ← expandRC ⟨ψ⟩
          `(RelCalc.Formula.and $φ' $ψ')
      | _, _ => throwUnsupported
  | .node _ `«dbt_rc_∨_» args =>
      match args[0]?, args[2]? with
      | some φ, some ψ => do
          let φ' ← expandRC ⟨φ⟩
          let ψ' ← expandRC ⟨ψ⟩
          `(RelCalc.Formula.or $φ' $ψ')
      | _, _ => throwUnsupported
  | .node _ `«dbt_rc¬_» args =>
      match args[1]? with
      | some φ => do
          let φ' ← expandRC ⟨φ⟩
          `(RelCalc.Formula.not $φ')
      | none => throwUnsupported
  | .node _ `«dbt_rc_→_» args =>
      match args[0]?, args[2]? with
      | some φ, some ψ => do
          let φ' ← expandRC ⟨φ⟩
          let ψ' ← expandRC ⟨ψ⟩
          `(RelCalc.Formula.imp $φ' $ψ')
      | _, _ => throwUnsupported
  | .node _ `«dbt_rc_↔_» args =>
      match args[0]?, args[2]? with
      | some φ, some ψ => do
          let φ' ← expandRC ⟨φ⟩
          let ψ' ← expandRC ⟨ψ⟩
          `(RelCalc.Formula.iff $φ' $ψ')
      | _, _ => throwUnsupported
  | .node _ `«dbt_rc∀_._» args =>
      match args[1]?, args[3]? with
      | some x, some φ => do
          let x' ← rcVarTerm ⟨x⟩
          let φ' ← expandRC ⟨φ⟩
          `(RelCalc.Formula.forall_ $x' $φ')
      | _, _ => throwUnsupported
  | .node _ `«dbt_rc∃_._» args =>
      match args[1]?, args[3]? with
      | some x, some φ => do
          let x' ← rcVarTerm ⟨x⟩
          let φ' ← expandRC ⟨φ⟩
          `(RelCalc.Formula.exists_ $x' $φ')
      | _, _ => throwUnsupported
  | .node _ `«dbt_rc(_)» args =>
      match args[1]? with
      | some φ => expandRC ⟨φ⟩
      | none => throwUnsupported
  | _ =>
      throwUnsupported

macro "relcalc![" φ:dbt_rc "]" : term =>
  expandRC φ

syntax "relcalcQuery![" dbt_rc "]" : term
syntax "relcalcQuery![" "{" dbt_rc_var " | " dbt_rc "}" "]" :
  term
syntax "relcalcQuery![" "{" "(" dbt_rc_var,* ")" " | "
  dbt_rc "}" "]" :
  term

macro_rules
| `(relcalcQuery![ $φ:dbt_rc ]) =>
    `(RelCalc.Notation.query [] relcalc![$φ] (by decide))
| `(relcalcQuery![ { $x:dbt_rc_var | $φ:dbt_rc } ]) => do
    let x' ← rcVarTerm x
    `(RelCalc.Notation.query [$x'] relcalc![$φ] (by decide))
| `(relcalcQuery![ { ( $[$xs:dbt_rc_var],* ) | $φ:dbt_rc } ]) => do
    let xs' ← xs.mapM rcVarTerm
    `(RelCalc.Notation.query [$[$xs'],*] relcalc![$φ]
      (by decide))
