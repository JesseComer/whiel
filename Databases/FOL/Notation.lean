-- Author: Jesse Comer
import Databases.Core.Notation
import Databases.FOL.PrettyPrint

/-
  Typed notation for first-order logic examples.

  Key declaration: `fol![...]`.
-/

namespace FOL

namespace Notation

variable {A F : Type}
variable [RelationNames A] [FunctionNames F]
variable {Sig : Signature A F}

/- Build a function term from a checked raw name. -/
def func
    (f : F)
    (h : f ∈ Sig.funs := by decide)
    (args : TermList Sig (Sig.funArity (Sig.func f h))) :
    Term Sig :=
  .func (Sig.func f h) args

/- Build a relation atom from a checked raw name. -/
def rel
    (X : A)
    (h : X ∈ Sig.syms := by decide)
    (ts : TermList Sig (Sig.arity (Sig.sym X h))) :
    Formula Sig :=
  .rel (Sig.sym X h) ts

end Notation

end FOL

------------------------------------------------------------
-- Surface Notation
------------------------------------------------------------

declare_syntax_cat dbt_fol_term
declare_syntax_cat dbt_fol_var

syntax ident : dbt_fol_var
syntax term:80 : dbt_fol_term
syntax term:80 "(" dbt_fol_term,* ")" : dbt_fol_term

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

private def folVarTerm
    (v : TSyntax `dbt_fol_var) :
    MacroM Term := do
  match v with
  | `(dbt_fol_var| $id:ident) =>
      match varOfIdent? id with
      | some x => pure (natTerm x)
      | none =>
          Macro.throwErrorAt id.raw
            "expected one of x1, y1, z1, x2, ..."
  | _ =>
      throwUnsupported

private partial def preferFOLTermChoice (stx : Syntax) :
    Syntax :=
  match stx with
  | .node _ `choice choices =>
      match choices.back? with
      | some stx' => preferFOLTermChoice stx'
      | none => stx
  | _ => stx

private def commaFOLTerms (stx : Syntax) :
    Array (TSyntax `dbt_fol_term) :=
  stx.getArgs.filterMap fun arg =>
    match arg with
    | .atom _ "," => none
    | other => some ⟨other⟩

private partial def expandFOLTerm
    (t : TSyntax `dbt_fol_term) :
    MacroM Term := do
  let raw := preferFOLTermChoice t.raw
  match raw with
  | .node _ `«dbt_fol_term_(_)» args =>
      match args[0]?, args[2]? with
      | some f, some tsRaw =>
          let fTerm : Term := ⟨f⟩
          let fTerm' ← DBLib.Notation.expandLiteralTerm fTerm
          let ts := commaFOLTerms tsRaw
          let ts' ← ts.mapM expandFOLTerm
          `(FOL.Notation.func $fTerm'
            (h := by decide)
            (FOL.TermList.ofVector
              (Vector.mk #[ $ts',* ] (by decide))))
      | _, _ => throwUnsupported
  | .node _ `dbt_fol_term_ args =>
      match args[0]? with
      | some f =>
          let fTerm : Term := ⟨f⟩
          match varOfTerm? fTerm with
          | some x =>
              let xTerm := natTerm x
              `(FOL.Term.var $xTerm)
          | none => do
              let fTerm' ← DBLib.Notation.expandLiteralTerm fTerm
              `(FOL.Notation.func $fTerm'
                (h := by decide)
                (FOL.TermList.ofVector
                  (Vector.mk #[] (by decide))))
      | none => throwUnsupported
  | _ =>
      throwUnsupported

declare_syntax_cat dbt_fol

syntax "⊤" : dbt_fol
syntax "⊥" : dbt_fol
syntax dbt_fol_term " = " dbt_fol_term : dbt_fol
syntax term:80 "(" dbt_fol_term,* ")" : dbt_fol
syntax dbt_fol:66 " ∧ " dbt_fol:67 : dbt_fol
syntax dbt_fol:61 " ∨ " dbt_fol:62 : dbt_fol
syntax "¬" dbt_fol:70 : dbt_fol
syntax dbt_fol:55 " → " dbt_fol:56 : dbt_fol
syntax dbt_fol:50 " ↔ " dbt_fol:51 : dbt_fol
syntax "∀ " dbt_fol_var ". " dbt_fol : dbt_fol
syntax "∃ " dbt_fol_var ". " dbt_fol : dbt_fol
syntax "(" dbt_fol ")" : dbt_fol

syntax "fol![" dbt_fol "]" : term

private partial def preferFOLChoice (stx : Syntax) :
    Syntax :=
  match stx with
  | .node _ `choice choices =>
      match choices.back? with
      | some stx' => preferFOLChoice stx'
      | none => stx
  | _ => stx

private partial def expandFOL
    (φ : TSyntax `dbt_fol) :
    MacroM Term := do
  let raw := preferFOLChoice φ.raw
  match raw with
  | .node _ `«dbt_fol⊤» _ =>
      `(FOL.Formula.top)
  | .node _ `«dbt_fol⊥» _ =>
      `(FOL.Formula.bot)
  | .node _ `«dbt_fol_=_» args =>
      match args[0]?, args[2]? with
      | some t₁, some t₂ =>
          let t₁Stx : TSyntax `dbt_fol_term := ⟨t₁⟩
          let t₂Stx : TSyntax `dbt_fol_term := ⟨t₂⟩
          let t₁' ← expandFOLTerm t₁Stx
          let t₂' ← expandFOLTerm t₂Stx
          `(FOL.Formula.eq $t₁' $t₂')
      | _, _ => throwUnsupported
  | .node _ `«dbt_fol_(_)» args =>
      match args[0]?, args[2]? with
      | some X, some tsRaw =>
          let XTerm : Term := ⟨X⟩
          let ts := commaFOLTerms tsRaw
          let ts' ← ts.mapM expandFOLTerm
          `(FOL.Notation.rel $XTerm
            (h := by decide)
            (FOL.TermList.ofVector
              (Vector.mk #[ $ts',* ] (by decide))))
      | _, _ => throwUnsupported
  | .node _ `«dbt_fol_∧_» args =>
      match args[0]?, args[2]? with
      | some φ, some ψ => do
          let φ' ← expandFOL ⟨φ⟩
          let ψ' ← expandFOL ⟨ψ⟩
          `(FOL.Formula.and $φ' $ψ')
      | _, _ => throwUnsupported
  | .node _ `«dbt_fol_∨_» args =>
      match args[0]?, args[2]? with
      | some φ, some ψ => do
          let φ' ← expandFOL ⟨φ⟩
          let ψ' ← expandFOL ⟨ψ⟩
          `(FOL.Formula.or $φ' $ψ')
      | _, _ => throwUnsupported
  | .node _ `«dbt_fol¬_» args =>
      match args[1]? with
      | some φ => do
          let φ' ← expandFOL ⟨φ⟩
          `(FOL.Formula.not $φ')
      | none => throwUnsupported
  | .node _ `«dbt_fol_→_» args =>
      match args[0]?, args[2]? with
      | some φ, some ψ => do
          let φ' ← expandFOL ⟨φ⟩
          let ψ' ← expandFOL ⟨ψ⟩
          `(FOL.Formula.imp $φ' $ψ')
      | _, _ => throwUnsupported
  | .node _ `«dbt_fol_↔_» args =>
      match args[0]?, args[2]? with
      | some φ, some ψ => do
          let φ' ← expandFOL ⟨φ⟩
          let ψ' ← expandFOL ⟨ψ⟩
          `(FOL.Formula.iff $φ' $ψ')
      | _, _ => throwUnsupported
  | .node _ `«dbt_fol∀_._» args =>
      match args[1]?, args[3]? with
      | some x, some φ => do
          let x' ← folVarTerm ⟨x⟩
          let φ' ← expandFOL ⟨φ⟩
          `(FOL.Formula.forall_ $x' $φ')
      | _, _ => throwUnsupported
  | .node _ `«dbt_fol∃_._» args =>
      match args[1]?, args[3]? with
      | some x, some φ => do
          let x' ← folVarTerm ⟨x⟩
          let φ' ← expandFOL ⟨φ⟩
          `(FOL.Formula.exists_ $x' $φ')
      | _, _ => throwUnsupported
  | .node _ `«dbt_fol(_)» args =>
      match args[1]? with
      | some φ => expandFOL ⟨φ⟩
      | none => throwUnsupported
  | _ =>
      throwUnsupported

macro "fol![" φ:dbt_fol "]" : term =>
  expandFOL φ
