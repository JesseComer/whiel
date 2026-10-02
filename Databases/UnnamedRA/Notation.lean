-- Author: Jesse Comer
import Lean
import Databases.Core.Notation
import Databases.UnnamedRA.PrettyPrint

/-
  Well-formed notation for unnamed relational algebra
  examples.

  `ra![...]` elaborates surface syntax into typed
  `RAExpr` constructors.
-/

------------------------------------------------------------
-- Surface Notation
------------------------------------------------------------

namespace RAExpr

namespace Notation

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Build a relation expression from a checked raw name. -/
def rel
    (X : A)
    (h : X ∈ Γ.syms := by decide) :
    RAExpr D Γ (Γ.arity (Γ.sym X h)) :=
  RAExpr.rel (Γ.sym X h)

end Notation

end RAExpr

declare_syntax_cat dbt_sel

syntax:max "#" num "=" "#" num : dbt_sel
syntax:max "#" num "=" term:70 : dbt_sel
syntax:66 dbt_sel:66 " ∧ " dbt_sel:67 : dbt_sel
syntax:61 dbt_sel:61 " ∨ " dbt_sel:62 : dbt_sel
syntax:70 "¬" dbt_sel:70 : dbt_sel
syntax:max "(" dbt_sel ")" : dbt_sel

declare_syntax_cat dbt_ra

syntax:max "⊤" : dbt_ra
syntax:max "∅[" term "]" : dbt_ra
syntax:max "{" term "}" : dbt_ra
syntax:max ident : dbt_ra
syntax:80 "σ[" dbt_sel "]" dbt_ra:80 : dbt_ra
syntax:80 "π[" term,* "]" dbt_ra:80 : dbt_ra
syntax:71 dbt_ra:71 " × " dbt_ra:72 : dbt_ra
syntax:66 dbt_ra:66 " ∪ " dbt_ra:67 : dbt_ra
syntax:66 dbt_ra:66 " ∖ " dbt_ra:67 : dbt_ra
syntax:max "(" dbt_ra ")" : dbt_ra

open Lean Macro

private partial def expandSel :
    TSyntax `dbt_sel → MacroM Term
| `(dbt_sel| #$i:num = #$j:num) =>
    `(Sel.eqIdx $i $j)
| `(dbt_sel| #$i:num = $c:term) => do
    let c' ← DBLib.Notation.expandLiteralTerm c
    `(Sel.eqConst $i $c')
| `(dbt_sel| $φ:dbt_sel ∧ $ψ:dbt_sel) => do
    let φ' ← expandSel φ
    let ψ' ← expandSel ψ
    `(Sel.and $φ' $ψ')
| `(dbt_sel| $φ:dbt_sel ∨ $ψ:dbt_sel) => do
    let φ' ← expandSel φ
    let ψ' ← expandSel ψ
    `(Sel.or $φ' $ψ')
| `(dbt_sel| ¬$φ:dbt_sel) => do
    let φ' ← expandSel φ
    `(Sel.not $φ')
| `(dbt_sel| ( $φ:dbt_sel )) =>
    expandSel φ
| _ =>
    throwUnsupported

private partial def expandTypedRA
    (e : TSyntax `dbt_ra) : MacroM Term :=
  match e with
  | `(dbt_ra| ⊤) =>
      `(RAExpr.top)
  | `(dbt_ra| ∅[$n:term]) =>
      `(RAExpr.empty $n)
  | `(dbt_ra| {$d:term}) => do
      let d' ← DBLib.Notation.expandLiteralTerm d
      `(RAExpr.single $d')
  | `(dbt_ra| $X:ident) =>
      let XTerm : Term := ⟨X.raw⟩
      `(RAExpr.Notation.rel $XTerm
        (h := by decide +kernel))
  | `(dbt_ra| σ[$φ:dbt_sel] $e:dbt_ra) => do
      let φ' ← expandSel φ
      let e' ← expandTypedRA e
      `(RAExpr.select $φ' $e'
        (by decide +kernel))
  | `(dbt_ra| π[$idxs:term,*] $e:dbt_ra) => do
      let e' ← expandTypedRA e
      `(RAExpr.proj [$idxs,*] $e'
        (by decide +kernel))
  | `(dbt_ra| $e₁:dbt_ra × $e₂:dbt_ra) => do
      let e₁' ← expandTypedRA e₁
      let e₂' ← expandTypedRA e₂
      `(RAExpr.prod $e₁' $e₂')
  | `(dbt_ra| $e₁:dbt_ra ∪ $e₂:dbt_ra) => do
      let e₁' ← expandTypedRA e₁
      let e₂' ← expandTypedRA e₂
      `(RAExpr.union $e₁' $e₂')
  | `(dbt_ra| $e₁:dbt_ra ∖ $e₂:dbt_ra) => do
      let e₁' ← expandTypedRA e₁
      let e₂' ← expandTypedRA e₂
      `(RAExpr.diff $e₁' $e₂')
  | `(dbt_ra| ( $e:dbt_ra )) =>
      expandTypedRA e
  | _ =>
      throwUnsupported

syntax (name := dbtRANotation) "ra![" dbt_ra "]" : term

open Lean Elab Term

@[term_elab dbtRANotation] def elabRANotation :
    TermElab := fun stx expectedType? => do
  match stx with
  | `(ra![$e:dbt_ra]) => do
      let e' ← liftMacroM <| expandTypedRA e
      Term.elabTerm e' expectedType?
  | _ =>
      throwUnsupportedSyntax
