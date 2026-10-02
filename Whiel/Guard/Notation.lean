-- Author: Jesse Comer
import Whiel.Guard.Syntax
import Whiel.Guard.PrettyPrint
import Whiel.Concrete.Data
import Databases.Core.Notation
import Databases.UnnamedRA.Notation

/-
  Whiel-owned guard notation infrastructure.

  This file provides the parser used by `whiel![...]` for
  command guards. It keeps raw syntax internal and uses the
  shared raw RA parser for embedded relational expressions.
  String, numeral, and Boolean literals inside those
  expressions are rewritten to `Whiel.Concrete.Data`.
-/

namespace RAExpr

namespace Notation

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Build a typed expression from a checked raw expression.
-/
def ofRaw
    {n : Nat}
    (e : RawRAExpr A D)
    (h : e.arity? Γ = some n := by decide) :
    RAExpr D Γ n where
  expr := e
  wf := h

end Notation

end RAExpr

namespace Whiel

namespace Guard

namespace Notation

section CheckedRaw

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A} {n : Nat}

/- Equality between checked raw RA expressions. -/
def eqRaw
    (e₁ e₂ : RawRAExpr A D)
    (hSome :
      (e₁.arity? Γ).isSome = Bool.true := by decide)
    (hEq :
      e₁.arity? Γ = e₂.arity? Γ := by decide) :
    Guard D Γ :=
  match h₁ : e₁.arity? Γ with
  | some n =>
      have h₂ :
          e₂.arity? Γ = some n := by
        rw [h₁] at hEq
        exact hEq.symm
      Guard.eq
        (RAExpr.Notation.ofRaw
          (Γ := Γ) (n := n) e₁ (h := h₁))
        (RAExpr.Notation.ofRaw
          (Γ := Γ) (n := n) e₂ (h := h₂))
  | none =>
      have hFalse : False := by
        simp [h₁] at hSome
      False.elim hFalse

/- Containment between checked raw RA expressions. -/
def subsetRaw
    (e₁ e₂ : RawRAExpr A D)
    (hSome :
      (e₁.arity? Γ).isSome = Bool.true := by decide)
    (hEq :
      e₁.arity? Γ = e₂.arity? Γ := by decide) :
    Guard D Γ :=
  match h₁ : e₁.arity? Γ with
  | some n =>
      have h₂ :
          e₂.arity? Γ = some n := by
        rw [h₁] at hEq
        exact hEq.symm
      Guard.subset
        (RAExpr.Notation.ofRaw
          (Γ := Γ) (n := n) e₁ (h := h₁))
        (RAExpr.Notation.ofRaw
          (Γ := Γ) (n := n) e₂ (h := h₂))
  | none =>
      have hFalse : False := by
        simp [h₁] at hSome
      False.elim hFalse

/- Equality with an arity-inferred empty relation. -/
def eqEmptyRightRaw
    (e : RawRAExpr A D)
    (hSome :
      (e.arity? Γ).isSome = Bool.true := by decide) :
    Guard D Γ :=
  match h : e.arity? Γ with
  | some n =>
      Guard.eq
        (RAExpr.Notation.ofRaw
          (Γ := Γ) (n := n) e (h := h))
        (RAExpr.empty n)
  | none =>
      have hFalse : False := by
        simp [h] at hSome
      False.elim hFalse

/- Equality from an arity-inferred empty relation. -/
def eqEmptyLeftRaw
    (e : RawRAExpr A D)
    (hSome :
      (e.arity? Γ).isSome = Bool.true := by decide) :
    Guard D Γ :=
  match h : e.arity? Γ with
  | some n =>
      Guard.eq
        (RAExpr.empty n)
        (RAExpr.Notation.ofRaw
          (Γ := Γ) (n := n) e (h := h))
  | none =>
      have hFalse : False := by
        simp [h] at hSome
      False.elim hFalse

/- Containment in an arity-inferred empty relation. -/
def subsetEmptyRightRaw
    (e : RawRAExpr A D)
    (hSome :
      (e.arity? Γ).isSome = Bool.true := by decide) :
    Guard D Γ :=
  match h : e.arity? Γ with
  | some n =>
      Guard.subset
        (RAExpr.Notation.ofRaw
          (Γ := Γ) (n := n) e (h := h))
        (RAExpr.empty n)
  | none =>
      have hFalse : False := by
        simp [h] at hSome
      False.elim hFalse

/- Containment of an arity-inferred empty relation. -/
def subsetEmptyLeftRaw
    (e : RawRAExpr A D)
    (hSome :
      (e.arity? Γ).isSome = Bool.true := by decide) :
    Guard D Γ :=
  match h : e.arity? Γ with
  | some n =>
      Guard.subset
        (RAExpr.empty n)
        (RAExpr.Notation.ofRaw
          (Γ := Γ) (n := n) e (h := h))
  | none =>
      have hFalse : False := by
        simp [h] at hSome
      False.elim hFalse

/- Empty relation at the same arity as an expression. -/
def emptyLike (_e : RAExpr D Γ n) : RAExpr D Γ n :=
  RAExpr.empty n

end CheckedRaw

end Notation

end Guard

end Whiel

------------------------------------------------------------
-- Surface Notation
------------------------------------------------------------

declare_syntax_cat dbt_guard (behavior := both)

syntax &"true" : dbt_guard
syntax &"false" : dbt_guard
syntax dbt_ra " = " dbt_ra : dbt_guard
syntax dbt_ra " ⊆ " dbt_ra : dbt_guard
syntax dbt_ra " = " "∅" : dbt_guard
syntax "∅" " = " dbt_ra : dbt_guard
syntax dbt_ra " ⊆ " "∅" : dbt_guard
syntax "∅" " ⊆ " dbt_ra : dbt_guard
syntax dbt_ra " ≠ " dbt_ra : dbt_guard
syntax dbt_ra " ≠ " "∅" : dbt_guard
syntax "∅" " ≠ " dbt_ra : dbt_guard
syntax dbt_guard:66 " ∧ " dbt_guard:67 : dbt_guard
syntax dbt_guard:61 " ∨ " dbt_guard:62 : dbt_guard
syntax "¬" dbt_guard:70 : dbt_guard
syntax "(" dbt_guard ")" : dbt_guard

open Lean Macro

private partial def preferWhielRAChoice (stx : Syntax) :
    Syntax :=
  match stx with
  | .node _ `choice choices =>
      match choices.back? with
      | some stx' => preferWhielRAChoice stx'
      | none => stx
  | _ => stx

private partial def singletonData (stx : Syntax) :
    Option Term :=
  match stx with
  | .node _ `choice choices =>
      choices.findSome? singletonData
  | .node _ `«dbt_ra{_}» args =>
      match args[1]? with
      | some rawTerm => some ⟨rawTerm⟩
      | none => none
  | _ => none

private def commaTerms (stx : Syntax) :
    Array Term :=
  stx.getArgs.filterMap fun arg =>
    match arg with
    | .atom _ "," => none
    | other => some ⟨other⟩

private def appTerm (fn : Name) (args : Array Term) :
    Term :=
  ⟨Syntax.mkApp (mkCIdent fn) args⟩

private def expandWhielDataLiteral
    (t : Term) :
    MacroM Term :=
  DBLib.Notation.expandLiteralTerm t

private partial def expandWhielSel
    (φ : TSyntax `dbt_sel) :
    MacroM Term := do
  match φ with
  | `(dbt_sel| #$i:num = #$j:num) =>
      pure <| appTerm ``Sel.eqIdx #[⟨i.raw⟩, ⟨j.raw⟩]
  | `(dbt_sel| #$i:num = $c:term) => do
      let cRaw ← expandWhielDataLiteral c
      pure <| appTerm ``Sel.eqConst #[⟨i.raw⟩, cRaw]
  | `(dbt_sel| $φ:dbt_sel ∧ $ψ:dbt_sel) => do
      let φRaw ← expandWhielSel φ
      let ψRaw ← expandWhielSel ψ
      pure <| appTerm ``Sel.and #[φRaw, ψRaw]
  | `(dbt_sel| $φ:dbt_sel ∨ $ψ:dbt_sel) => do
      let φRaw ← expandWhielSel φ
      let ψRaw ← expandWhielSel ψ
      pure <| appTerm ``Sel.or #[φRaw, ψRaw]
  | `(dbt_sel| ¬$φ:dbt_sel) => do
      let φRaw ← expandWhielSel φ
      pure <| appTerm ``Sel.not #[φRaw]
  | `(dbt_sel| ($φ:dbt_sel)) =>
      expandWhielSel φ
  | _ =>
      throwUnsupported

partial def expandWhielRA
    (e : TSyntax `dbt_ra) :
    MacroM Term := do
  let raw := preferWhielRAChoice e.raw
  if let some d := singletonData raw then
    let dRaw ← expandWhielDataLiteral d
    `(RawRAExpr.single $dRaw)
  else
    match raw with
    | .node _ `«dbt_ra⊤» _ =>
        pure <| appTerm ``RawRAExpr.top #[]
    | .node _ `«dbt_ra∅[_]» args =>
        match args[1]? with
        | some n =>
            let nTerm : Term := ⟨n⟩
            pure <| appTerm ``RawRAExpr.empty #[nTerm]
        | none => throwUnsupported
    | .node _ `«dbt_raσ[_]_» args =>
        match args[1]?, args[3]? with
        | some φ, some e => do
            let e' ← expandWhielRA ⟨e⟩
            let φStx : TSyntax `dbt_sel := ⟨φ⟩
            let φ' ← expandWhielSel φStx
            pure <| appTerm ``RawRAExpr.select #[φ', e']
        | _, _ => throwUnsupported
    | .node _ `«dbt_raπ[_]_» args =>
        match args[1]?, args[3]? with
        | some idxs, some e => do
            let e' ← expandWhielRA ⟨e⟩
            let idxTerms := commaTerms idxs
            let idxList ← `([$[$idxTerms],*])
            pure <| appTerm ``RawRAExpr.proj #[idxList, e']
        | _, _ => throwUnsupported
    | .node _ `«dbt_ra_×_» args =>
        match args[0]?, args[2]? with
        | some e₁, some e₂ => do
            let e₁' ← expandWhielRA ⟨e₁⟩
            let e₂' ← expandWhielRA ⟨e₂⟩
            pure <| appTerm ``RawRAExpr.prod #[e₁', e₂']
        | _, _ => throwUnsupported
    | .node _ `«dbt_ra_∪_» args =>
        match args[0]?, args[2]? with
        | some e₁, some e₂ => do
            let e₁' ← expandWhielRA ⟨e₁⟩
            let e₂' ← expandWhielRA ⟨e₂⟩
            pure <| appTerm ``RawRAExpr.union #[e₁', e₂']
        | _, _ => throwUnsupported
    | .node _ `«dbt_ra_∖_» args =>
        match args[0]?, args[2]? with
        | some e₁, some e₂ => do
            let e₁' ← expandWhielRA ⟨e₁⟩
            let e₂' ← expandWhielRA ⟨e₂⟩
            pure <| appTerm ``RawRAExpr.diff #[e₁', e₂']
        | _, _ => throwUnsupported
    | .node _ `«dbt_ra(_)» args =>
        match args[1]? with
        | some e => expandWhielRA ⟨e⟩
        | none => throwUnsupported
    | .node _ `dbt_ra_ args =>
        match args[0]? with
        | some X =>
            let XTerm : Term := ⟨X⟩
            pure <| appTerm ``RawRAExpr.rel #[XTerm]
        | none => throwUnsupported
    | _ =>
        throwUnsupported

/-
  Expand surface guard syntax into raw syntax before schema
  checking. This function is notation infrastructure, not a
  public raw-notation interface.
-/
partial def expandRawGuard
    (G : TSyntax `dbt_guard) :
    MacroM Term := do
  match G with
  | `(dbt_guard| true) =>
      pure <| appTerm ``Whiel.RawGuard.«true» #[]
  | `(dbt_guard| false) =>
      pure <| appTerm ``Whiel.RawGuard.«false» #[]
  | `(dbt_guard| $e₁:dbt_ra = $e₂:dbt_ra) => do
      let e₁Raw ← expandWhielRA e₁
      let e₂Raw ← expandWhielRA e₂
      pure <| appTerm ``Whiel.RawGuard.eq #[e₁Raw, e₂Raw]
  | `(dbt_guard| $e₁:dbt_ra ⊆ $e₂:dbt_ra) => do
      let e₁Raw ← expandWhielRA e₁
      let e₂Raw ← expandWhielRA e₂
      pure <| appTerm ``Whiel.RawGuard.subset #[e₁Raw, e₂Raw]
  | `(dbt_guard| $e:dbt_ra = ∅) => do
      let eRaw ← expandWhielRA e
      pure <| appTerm ``Whiel.RawGuard.eqEmptyRight #[eRaw]
  | `(dbt_guard| ∅ = $e:dbt_ra) => do
      let eRaw ← expandWhielRA e
      pure <| appTerm ``Whiel.RawGuard.eqEmptyLeft #[eRaw]
  | `(dbt_guard| $e:dbt_ra ⊆ ∅) => do
      let eRaw ← expandWhielRA e
      pure <| appTerm ``Whiel.RawGuard.subsetEmptyRight #[eRaw]
  | `(dbt_guard| ∅ ⊆ $e:dbt_ra) => do
      let eRaw ← expandWhielRA e
      pure <| appTerm ``Whiel.RawGuard.subsetEmptyLeft #[eRaw]
  | `(dbt_guard| $e₁:dbt_ra ≠ $e₂:dbt_ra) => do
      let e₁Raw ← expandWhielRA e₁
      let e₂Raw ← expandWhielRA e₂
      let eqRaw := appTerm ``Whiel.RawGuard.eq #[e₁Raw, e₂Raw]
      pure <| appTerm ``Whiel.RawGuard.not #[eqRaw]
  | `(dbt_guard| $e:dbt_ra ≠ ∅) => do
      let eRaw ← expandWhielRA e
      let eqRaw := appTerm ``Whiel.RawGuard.eqEmptyRight #[eRaw]
      pure <| appTerm ``Whiel.RawGuard.not #[eqRaw]
  | `(dbt_guard| ∅ ≠ $e:dbt_ra) => do
      let eRaw ← expandWhielRA e
      let eqRaw := appTerm ``Whiel.RawGuard.eqEmptyLeft #[eRaw]
      pure <| appTerm ``Whiel.RawGuard.not #[eqRaw]
  | `(dbt_guard| $φ:dbt_guard ∧ $ψ:dbt_guard) => do
      let φRaw ← expandRawGuard φ
      let ψRaw ← expandRawGuard ψ
      pure <| appTerm ``Whiel.RawGuard.and #[φRaw, ψRaw]
  | `(dbt_guard| $φ:dbt_guard ∨ $ψ:dbt_guard) => do
      let φRaw ← expandRawGuard φ
      let ψRaw ← expandRawGuard ψ
      pure <| appTerm ``Whiel.RawGuard.or #[φRaw, ψRaw]
  | `(dbt_guard| ¬$φ:dbt_guard) => do
      let φRaw ← expandRawGuard φ
      pure <| appTerm ``Whiel.RawGuard.not #[φRaw]
  | `(dbt_guard| ($φ:dbt_guard)) =>
      expandRawGuard φ
  | _ =>
      throwUnsupported
