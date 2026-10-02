-- Author: Jesse Comer
import Databases.UnnamedRA.Syntax

/-
  Guard syntax for Whiel assertions and commands.

  Key declarations:
    * `Guard`

  Guards are built directly from typed `RAExpr`s, so atoms
  need no separate raw syntax or well-formedness layer.
-/

------------------------------------------------------------
-- Guard Syntax
------------------------------------------------------------

namespace Whiel

/-
  Guards over a schema `Γ`.

  Equality and containment atoms compare same-arity typed
  relational algebra expressions.
-/
inductive Guard
    {A : Type} [RelationNames A]
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) : Type
| «true» : Guard D Γ
| «false» : Guard D Γ
| eq {n : Nat} (e₁ e₂ : RAExpr D Γ n) :
    Guard D Γ
| subset {n : Nat} (e₁ e₂ : RAExpr D Γ n) :
    Guard D Γ
| and (φ ψ : Guard D Γ) :
    Guard D Γ
| or (φ ψ : Guard D Γ) :
    Guard D Γ
| not (φ : Guard D Γ) :
    Guard D Γ

end Whiel

------------------------------------------------------------
-- Guard Syntactic Support
------------------------------------------------------------

namespace Whiel

namespace Guard

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Reinterpret a guard over an extending schema. -/
def onExtension
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ) :
    Guard D Γ → Guard D Δ
| .«true» => .«true»
| .«false» => .«false»
| .eq e₁ e₂ =>
    .eq (e₁.onExtension hExt) (e₂.onExtension hExt)
| .subset e₁ e₂ =>
    .subset (e₁.onExtension hExt) (e₂.onExtension hExt)
| .and φ ψ =>
    .and (onExtension hExt φ) (onExtension hExt ψ)
| .or φ ψ =>
    .or (onExtension hExt φ) (onExtension hExt ψ)
| .not φ => .not (onExtension hExt φ)

/- Relation names occurring in a guard. -/
def symbols : Guard D Γ → Finset A
| .«true» => ∅
| .«false» => ∅
| .eq e₁ e₂ => e₁.symbols ∪ e₂.symbols
| .subset e₁ e₂ => e₁.symbols ∪ e₂.symbols
| .and φ ψ => φ.symbols ∪ ψ.symbols
| .or φ ψ => φ.symbols ∪ ψ.symbols
| .not φ => φ.symbols

/- Domain constants occurring in a guard. -/
def constants : Guard D Γ → Finset D
| .«true» => ∅
| .«false» => ∅
| .eq e₁ e₂ => e₁.constants ∪ e₂.constants
| .subset e₁ e₂ => e₁.constants ∪ e₂.constants
| .and φ ψ => φ.constants ∪ ψ.constants
| .or φ ψ => φ.constants ∪ ψ.constants
| .not φ => φ.constants

/- Derived implication, represented as `¬φ ∨ ψ`. -/
def implies
    (φ ψ : Guard D Γ) :
    Guard D Γ :=
  .or (.not φ) ψ

/- Retyping over an extension preserves symbols. -/
@[simp] theorem symbols_onExtension
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (φ : Guard D Γ) :
    (φ.onExtension hExt).symbols = φ.symbols := by
  induction φ with
  | «true» =>
      rfl
  | «false» =>
      rfl
  | eq e₁ e₂ =>
      rfl
  | subset e₁ e₂ =>
      rfl
  | and φ ψ ihφ ihψ =>
      simp [onExtension, symbols, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [onExtension, symbols, ihφ, ihψ]
  | not φ ih =>
      simp [onExtension, symbols, ih]

/- Retyping over an extension does not change constants. -/
@[simp] theorem constants_onExtension
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (φ : Guard D Γ) :
    (φ.onExtension hExt).constants = φ.constants := by
  induction φ with
  | «true» =>
      rfl
  | «false» =>
      rfl
  | eq e₁ e₂ =>
      rfl
  | subset e₁ e₂ =>
      rfl
  | and φ ψ ihφ ihψ =>
      simp [onExtension, constants, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [onExtension, constants, ihφ, ihψ]
  | not φ ih =>
      simp [onExtension, constants, ih]

end Guard

end Whiel

------------------------------------------------------------
-- Raw Guard Syntax And Checking
------------------------------------------------------------

/-
  Raw Whiel guard syntax.

  This layer is syntactic infrastructure for notation and
  compiler construction. It has no separate semantics:
  well-formed raw guards are checked into typed `Guard`s
  before evaluation.
-/

namespace Whiel

/-
  Raw guards over relation names `A`.

  Equality and containment atoms carry raw RA expressions.
  The empty-relation forms infer their arity when the raw
  guard is checked against a schema.
-/
inductive RawGuard
    (A D : Type)
    [RelationNames A]
    [Domain D] : Type
| «true» : RawGuard A D
| «false» : RawGuard A D
| eq (e₁ e₂ : RawRAExpr A D) : RawGuard A D
| subset (e₁ e₂ : RawRAExpr A D) : RawGuard A D
| eqEmptyRight (e : RawRAExpr A D) : RawGuard A D
| eqEmptyLeft (e : RawRAExpr A D) : RawGuard A D
| subsetEmptyRight (e : RawRAExpr A D) : RawGuard A D
| subsetEmptyLeft (e : RawRAExpr A D) : RawGuard A D
| and (φ ψ : RawGuard A D) : RawGuard A D
| or (φ ψ : RawGuard A D) : RawGuard A D
| not (φ : RawGuard A D) : RawGuard A D
deriving DecidableEq, Repr

namespace RawGuard

variable {A D : Type}
variable [RelationNames A] [Domain D]

/- Relation names occurring in a raw guard. -/
def symbols : RawGuard A D → Finset A
| .«true» => ∅
| .«false» => ∅
| .eq e₁ e₂ => e₁.symbols ∪ e₂.symbols
| .subset e₁ e₂ => e₁.symbols ∪ e₂.symbols
| .eqEmptyRight e => e.symbols
| .eqEmptyLeft e => e.symbols
| .subsetEmptyRight e => e.symbols
| .subsetEmptyLeft e => e.symbols
| .and φ ψ => φ.symbols ∪ ψ.symbols
| .or φ ψ => φ.symbols ∪ ψ.symbols
| .not φ => φ.symbols

/- Domain constants occurring in a raw guard. -/
def constants : RawGuard A D → Finset D
| .«true» => ∅
| .«false» => ∅
| .eq e₁ e₂ => e₁.constants ∪ e₂.constants
| .subset e₁ e₂ => e₁.constants ∪ e₂.constants
| .eqEmptyRight e => e.constants
| .eqEmptyLeft e => e.constants
| .subsetEmptyRight e => e.constants
| .subsetEmptyLeft e => e.constants
| .and φ ψ => φ.constants ∪ ψ.constants
| .or φ ψ => φ.constants ∪ ψ.constants
| .not φ => φ.constants

/- Conjunction of a raw guard list. -/
def andList : List (RawGuard A D) → RawGuard A D
| [] => .«true»
| G :: Gs => .and G (andList Gs)

/- Disjunction of a raw guard list. -/
def orList : List (RawGuard A D) → RawGuard A D
| [] => .«false»
| G :: Gs => .or G (orList Gs)

/-
  Check two same-arity raw RA expressions as a guard atom.
-/
def binaryAtom?
    {Γ : UnnamedSchema A}
    (mk : {n : Nat} →
      RAExpr D Γ n → RAExpr D Γ n → Guard D Γ)
    (e₁ e₂ : RawRAExpr A D) :
    Option (Guard D Γ) :=
  match h₁ : e₁.arity? Γ, h₂ : e₂.arity? Γ with
  | some n, some m =>
      if hEq : n = m then
        some
          (mk
            (n := n)
            ({ expr := e₁, wf := h₁ } :
              RAExpr D Γ n)
            ({ expr := e₂, wf := by
                rw [hEq]
                exact h₂ } : RAExpr D Γ n))
      else
        none
  | _, _ => none

/- Check a raw guard against a schema. -/
def toGuard?
    (Γ : UnnamedSchema A) :
    RawGuard A D → Option (Guard D Γ)
| .«true» => some .«true»
| .«false» => some .«false»
| .eq e₁ e₂ => binaryAtom? (fun e₁ e₂ => .eq e₁ e₂) e₁ e₂
| .subset e₁ e₂ =>
    binaryAtom? (fun e₁ e₂ => .subset e₁ e₂) e₁ e₂
| .eqEmptyRight e =>
    match h : e.arity? Γ with
    | some n =>
        some
          (.eq
            ({ expr := e, wf := h } : RAExpr D Γ n)
            (RAExpr.empty n))
    | none => none
| .eqEmptyLeft e =>
    match h : e.arity? Γ with
    | some n =>
        some
          (.eq
            (RAExpr.empty n)
            ({ expr := e, wf := h } : RAExpr D Γ n))
    | none => none
| .subsetEmptyRight e =>
    match h : e.arity? Γ with
    | some n =>
        some
          (.subset
            ({ expr := e, wf := h } : RAExpr D Γ n)
            (RAExpr.empty n))
    | none => none
| .subsetEmptyLeft e =>
    match h : e.arity? Γ with
    | some n =>
        some
          (.subset
            (RAExpr.empty n)
            ({ expr := e, wf := h } : RAExpr D Γ n))
    | none => none
| .and φ ψ =>
    match toGuard? Γ φ, toGuard? Γ ψ with
    | some φ', some ψ' => some (.and φ' ψ')
    | _, _ => none
| .or φ ψ =>
    match toGuard? Γ φ, toGuard? Γ ψ with
    | some φ', some ψ' => some (.or φ' ψ')
    | _, _ => none
| .not φ =>
    match toGuard? Γ φ with
    | some φ' => some (.not φ')
    | none => none

/- Checked conversion from raw syntax to a typed guard. -/
def toGuard
    {Γ : UnnamedSchema A}
    (φ : RawGuard A D)
    (h : (φ.toGuard? Γ).isSome = Bool.true := by decide) :
    Guard D Γ :=
  match hφ : φ.toGuard? Γ with
  | some φ' => φ'
  | none =>
      have hFalse : False := by
        rw [hφ] at h
        contradiction
      False.elim hFalse

------------------------------------------------------------
-- Diagnostics
------------------------------------------------------------

section Diagnostics

variable [Repr A] [Repr D]

private def exprText
    (e : RawRAExpr A D) : String :=
  reprStr e

private def arityCheck
    (Γ : UnnamedSchema A) :
    RawRAExpr A D → Except String Nat
| .top => .ok 0
| .empty n => .ok n
| .rel X =>
    match Γ.arity? X with
    | some n => .ok n
    | none =>
        .error s!"unknown relation {reprStr X}"
| .single _ => .ok 1
| .select φ e =>
    match arityCheck Γ e with
    | .ok n =>
        if φ.arityReq < n then
          .ok n
        else
          .error
            (s!"selection index out of range: " ++
             s!"condition needs index {φ.arityReq}, " ++
             s!"operand arity is {n}; " ++
             s!"expression {exprText (.select φ e)}")
    | .error msg =>
        .error s!"selection operand invalid: {msg}"
| .proj idxs e =>
    match arityCheck Γ e with
    | .ok n =>
        if idxs.all (fun i => decide (i < n)) then
          .ok idxs.length
        else
          .error
            (s!"projection index out of range: " ++
             s!"indices {reprStr idxs}, operand arity {n}; " ++
             s!"expression {exprText (.proj idxs e)}")
    | .error msg =>
        .error s!"projection operand invalid: {msg}"
| .prod e₁ e₂ =>
    match arityCheck Γ e₁, arityCheck Γ e₂ with
    | .ok n, .ok m => .ok (n + m)
    | .error msg, _ =>
        .error s!"product left operand invalid: {msg}"
    | _, .error msg =>
        .error s!"product right operand invalid: {msg}"
| .union e₁ e₂ =>
    match arityCheck Γ e₁, arityCheck Γ e₂ with
    | .ok n, .ok m =>
        if n = m then
          .ok n
        else
          .error
            (s!"union arity mismatch: left arity {n}, " ++
             s!"right arity {m}; left {exprText e₁}; " ++
             s!"right {exprText e₂}")
    | .error msg, _ =>
        .error s!"union left operand invalid: {msg}"
    | _, .error msg =>
        .error s!"union right operand invalid: {msg}"
| .diff e₁ e₂ =>
    match arityCheck Γ e₁, arityCheck Γ e₂ with
    | .ok n, .ok m =>
        if n = m then
          .ok n
        else
          .error
            (s!"difference arity mismatch: left arity {n}, " ++
             s!"right arity {m}; left {exprText e₁}; " ++
             s!"right {exprText e₂}")
    | .error msg, _ =>
        .error s!"difference left operand invalid: {msg}"
    | _, .error msg =>
        .error s!"difference right operand invalid: {msg}"

private def binaryAtomError?
    (name : String)
    (Γ : UnnamedSchema A)
    (e₁ e₂ : RawRAExpr A D) :
    Option String :=
  match arityCheck Γ e₁, arityCheck Γ e₂ with
  | .ok n, .ok m =>
      if n = m then
        none
      else
        some
          (s!"{name} arity mismatch: left arity {n}, " ++
           s!"right arity {m}; left {exprText e₁}; " ++
           s!"right {exprText e₂}")
  | .error msg, _ =>
      some s!"{name} left operand invalid: {msg}"
  | _, .error msg =>
      some s!"{name} right operand invalid: {msg}"

private def unaryAtomError?
    (name : String)
    (Γ : UnnamedSchema A)
    (e : RawRAExpr A D) :
    Option String :=
  match arityCheck Γ e with
  | .ok _ => none
  | .error msg =>
      some s!"{name} operand invalid: {msg}"

/- Explain why a raw guard is not well formed, if it fails. -/
def wellFormedError?
    (Γ : UnnamedSchema A) :
    RawGuard A D → Option String
| .«true» => none
| .«false» => none
| .eq e₁ e₂ => binaryAtomError? "equality" Γ e₁ e₂
| .subset e₁ e₂ =>
    binaryAtomError? "containment" Γ e₁ e₂
| .eqEmptyRight e =>
    unaryAtomError? "equality-to-empty" Γ e
| .eqEmptyLeft e =>
    unaryAtomError? "equality-from-empty" Γ e
| .subsetEmptyRight e =>
    unaryAtomError? "containment-to-empty" Γ e
| .subsetEmptyLeft e =>
    unaryAtomError? "containment-from-empty" Γ e
| .and φ ψ =>
    match wellFormedError? Γ φ with
    | some msg => some s!"left conjunct invalid: {msg}"
    | none =>
        match wellFormedError? Γ ψ with
        | some msg => some s!"right conjunct invalid: {msg}"
        | none => none
| .or φ ψ =>
    match wellFormedError? Γ φ with
    | some msg => some s!"left disjunct invalid: {msg}"
    | none =>
        match wellFormedError? Γ ψ with
        | some msg => some s!"right disjunct invalid: {msg}"
        | none => none
| .not φ =>
    match wellFormedError? Γ φ with
    | some msg => some s!"negated guard invalid: {msg}"
    | none => none

end Diagnostics

@[simp] private theorem rawRAExpr_heq
    {Γ : UnnamedSchema A}
    {m n : Nat}
    {e : RawRAExpr A D}
    (hm : e.arity? Γ = some m)
    (hn : e.arity? Γ = some n) :
    HEq
      ({ expr := e, wf := hm } : RAExpr D Γ m)
      ({ expr := e, wf := hn } : RAExpr D Γ n) := by
  have hmn : m = n := by
    rw [hm] at hn
    injection hn
  subst n
  simp

/-
  Checking the raw form of a typed equality atom recovers
  it.
-/
theorem toGuard?_eq_expr
    {Γ : UnnamedSchema A}
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n) :
    (RawGuard.eq e₁.expr e₂.expr).toGuard? Γ =
      some (Guard.eq e₁ e₂) := by
  cases e₁ with
  | mk expr₁ wf₁ =>
      cases e₂ with
          | mk expr₂ wf₂ =>
          change
            binaryAtom?
                (fun {n} e₁ e₂ => Guard.eq e₁ e₂)
                expr₁ expr₂ =
              some
                (Guard.eq
                  ({ expr := expr₁, wf := wf₁ } :
                    RAExpr D Γ n)
                  ({ expr := expr₂, wf := wf₂ } :
                    RAExpr D Γ n))
          unfold binaryAtom?
          split <;> aesop

/-
  Checking the raw form of a typed containment atom
  recovers it.
-/
theorem toGuard?_subset_expr
    {Γ : UnnamedSchema A}
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n) :
    (RawGuard.subset e₁.expr e₂.expr).toGuard? Γ =
      some (Guard.subset e₁ e₂) := by
  cases e₁ with
  | mk expr₁ wf₁ =>
      cases e₂ with
          | mk expr₂ wf₂ =>
          change
            binaryAtom?
                (fun {n} e₁ e₂ => Guard.subset e₁ e₂)
                expr₁ expr₂ =
              some
                (Guard.subset
                  ({ expr := expr₁, wf := wf₁ } :
                    RAExpr D Γ n)
                  ({ expr := expr₂, wf := wf₂ } :
                    RAExpr D Γ n))
          unfold binaryAtom?
          split <;> aesop

end RawGuard

namespace Guard

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Erase a typed guard to its raw syntax. -/
def toRaw :
    Guard D Γ → RawGuard A D
| .«true» => .«true»
| .«false» => .«false»
| .eq e₁ e₂ => .eq e₁.expr e₂.expr
| .subset e₁ e₂ => .subset e₁.expr e₂.expr
| .and φ ψ => .and φ.toRaw ψ.toRaw
| .or φ ψ => .or φ.toRaw ψ.toRaw
| .not φ => .not φ.toRaw

/- Checking a typed guard's raw syntax recovers it. -/
@[simp] theorem toRaw_toGuard?
    (G : Guard D Γ) :
    G.toRaw.toGuard? Γ = some G := by
  induction G with
  | «true» =>
      rfl
  | «false» =>
      rfl
  | eq e₁ e₂ =>
      exact RawGuard.toGuard?_eq_expr e₁ e₂
  | subset e₁ e₂ =>
      exact RawGuard.toGuard?_subset_expr e₁ e₂
  | and φ ψ hφ hψ =>
      simp [toRaw, RawGuard.toGuard?, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [toRaw, RawGuard.toGuard?, hφ, hψ]
  | not φ hφ =>
      simp [toRaw, RawGuard.toGuard?, hφ]

/- Equal raw syntax gives equal typed guards. -/
theorem eq_of_toRaw_eq
    {G H : Guard D Γ}
    (hRaw : G.toRaw = H.toRaw) :
    G = H := by
  have hG := toRaw_toGuard? G
  have hH := toRaw_toGuard? H
  rw [hRaw] at hG
  rw [hH] at hG
  injection hG with hEq
  exact hEq.symm

end Guard

end Whiel
