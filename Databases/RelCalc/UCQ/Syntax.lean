-- Author: Jesse Comer
import Databases.RelCalc.CQ.Syntax

/-
  This file specifies the union-of-conjunctive-queries
  fragment of relational calculus.

  Key definitions include:
    * `RelCalc.Formula.IsUCQ`
    * `RelCalc.UCQFormula`

  Key theorems include:
    * `RelCalc.Formula.IsCQ.toIsUCQ`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Unions Of Conjunctive Queries
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  UCQ formulas are finite disjunctions of CQ formulas.
  A single CQ is a UCQ; binary `or` builds finite unions.
-/
def IsUCQ : Formula D Γ → Prop
| .or φ ψ => IsUCQ φ ∧ IsUCQ ψ
| .top => True
| .bot => True
| .eq _ _ => True
| .rel _ => True
| .and φ ψ => φ.IsConjunctive ∧ ψ.IsConjunctive
| .not _ => False
| .imp _ _ => False
| .iff _ _ => False
| .forall_ _ _ => False
| .exists_ _ φ => φ.IsCQ

/-
  UCQ membership is decidable by structural recursion on
  formulas.
-/
def IsUCQ.decidable :
    (φ : Formula D Γ) → Decidable (IsUCQ φ)
| .or φ ψ =>
    match IsUCQ.decidable φ,
        IsUCQ.decidable ψ with
    | isTrue hφ, isTrue hψ => isTrue ⟨hφ, hψ⟩
    | isFalse hφ, _ =>
        isFalse (fun h => hφ h.1)
    | _, isFalse hψ =>
        isFalse (fun h => hψ h.2)
| .top => isTrue trivial
| .bot => isTrue trivial
| .eq _ _ => isTrue trivial
| .rel _ => isTrue trivial
| .and φ ψ =>
    match Formula.IsConjunctive.decidable φ,
        Formula.IsConjunctive.decidable ψ with
    | isTrue hφ, isTrue hψ => isTrue ⟨hφ, hψ⟩
    | isFalse hφ, _ =>
        isFalse (fun h => hφ h.1)
    | _, isFalse hψ =>
        isFalse (fun h => hψ h.2)
| .not _ => isFalse (fun h => h)
| .imp _ _ => isFalse (fun h => h)
| .iff _ _ => isFalse (fun h => h)
| .forall_ _ _ => isFalse (fun h => h)
| .exists_ _ φ => Formula.IsCQ.decidable φ

instance
    (φ : Formula D Γ) :
    Decidable φ.IsUCQ :=
  IsUCQ.decidable φ

/- Every CQ formula is a UCQ formula. -/
theorem IsCQ.toIsUCQ
    {φ : Formula D Γ}
    (h : φ.IsCQ) :
    φ.IsUCQ := by
  cases φ with
  | top =>
      trivial
  | bot =>
      trivial
  | eq _ _ =>
      trivial
  | rel _ =>
      trivial
  | and _ _ =>
      exact h
  | or _ _ =>
      cases h
  | not _ =>
      cases h
  | imp _ _ =>
      cases h
  | iff _ _ =>
      cases h
  | forall_ _ _ =>
      cases h
  | exists_ _ _ =>
      exact h

end Formula

/- Relational-calculus formulas in the UCQ fragment. -/
abbrev UCQFormula
    {A : Type}
    {_ : RelationNames A}
    (D : Type)
    [Domain D]
    (Γ : UnnamedSchema A) : Type :=
  {φ : Formula D Γ // φ.IsUCQ}

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Cast a formula with a UCQ proof to a UCQ formula.
-/
def toUCQ
    (φ : Formula D Γ)
    (h : φ.IsUCQ) :
    UCQFormula D Γ :=
  ⟨φ, h⟩

end Formula

namespace CQFormula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  A CQ formula induces a UCQ formula with the same formula.
-/
def toUCQ
    (φ : CQFormula D Γ) :
    UCQFormula D Γ :=
  ⟨φ.1, Formula.IsCQ.toIsUCQ φ.2⟩

end CQFormula

namespace UCQFormula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  A UCQ formula is also an ordinary relational-calculus
  formula.
-/
def toFormula
    (φ : UCQFormula D Γ) :
    Formula D Γ :=
  φ.1

end UCQFormula

namespace Query

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}
variable {n : Nat}

/- A query is a UCQ when its formula is a UCQ. -/
def IsUCQ
    (q : Query D Γ n) : Prop :=
  q.form.IsUCQ

instance
    (q : Query D Γ n) :
    Decidable q.IsUCQ :=
  inferInstanceAs (Decidable q.form.IsUCQ)

end Query

end RelCalc
