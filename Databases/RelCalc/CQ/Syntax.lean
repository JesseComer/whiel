-- Author: Jesse Comer
import Databases.RelCalc.Syntax

/-
  This file specifies the conjunctive-query fragment of
  relational calculus.

  Key definitions include:
    * `RelCalc.Formula.IsConjunctive`
    * `RelCalc.Formula.IsCQ`
    * `RelCalc.CQFormula`

  Key theorems include:
    * `RelCalc.Formula.IsConjunctive.toIsCQ`
    * `RelCalc.Formula.IsCQ.existsMany`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Conjunctive Queries
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- A formula is a relation atom. -/
def IsRelAtom : Formula D Γ → Prop
| .rel _ => True
| _ => False

/- Relation-atom membership is decidable by cases. -/
def IsRelAtom.decidable :
    (φ : Formula D Γ) → Decidable (IsRelAtom φ)
| .rel _ => isTrue trivial
| .top => isFalse (fun h => h)
| .bot => isFalse (fun h => h)
| .eq _ _ => isFalse (fun h => h)
| .and _ _ => isFalse (fun h => h)
| .or _ _ => isFalse (fun h => h)
| .not _ => isFalse (fun h => h)
| .imp _ _ => isFalse (fun h => h)
| .iff _ _ => isFalse (fun h => h)
| .forall_ _ _ => isFalse (fun h => h)
| .exists_ _ _ => isFalse (fun h => h)

instance
    (φ : Formula D Γ) :
    Decidable φ.IsRelAtom :=
  IsRelAtom.decidable φ

/- A formula is a relation or equality atom. -/
def IsAtom : Formula D Γ → Prop
| .eq _ _ => True
| .rel _ => True
| _ => False

/- Atom membership is decidable by cases. -/
def IsAtom.decidable :
    (φ : Formula D Γ) → Decidable (IsAtom φ)
| .eq _ _ => isTrue trivial
| .rel _ => isTrue trivial
| .top => isFalse (fun h => h)
| .bot => isFalse (fun h => h)
| .and _ _ => isFalse (fun h => h)
| .or _ _ => isFalse (fun h => h)
| .not _ => isFalse (fun h => h)
| .imp _ _ => isFalse (fun h => h)
| .iff _ _ => isFalse (fun h => h)
| .forall_ _ _ => isFalse (fun h => h)
| .exists_ _ _ => isFalse (fun h => h)

instance
    (φ : Formula D Γ) :
    Decidable φ.IsAtom :=
  IsAtom.decidable φ

/-
  Equality-free conjunctive matrices are quantifier-free
  formulas built from truth, relation atoms, and
  conjunction.
-/
def IsRelConjunctive : Formula D Γ → Prop
| .top => True
| .rel _ => True
| .and φ ψ =>
    IsRelConjunctive φ ∧ IsRelConjunctive ψ
| .bot => False
| .eq _ _ => False
| .or _ _ => False
| .not _ => False
| .imp _ _ => False
| .iff _ _ => False
| .forall_ _ _ => False
| .exists_ _ _ => False

/-
  Equality-free conjunctive-matrix membership is decidable
  by structural recursion on formulas.
-/
def IsRelConjunctive.decidable :
    (φ : Formula D Γ) → Decidable (IsRelConjunctive φ)
| .top => isTrue trivial
| .rel _ => isTrue trivial
| .and φ ψ =>
    match IsRelConjunctive.decidable φ,
        IsRelConjunctive.decidable ψ with
    | isTrue hφ, isTrue hψ => isTrue ⟨hφ, hψ⟩
    | isFalse hφ, _ =>
        isFalse (fun h => hφ h.1)
    | _, isFalse hψ =>
        isFalse (fun h => hψ h.2)
| .bot => isFalse (fun h => h)
| .eq _ _ => isFalse (fun h => h)
| .or _ _ => isFalse (fun h => h)
| .not _ => isFalse (fun h => h)
| .imp _ _ => isFalse (fun h => h)
| .iff _ _ => isFalse (fun h => h)
| .forall_ _ _ => isFalse (fun h => h)
| .exists_ _ _ => isFalse (fun h => h)

instance
    (φ : Formula D Γ) :
    Decidable φ.IsRelConjunctive :=
  IsRelConjunctive.decidable φ

/-
  Equality-free conjunctive queries are formulas obtained
  from an equality-free conjunctive matrix by adding zero
  or more existential quantifiers as an outer prefix.
-/
def IsRelCQ : Formula D Γ → Prop
| .exists_ _ φ => IsRelCQ φ
| .top => True
| .rel _ => True
| .and φ ψ =>
    IsRelConjunctive φ ∧ IsRelConjunctive ψ
| .bot => False
| .eq _ _ => False
| .or _ _ => False
| .not _ => False
| .imp _ _ => False
| .iff _ _ => False
| .forall_ _ _ => False

/-
  Equality-free CQ membership is decidable by structural
  recursion on formulas.
-/
def IsRelCQ.decidable :
    (φ : Formula D Γ) → Decidable (IsRelCQ φ)
| .exists_ _ φ => IsRelCQ.decidable φ
| .top => isTrue trivial
| .rel _ => isTrue trivial
| .and φ ψ =>
    match IsRelConjunctive.decidable φ,
        IsRelConjunctive.decidable ψ with
    | isTrue hφ, isTrue hψ => isTrue ⟨hφ, hψ⟩
    | isFalse hφ, _ =>
        isFalse (fun h => hφ h.1)
    | _, isFalse hψ =>
        isFalse (fun h => hψ h.2)
| .bot => isFalse (fun h => h)
| .eq _ _ => isFalse (fun h => h)
| .or _ _ => isFalse (fun h => h)
| .not _ => isFalse (fun h => h)
| .imp _ _ => isFalse (fun h => h)
| .iff _ _ => isFalse (fun h => h)
| .forall_ _ _ => isFalse (fun h => h)

instance
    (φ : Formula D Γ) :
    Decidable φ.IsRelCQ :=
  IsRelCQ.decidable φ

/-
  Every equality-free conjunctive matrix is an
  equality-free CQ.
-/
theorem IsRelConjunctive.toIsRelCQ
    {φ : Formula D Γ}
    (h : φ.IsRelConjunctive) :
    φ.IsRelCQ := by
  cases φ with
  | top =>
      trivial
  | bot =>
      cases h
  | eq _ _ =>
      cases h
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
      cases h

/-
  Prefixing an equality-free CQ with one existential
  quantifier is an equality-free CQ.
-/
theorem IsRelCQ.exists_
    {φ : Formula D Γ}
    (x : Var)
    (h : φ.IsRelCQ) :
    (Formula.exists_ x φ).IsRelCQ := by
  simpa [IsRelCQ] using h

/-
  Prefixing an equality-free CQ with finitely many
  existential quantifiers is an equality-free CQ.
-/
theorem IsRelCQ.existsMany
    {φ : Formula D Γ}
    (xs : List Var)
    (h : φ.IsRelCQ) :
    (Formula.existsMany xs φ).IsRelCQ := by
  induction xs with
  | nil =>
      simpa [Formula.existsMany] using h
  | cons x xs ih =>
      simpa [Formula.existsMany] using
        IsRelCQ.exists_ x ih

/- Variables occurring in relation atoms of a formula. -/
def relVars : Formula D Γ → Finset Var
| .top => ∅
| .bot => ∅
| .eq _ _ => ∅
| .rel a => RelTerm.tupleVars a.args
| .and φ ψ => relVars φ ∪ relVars ψ
| .or φ ψ => relVars φ ∪ relVars ψ
| .not φ => relVars φ
| .imp φ ψ => relVars φ ∪ relVars ψ
| .iff φ ψ => relVars φ ∪ relVars ψ
| .forall_ _ φ => relVars φ
| .exists_ _ φ => relVars φ

/-
  Range-restriction for equality-free CQs. An existential
  binder is safe when the bound variable appears in a
  relation atom in its scope.
-/
def IsRelSafe : Formula D Γ → Prop
| .top => True
| .bot => True
| .eq _ _ => True
| .rel _ => True
| .and φ ψ => IsRelSafe φ ∧ IsRelSafe ψ
| .or φ ψ => IsRelSafe φ ∧ IsRelSafe ψ
| .not φ => IsRelSafe φ
| .imp φ ψ => IsRelSafe φ ∧ IsRelSafe ψ
| .iff φ ψ => IsRelSafe φ ∧ IsRelSafe ψ
| .forall_ _ φ => IsRelSafe φ
| .exists_ x φ => x ∈ φ.relVars ∧ IsRelSafe φ

/-
  Range-restriction membership is decidable by structural
  recursion on formulas.
-/
def IsRelSafe.decidable :
    (φ : Formula D Γ) → Decidable (IsRelSafe φ)
| .top => isTrue trivial
| .bot => isTrue trivial
| .eq _ _ => isTrue trivial
| .rel _ => isTrue trivial
| .and φ ψ =>
    match IsRelSafe.decidable φ,
        IsRelSafe.decidable ψ with
    | isTrue hφ, isTrue hψ => isTrue ⟨hφ, hψ⟩
    | isFalse hφ, _ =>
        isFalse (fun h => hφ h.1)
    | _, isFalse hψ =>
        isFalse (fun h => hψ h.2)
| .or φ ψ =>
    match IsRelSafe.decidable φ,
        IsRelSafe.decidable ψ with
    | isTrue hφ, isTrue hψ => isTrue ⟨hφ, hψ⟩
    | isFalse hφ, _ =>
        isFalse (fun h => hφ h.1)
    | _, isFalse hψ =>
        isFalse (fun h => hψ h.2)
| .not φ => IsRelSafe.decidable φ
| .imp φ ψ =>
    match IsRelSafe.decidable φ,
        IsRelSafe.decidable ψ with
    | isTrue hφ, isTrue hψ => isTrue ⟨hφ, hψ⟩
    | isFalse hφ, _ =>
        isFalse (fun h => hφ h.1)
    | _, isFalse hψ =>
        isFalse (fun h => hψ h.2)
| .iff φ ψ =>
    match IsRelSafe.decidable φ,
        IsRelSafe.decidable ψ with
    | isTrue hφ, isTrue hψ => isTrue ⟨hφ, hψ⟩
    | isFalse hφ, _ =>
        isFalse (fun h => hφ h.1)
    | _, isFalse hψ =>
        isFalse (fun h => hψ h.2)
| .forall_ _ φ => IsRelSafe.decidable φ
| .exists_ x φ =>
    match inferInstanceAs (Decidable (x ∈ φ.relVars)),
        IsRelSafe.decidable φ with
    | isTrue hx, isTrue hφ => isTrue ⟨hx, hφ⟩
    | isFalse hx, _ =>
        isFalse (fun h => hx h.1)
    | _, isFalse hφ =>
        isFalse (fun h => hφ h.2)

instance
    (φ : Formula D Γ) :
    Decidable φ.IsRelSafe :=
  IsRelSafe.decidable φ

/-
  The safe equality-free CQ fragment: structural
  equality-free CQ syntax plus range restriction.
-/
def IsSafeRelCQ
    (φ : Formula D Γ) : Prop :=
  φ.IsRelCQ ∧ φ.IsRelSafe

instance
    (φ : Formula D Γ) :
    Decidable φ.IsSafeRelCQ := by
  unfold IsSafeRelCQ
  infer_instance

/- A safe equality-free CQ is structurally equality-free. -/
theorem IsSafeRelCQ.isRelCQ
    {φ : Formula D Γ}
    (h : φ.IsSafeRelCQ) :
    φ.IsRelCQ :=
  h.1

/- A safe equality-free CQ is range-restricted. -/
theorem IsSafeRelCQ.isRelSafe
    {φ : Formula D Γ}
    (h : φ.IsSafeRelCQ) :
    φ.IsRelSafe :=
  h.2

/-
  Conjunctive matrices are quantifier-free formulas built
  from truth, falsity, equality atoms, relation atoms, and
  conjunction.
-/
def IsConjunctive : Formula D Γ → Prop
| .top => True
| .bot => True
| .eq _ _ => True
| .rel _ => True
| .and φ ψ => IsConjunctive φ ∧ IsConjunctive ψ
| .or _ _ => False
| .not _ => False
| .imp _ _ => False
| .iff _ _ => False
| .forall_ _ _ => False
| .exists_ _ _ => False

/-
  Conjunctive-matrix membership is decidable by structural
  recursion on formulas.
-/
def IsConjunctive.decidable :
    (φ : Formula D Γ) → Decidable (IsConjunctive φ)
| .top => isTrue trivial
| .bot => isTrue trivial
| .eq _ _ => isTrue trivial
| .rel _ => isTrue trivial
| .and φ ψ =>
    match IsConjunctive.decidable φ,
        IsConjunctive.decidable ψ with
    | isTrue hφ, isTrue hψ => isTrue ⟨hφ, hψ⟩
    | isFalse hφ, _ =>
        isFalse (fun h => hφ h.1)
    | _, isFalse hψ =>
        isFalse (fun h => hψ h.2)
| .or _ _ => isFalse (fun h => h)
| .not _ => isFalse (fun h => h)
| .imp _ _ => isFalse (fun h => h)
| .iff _ _ => isFalse (fun h => h)
| .forall_ _ _ => isFalse (fun h => h)
| .exists_ _ _ => isFalse (fun h => h)

instance
    (φ : Formula D Γ) :
    Decidable φ.IsConjunctive :=
  IsConjunctive.decidable φ

/-
  Conjunctive queries are formulas obtained from a
  conjunctive matrix by adding zero or more existential
  quantifiers as an outer prefix.
-/
def IsCQ : Formula D Γ → Prop
| .exists_ _ φ => IsCQ φ
| .top => True
| .bot => True
| .eq _ _ => True
| .rel _ => True
| .and φ ψ => IsConjunctive φ ∧ IsConjunctive ψ
| .or _ _ => False
| .not _ => False
| .imp _ _ => False
| .iff _ _ => False
| .forall_ _ _ => False

/-
  CQ membership is decidable by structural recursion on
  formulas.
-/
def IsCQ.decidable :
    (φ : Formula D Γ) → Decidable (IsCQ φ)
| .exists_ _ φ => IsCQ.decidable φ
| .top => isTrue trivial
| .bot => isTrue trivial
| .eq _ _ => isTrue trivial
| .rel _ => isTrue trivial
| .and φ ψ =>
    match IsConjunctive.decidable φ,
        IsConjunctive.decidable ψ with
    | isTrue hφ, isTrue hψ => isTrue ⟨hφ, hψ⟩
    | isFalse hφ, _ =>
        isFalse (fun h => hφ h.1)
    | _, isFalse hψ =>
        isFalse (fun h => hψ h.2)
| .or _ _ => isFalse (fun h => h)
| .not _ => isFalse (fun h => h)
| .imp _ _ => isFalse (fun h => h)
| .iff _ _ => isFalse (fun h => h)
| .forall_ _ _ => isFalse (fun h => h)

instance
    (φ : Formula D Γ) :
    Decidable φ.IsCQ :=
  IsCQ.decidable φ

/- Every conjunctive matrix is a CQ. -/
theorem IsConjunctive.toIsCQ
    {φ : Formula D Γ}
    (h : φ.IsConjunctive) :
    φ.IsCQ := by
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
      cases h

/-
  Prefixing a CQ with one existential quantifier is a CQ.
-/
theorem IsCQ.exists_
    {φ : Formula D Γ}
    (x : Var)
    (h : φ.IsCQ) :
    (Formula.exists_ x φ).IsCQ := by
  simpa [IsCQ] using h

/-
  Prefixing a CQ with finitely many existential quantifiers
  is a CQ.
-/
theorem IsCQ.existsMany
    {φ : Formula D Γ}
    (xs : List Var)
    (h : φ.IsCQ) :
    (Formula.existsMany xs φ).IsCQ := by
  induction xs with
  | nil =>
      simpa [Formula.existsMany] using h
  | cons x xs ih =>
      simpa [Formula.existsMany] using
        IsCQ.exists_ x ih

end Formula

/- Relational-calculus formulas in the CQ fragment. -/
abbrev CQFormula
    {A : Type}
    {_ : RelationNames A}
    (D : Type)
    [Domain D]
    (Γ : UnnamedSchema A) : Type :=
  {φ : Formula D Γ // φ.IsCQ}

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Cast a formula with a CQ proof to a CQ formula. -/
def toCQ
    (φ : Formula D Γ)
    (h : φ.IsCQ) :
    CQFormula D Γ :=
  ⟨φ, h⟩

end Formula

namespace CQFormula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  A CQ formula is also an ordinary relational-calculus
  formula.
-/
def toFormula
    (φ : CQFormula D Γ) :
    Formula D Γ :=
  φ.1

end CQFormula

namespace Query

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}
variable {n : Nat}

/- A query is a CQ when its formula is a CQ. -/
def IsCQ
    (q : Query D Γ n) : Prop :=
  q.form.IsCQ

instance
    (q : Query D Γ n) :
    Decidable q.IsCQ :=
  inferInstanceAs (Decidable q.form.IsCQ)

/-
  A query is equality-free conjunctive when its formula
  is.
-/
def IsRelCQ
    (q : Query D Γ n) : Prop :=
  q.form.IsRelCQ

instance
    (q : Query D Γ n) :
    Decidable q.IsRelCQ :=
  inferInstanceAs (Decidable q.form.IsRelCQ)

/-
  A query is a safe equality-free CQ when its formula is
  structural equality-free CQ syntax and range-restricted.
-/
def IsSafeRelCQ
    (q : Query D Γ n) : Prop :=
  q.form.IsSafeRelCQ

instance
    (q : Query D Γ n) :
    Decidable q.IsSafeRelCQ :=
  inferInstanceAs (Decidable q.form.IsSafeRelCQ)

/-
  A safe equality-free CQ query is structurally
  equality-free.
-/
theorem IsSafeRelCQ.isRelCQ
    {q : Query D Γ n}
    (h : q.IsSafeRelCQ) :
    q.IsRelCQ :=
  h.1

/- A safe equality-free CQ query is range-restricted. -/
theorem IsSafeRelCQ.isRelSafe
    {q : Query D Γ n}
    (h : q.IsSafeRelCQ) :
    q.form.IsRelSafe :=
  h.2

end Query

end RelCalc
