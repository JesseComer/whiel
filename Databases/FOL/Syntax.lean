-- Author: Jesse Comer
import Databases.Core.Signature

/-
  First-order logic syntax.

  Key declarations:
    * `FOL.Term`
    * `FOL.Formula`
    * `FOL.Sentence`

  Term and atom arities are enforced by construction.
-/

------------------------------------------------------------
-- First-Order Logic Syntax
------------------------------------------------------------

namespace FOL

mutual

/-
  Terms over a signature. Nullary function symbols are
  constants.
-/
  inductive Term
      {A F : Type}
      [RelationNames A]
      [FunctionNames F]
      (Sig : Signature A F) : Type where
    | var : Var → Term Sig
    | func : (f : Signature.Fun Sig) →
        TermList Sig (Sig.funArity f) → Term Sig

/-
  Length-indexed term lists. This avoids Lean's nested
  inductive restrictions while keeping arities explicit.
-/
  inductive TermList
      {A F : Type}
      [RelationNames A]
      [FunctionNames F]
      (Sig : Signature A F) : Nat → Type where
    | nil : TermList Sig 0
    | cons : Term Sig → TermList Sig n →
        TermList Sig (n + 1)

end

namespace TermList

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Sig : Signature A F}

/- Convert an indexed term list to an ordinary list. -/
def toList :
    {n : Nat} → TermList Sig n → List (Term Sig)
| _, .nil => []
| _, .cons t ts => t :: toList ts

/-
  Build an indexed term list from an ordinary list.
-/
def ofList :
    (ts : List (Term Sig)) → TermList Sig ts.length
| [] => .nil
| t :: ts => .cons t (ofList ts)

/- Build an indexed term list from a finite function. -/
def ofFn :
    {n : Nat} → (Fin n → Term Sig) → TermList Sig n
| 0, _ => .nil
| n + 1, f =>
    .cons
      (f ⟨0, Nat.zero_lt_succ n⟩)
      (ofFn
        (fun i : Fin n =>
          f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

/- Build an indexed term list from a vector. -/
def ofVector
    {n : Nat}
    (ts : Vector (Term Sig) n) :
    TermList Sig n :=
  ofFn (fun i => ts.get i)

/- Get the term at a valid coordinate. -/
def get :
    {n : Nat} → TermList Sig n → Fin n → Term Sig
| 0, .nil, i => nomatch i
| _ + 1, .cons t ts, i =>
    Fin.cases t (fun j => get ts j) i

@[simp] theorem toList_nil :
    toList (Sig := Sig) .nil = [] := rfl

@[simp] theorem toList_cons
    {n : Nat}
    (t : Term Sig)
    (ts : TermList Sig n) :
    toList (.cons t ts) = t :: toList ts := rfl

@[simp] theorem length_toList :
    {n : Nat} →
      (ts : TermList Sig n) → ts.toList.length = n
| _, .nil => by
    simp [toList]
| _, .cons _ ts => by
    simp [toList, length_toList ts]

end TermList

mutual
/- Free variables in a term. -/
  def Term.freeVars
      {A F : Type}
      [RelationNames A]
      [FunctionNames F]
      {Sig : Signature A F} :
      Term Sig → Finset Var
  | .var x => {x}
  | .func _ ts => TermList.freeVars ts

/- Free variables in an indexed term list. -/
  def TermList.freeVars
      {A F : Type}
      [RelationNames A]
      [FunctionNames F]
      {Sig : Signature A F} :
      {n : Nat} → TermList Sig n → Finset Var
  | _, .nil => ∅
  | _, .cons t ts => t.freeVars ∪ TermList.freeVars ts
end

namespace TermList

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Sig : Signature A F}

/-
  Free variables of a function-built term list come from
  one generated term.
-/
theorem mem_freeVars_ofFn
    {n : Nat}
    (f : Fin n → Term Sig)
    {y : Var} :
    y ∈ (TermList.ofFn f).freeVars →
      ∃ i : Fin n, y ∈ (f i).freeVars := by
  induction n with
  | zero =>
      simp [TermList.ofFn, TermList.freeVars]
  | succ n ih =>
      intro h
      change y ∈
          (f ⟨0, Nat.zero_lt_succ n⟩).freeVars ∪
            (TermList.ofFn
              (fun i : Fin n =>
                f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)).freeVars at h
      rw [Finset.mem_union] at h
      cases h with
      | inl hHead =>
          exact ⟨⟨0, Nat.zero_lt_succ n⟩, hHead⟩
      | inr hTail =>
          rcases ih
              (fun i : Fin n =>
                f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
              hTail with
            ⟨i, hi⟩
          exact ⟨⟨i.1 + 1, Nat.succ_lt_succ i.2⟩,
            hi⟩

end TermList

/- First-order formulas over a fixed signature. -/
inductive Formula
    {A F : Type}
    [RelationNames A]
    [FunctionNames F]
    (Sig : Signature A F) : Type where
  | top : Formula Sig
  | bot : Formula Sig
  | eq : Term Sig → Term Sig → Formula Sig
  | rel : (X : Signature.Rel Sig) →
      TermList Sig (Sig.arity X) → Formula Sig
  | and : Formula Sig → Formula Sig → Formula Sig
  | or : Formula Sig → Formula Sig → Formula Sig
  | not : Formula Sig → Formula Sig
  | imp : Formula Sig → Formula Sig → Formula Sig
  | iff : Formula Sig → Formula Sig → Formula Sig
  | forall_ : Var → Formula Sig → Formula Sig
  | exists_ : Var → Formula Sig → Formula Sig

namespace Formula

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Sig : Signature A F}

/- Existentially quantify a list of variables. -/
def existsMany
    (xs : List Var)
    (φ : Formula Sig) :
    Formula Sig :=
  xs.foldr Formula.exists_ φ

/- Disjoin a finite list of formulas. -/
def disjoin : List (Formula Sig) → Formula Sig
| [] => .bot
| φ :: φs => .or φ (disjoin φs)

/- Free variables in a formula. -/
def freeVars : Formula Sig → Finset Var
| .top => ∅
| .bot => ∅
| .eq t₁ t₂ => t₁.freeVars ∪ t₂.freeVars
| .rel _ ts => ts.freeVars
| .and φ ψ => freeVars φ ∪ freeVars ψ
| .or φ ψ => freeVars φ ∪ freeVars ψ
| .not φ => freeVars φ
| .imp φ ψ => freeVars φ ∪ freeVars ψ
| .iff φ ψ => freeVars φ ∪ freeVars ψ
| .forall_ x φ => (freeVars φ).erase x
| .exists_ x φ => (freeVars φ).erase x

/-
  Free variables after existentially closing a variable
  list.
-/
theorem mem_freeVars_existsMany_iff
    (xs : List Var)
    (φ : Formula Sig)
    (y : Var) :
    y ∈ (existsMany xs φ).freeVars ↔
      y ∈ φ.freeVars ∧ y ∉ xs := by
  induction xs with
  | nil =>
      simp [existsMany]
  | cons x xs ih =>
      change y ∈
          (Formula.exists_ x (existsMany xs φ)).freeVars ↔
        y ∈ φ.freeVars ∧ y ∉ x :: xs
      rw [Formula.freeVars]
      simp only [Finset.mem_erase, List.mem_cons, not_or]
      rw [ih]
      constructor
      · intro h
        exact ⟨h.2.1, h.1, h.2.2⟩
      · intro h
        exact ⟨h.2.1, h.1, h.2.2⟩

/-
  A finite disjunction has only variables allowed by each
  disjunct.
-/
theorem freeVars_disjoin_subset
    (φs : List (Formula Sig))
    (S : Finset Var)
    (hφs : ∀ φ ∈ φs, φ.freeVars ⊆ S) :
    (disjoin φs).freeVars ⊆ S := by
  induction φs with
  | nil =>
      intro y hy
      change y ∈ (∅ : Finset Var) at hy
      exact False.elim (Finset.notMem_empty y hy)
  | cons φ φs ih =>
      intro y hy
      change y ∈ φ.freeVars ∪
          (disjoin φs).freeVars at hy
      rw [Finset.mem_union] at hy
      cases hy with
      | inl h =>
          exact hφs φ (by simp) h
      | inr h =>
          exact ih
            (fun ψ hψ => hφs ψ (by simp [hψ]))
            h

end Formula

end FOL

------------------------------------------------------------
-- First-Order Sentences
------------------------------------------------------------

namespace FOL

namespace Formula

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Sig : Signature A F}

/- A formula is a sentence when it has no free variables. -/
def IsSentence
    (φ : Formula Sig) : Prop :=
  φ.freeVars = ∅

instance
    (φ : Formula Sig) :
    Decidable φ.IsSentence := by
  unfold IsSentence
  infer_instance

end Formula

/-
  First-order sentences are the closed-formula fragment.
-/
abbrev Sentence
    {A F : Type}
    [RelationNames A]
    [FunctionNames F]
    (Sig : Signature A F) : Type :=
  {φ : Formula Sig // φ.IsSentence}

namespace Formula

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Sig : Signature A F}

/- Package a closed formula as a sentence. -/
def toSentence
    (φ : Formula Sig)
    (h : φ.IsSentence) :
    FOL.Sentence Sig :=
  ⟨φ, h⟩

end Formula

end FOL
