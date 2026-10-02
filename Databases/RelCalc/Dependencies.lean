-- Author: Jesse Comer
import Databases.RelCalc.Syntax
import Mathlib.Data.Finset.Powerset

/-
  This file specifies strict database-dependency syntax for
  relational calculus formulas.

  Key definitions include:
    * `RelCalc.Formula.IsTGD`
    * `RelCalc.Formula.IsEGD`
    * `RelCalc.Dependency.FDSpec`
    * `RelCalc.Formula.IsFD`
    * `RelCalc.Formula.IsSuperkeyFor`
    * `RelCalc.Formula.IsCandidateKeyFor`

  The declarations here are syntax-only recognizers. They
  do not define dependency satisfaction or implication.
-/

------------------------------------------------------------
-- Formula Variable Helpers
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- A relation atom whose arguments are all variables. -/
def IsRelVarAtom : Formula D Γ → Prop
| .rel a => ∀ i, (a.args.get i).IsVar
| _ => False

/- Relation-variable atoms are decidable. -/
def IsRelVarAtom.decidable :
    (φ : Formula D Γ) → Decidable φ.IsRelVarAtom
| .rel a => by
    change Decidable (∀ i, (a.args.get i).IsVar)
    exact inferInstance
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
    Decidable φ.IsRelVarAtom :=
  IsRelVarAtom.decidable φ

/-
  A nonempty conjunction of relation atoms whose arguments
  are all variables.
-/
def IsRelVarConj : Formula D Γ → Prop
| .rel a => ∀ i, (a.args.get i).IsVar
| .and φ ψ => φ.IsRelVarConj ∧ ψ.IsRelVarConj
| _ => False

/-
  Relation-variable conjunction membership is decidable by
  structural recursion.
-/
def IsRelVarConj.decidable :
    (φ : Formula D Γ) → Decidable φ.IsRelVarConj
| .rel a => by
    change Decidable (∀ i, (a.args.get i).IsVar)
    exact inferInstance
| .and φ ψ => by
    haveI : Decidable φ.IsRelVarConj :=
      IsRelVarConj.decidable φ
    haveI : Decidable ψ.IsRelVarConj :=
      IsRelVarConj.decidable ψ
    change Decidable
      (φ.IsRelVarConj ∧ ψ.IsRelVarConj)
    exact inferInstance
| .top => isFalse (fun h => h)
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
    Decidable φ.IsRelVarConj :=
  IsRelVarConj.decidable φ

end Formula

end RelCalc

------------------------------------------------------------
-- Quantifier Prefixes
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Strip the outer universal-quantifier prefix. -/
def stripForalls :
    Formula D Γ → List Var × Formula D Γ
| .forall_ x φ =>
    let r := stripForalls φ
    (x :: r.1, r.2)
| φ => ([], φ)

/- Strip the outer existential-quantifier prefix. -/
def stripExists :
    Formula D Γ → List Var × Formula D Γ
| .exists_ x φ =>
    let r := stripExists φ
    (x :: r.1, r.2)
| φ => ([], φ)

/- `stripForalls` sees all quantifiers from `forallMany`. -/
theorem stripForalls_forallMany
    (xs : List Var)
    (φ : Formula D Γ) :
    stripForalls (forallMany xs φ) =
      (xs ++ (stripForalls φ).1,
        (stripForalls φ).2) := by
  induction xs with
  | nil =>
      change stripForalls φ =
        (([] : List Var) ++ (stripForalls φ).1,
          (stripForalls φ).2)
      cases stripForalls φ
      rfl
  | cons x xs ih =>
      change
        (let r := stripForalls (forallMany xs φ);
          (x :: r.1, r.2)) =
          (x :: (xs ++ (stripForalls φ).1),
            (stripForalls φ).2)
      rw [ih]

/- `stripExists` sees all quantifiers from `existsMany`. -/
theorem stripExists_existsMany
    (xs : List Var)
    (φ : Formula D Γ) :
    stripExists (existsMany xs φ) =
      (xs ++ (stripExists φ).1,
        (stripExists φ).2) := by
  induction xs with
  | nil =>
      change stripExists φ =
        (([] : List Var) ++ (stripExists φ).1,
          (stripExists φ).2)
      cases stripExists φ
      rfl
  | cons x xs ih =>
      change
        (let r := stripExists (existsMany xs φ);
          (x :: r.1, r.2)) =
          (x :: (xs ++ (stripExists φ).1),
            (stripExists φ).2)
      rw [ih]

end Formula

end RelCalc

------------------------------------------------------------
-- Tuple-Generating Dependencies
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Boolean recognizer for TGD syntax. -/
def isTGD
    (φ : Formula D Γ) : Bool :=
  let r := stripForalls φ
  match r.2 with
  | .imp body rhs =>
      let e := stripExists rhs
      decide
        (r.1.Nodup ∧
        e.1.Nodup ∧
        r.1.toFinset ∩ e.1.toFinset = ∅ ∧
        body.IsRelVarConj ∧
        e.2.IsRelVarConj ∧
        body.allVars = r.1.toFinset ∧
        e.2.allVars ⊆ r.1.toFinset ∪ e.1.toFinset ∧
        e.1.toFinset ⊆ e.2.allVars)
  | _ => false

/-
  `IsTGD φ` recognizes formulas of the form
  `∀ x̄ ȳ. body(x̄, ȳ) → ∃ z̄. head(x̄, z̄)`.
-/
def IsTGD
    (φ : Formula D Γ) : Prop :=
  φ.isTGD = true

/- TGD syntax recognition is decidable. -/
def IsTGD.decidable
    (φ : Formula D Γ) :
    Decidable φ.IsTGD := by
  unfold IsTGD
  infer_instance

instance
    (φ : Formula D Γ) :
    Decidable φ.IsTGD :=
  IsTGD.decidable φ

end Formula

end RelCalc

------------------------------------------------------------
-- Equality-Generating Dependencies
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Boolean recognizer for EGD syntax. -/
def isEGD
    (φ : Formula D Γ) : Bool :=
  let r := stripForalls φ
  match r.2 with
  | .imp body (.eq (.var u) (.var v)) =>
      decide
        (r.1.Nodup ∧
        body.IsRelVarConj ∧
        body.allVars = r.1.toFinset ∧
        u ∈ body.allVars ∧
        v ∈ body.allVars)
  | _ => false

/-
  `IsEGD φ` recognizes formulas of the form
  `∀ x̄. body(x̄) → u = v`.
-/
def IsEGD
    (φ : Formula D Γ) : Prop :=
  φ.isEGD = true

/- EGD syntax recognition is decidable. -/
def IsEGD.decidable
    (φ : Formula D Γ) :
    Decidable φ.IsEGD := by
  unfold IsEGD
  infer_instance

instance
    (φ : Formula D Γ) :
    Decidable φ.IsEGD :=
  IsEGD.decidable φ

end Formula

end RelCalc

------------------------------------------------------------
-- Certified Dependencies
------------------------------------------------------------

namespace RelCalc

/- A relational-calculus formula certified as a TGD. -/
abbrev TGD
    {A : Type}
    {_ : RelationNames A}
    (D : Type)
    [Domain D]
    (Γ : UnnamedSchema A) : Type :=
  { φ : Formula D Γ // φ.IsTGD }

/- A relational-calculus formula certified as an EGD. -/
abbrev EGD
    {A : Type}
    {_ : RelationNames A}
    (D : Type)
    [Domain D]
    (Γ : UnnamedSchema A) : Type :=
  { φ : Formula D Γ // φ.IsEGD }

end RelCalc

------------------------------------------------------------
-- Functional Dependencies
------------------------------------------------------------

namespace RelCalc

namespace Dependency

/-
  A functional-dependency specification over one checked
  relation symbol.
-/
structure FDSpec
    {A : Type}
    [RelationNames A]
    (Γ : UnnamedSchema A) where
  rel : Γ.syms
  lhs : Finset (Fin (Γ.arity rel))
  rhs : Fin (Γ.arity rel)

namespace FDSpec

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- The left tuple variable at coordinate `i`. -/
def leftVar
    (fd : FDSpec Γ)
    (i : Fin (Γ.arity fd.rel)) : Var :=
  i.1

/- The right tuple variable at coordinate `i`. -/
def rightVar
    (fd : FDSpec Γ)
    (i : Fin (Γ.arity fd.rel)) : Var :=
  if i ∈ fd.lhs then
    fd.leftVar i
  else
    Γ.arity fd.rel + i.1

/- Variables used by the left tuple. -/
def leftVarSet
    (fd : FDSpec Γ) : Finset Var :=
  (Finset.univ : Finset (Fin (Γ.arity fd.rel))).image
    (fun i => fd.leftVar i)

/- Variables used by the right tuple. -/
def rightVarSet
    (fd : FDSpec Γ) : Finset Var :=
  (Finset.univ : Finset (Fin (Γ.arity fd.rel))).image
    (fun i => fd.rightVar i)

/- All variables used by the normalized FD formula. -/
def varSet
    (fd : FDSpec Γ) : Finset Var :=
  fd.leftVarSet ∪ fd.rightVarSet

/-
  Optional fresh right-side variable at a raw
  coordinate.
-/
def rightFreshVar?
    (fd : FDSpec Γ)
    (k : Nat) : Option Var :=
  if h : k < Γ.arity fd.rel then
    let i : Fin (Γ.arity fd.rel) := ⟨k, h⟩
    if i ∈ fd.lhs then
      none
    else
      some (Γ.arity fd.rel + k)
  else
    none

/- Fresh right-side variables not shared by `lhs`. -/
def rightFreshVarList
    (fd : FDSpec Γ) : List Var :=
  (List.range (Γ.arity fd.rel)).filterMap
    fd.rightFreshVar?

/- A computable prefix for the normalized FD formula. -/
def varList
    (fd : FDSpec Γ) : List Var :=
  List.range (Γ.arity fd.rel) ++ fd.rightFreshVarList

/- The left relation-atom tuple. -/
def leftTuple
    (fd : FDSpec Γ) :
    Vector (RelTerm D) (Γ.arity fd.rel) :=
  Vector.ofFn (fun i => .var (fd.leftVar i))

/- The right relation-atom tuple. -/
def rightTuple
    (fd : FDSpec Γ) :
    Vector (RelTerm D) (Γ.arity fd.rel) :=
  Vector.ofFn (fun i => .var (fd.rightVar i))

/- The left relation atom in the normalized FD formula. -/
def leftAtom
    (fd : FDSpec Γ) : Formula D Γ :=
  .rel { rel := fd.rel, args := fd.leftTuple }

/- The right relation atom in the normalized FD formula. -/
def rightAtom
    (fd : FDSpec Γ) : Formula D Γ :=
  .rel { rel := fd.rel, args := fd.rightTuple }

/- The FD antecedent relation conjunction. -/
def body
    (fd : FDSpec Γ) : Formula D Γ :=
  .and fd.leftAtom fd.rightAtom

/- The FD equality consequent. -/
def eqHead
    (fd : FDSpec Γ) : Formula D Γ :=
  .eq (.var (fd.leftVar fd.rhs))
    (.var (fd.rightVar fd.rhs))

/- The quantifier-free normalized FD matrix. -/
def matrix
    (fd : FDSpec Γ) : Formula D Γ :=
  .imp fd.body fd.eqHead

/- The normalized RelCalc formula for this FD. -/
def toFormula
    (fd : FDSpec Γ) : Formula D Γ :=
  Formula.forallMany fd.varList fd.matrix

/- Erase a tuple's arity into a sigma type. -/
def tupleSigma
    {n : Nat}
    (ts : Vector (RelTerm D) n) :
    Sigma (fun n => Vector (RelTerm D) n) :=
  ⟨n, ts⟩

/-
  A formula is a particular relation atom, up to
  proof-irrelevant schema-membership evidence.
-/
def IsAtom
    (fd : FDSpec Γ)
    (ts₀ : Vector (RelTerm D) (Γ.arity fd.rel)) :
    Formula D Γ → Prop
| .rel a =>
    a.rel.1 = fd.rel.1 ∧
      tupleSigma a.args = tupleSigma ts₀
| _ => False

/- Expected-atom recognition is decidable. -/
def IsAtom.decidable
    (fd : FDSpec Γ)
    (ts₀ : Vector (RelTerm D) (Γ.arity fd.rel)) :
    (φ : Formula D Γ) →
      Decidable (fd.IsAtom ts₀ φ)
| .rel a => by
    change Decidable
      (a.rel.1 = fd.rel.1 ∧
        tupleSigma a.args = tupleSigma ts₀)
    exact inferInstance
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
    (fd : FDSpec Γ)
    (ts₀ : Vector (RelTerm D) (Γ.arity fd.rel))
    (φ : Formula D Γ) :
    Decidable (fd.IsAtom ts₀ φ) :=
  IsAtom.decidable fd ts₀ φ

/-
  A formula is the normalized two-atom FD antecedent for
  `fd`.
-/
def IsBody
    (fd : FDSpec Γ) :
    Formula D Γ → Prop
| .and φ ψ =>
    fd.IsAtom fd.leftTuple φ ∧
      fd.IsAtom fd.rightTuple ψ
| _ => False

/- Expected-body recognition is decidable. -/
def IsBody.decidable
    (fd : FDSpec Γ) :
    (φ : Formula D Γ) →
      Decidable (fd.IsBody φ)
| .and φ ψ => by
    haveI : Decidable (fd.IsAtom fd.leftTuple φ) :=
      inferInstance
    haveI : Decidable (fd.IsAtom fd.rightTuple ψ) :=
      inferInstance
    change Decidable
      (fd.IsAtom fd.leftTuple φ ∧
        fd.IsAtom fd.rightTuple ψ)
    exact inferInstance
| .top => isFalse (fun h => h)
| .bot => isFalse (fun h => h)
| .eq _ _ => isFalse (fun h => h)
| .rel _ => isFalse (fun h => h)
| .or _ _ => isFalse (fun h => h)
| .not _ => isFalse (fun h => h)
| .imp _ _ => isFalse (fun h => h)
| .iff _ _ => isFalse (fun h => h)
| .forall_ _ _ => isFalse (fun h => h)
| .exists_ _ _ => isFalse (fun h => h)

instance
    (fd : FDSpec Γ)
    (φ : Formula D Γ) :
    Decidable (fd.IsBody φ) :=
  IsBody.decidable fd φ

/-
  A formula is the normalized equality consequent for
  `fd`.
-/
def IsHead
    (fd : FDSpec Γ) :
    Formula D Γ → Prop
| .eq (.var u) (.var v) =>
    u = fd.leftVar fd.rhs ∧
      v = fd.rightVar fd.rhs
| _ => False

/- Expected-head recognition is decidable. -/
def IsHead.decidable
    (fd : FDSpec Γ) :
    (φ : Formula D Γ) →
      Decidable (fd.IsHead φ)
| .eq (.var u) (.var v) => by
    change Decidable
      (u = fd.leftVar fd.rhs ∧
        v = fd.rightVar fd.rhs)
    exact inferInstance
| .eq (.var _) (.const _) => isFalse (fun h => h)
| .eq (.const _) _ => isFalse (fun h => h)
| .top => isFalse (fun h => h)
| .bot => isFalse (fun h => h)
| .rel _ => isFalse (fun h => h)
| .and _ _ => isFalse (fun h => h)
| .or _ _ => isFalse (fun h => h)
| .not _ => isFalse (fun h => h)
| .imp _ _ => isFalse (fun h => h)
| .iff _ _ => isFalse (fun h => h)
| .forall_ _ _ => isFalse (fun h => h)
| .exists_ _ _ => isFalse (fun h => h)

instance
    (fd : FDSpec Γ)
    (φ : Formula D Γ) :
    Decidable (fd.IsHead φ) :=
  IsHead.decidable fd φ

/-
  A formula matrix is exactly the normalized FD matrix for
  `fd`.
-/
def IsMatrix
    (fd : FDSpec Γ) :
    Formula D Γ → Prop
| .imp body head =>
    fd.IsBody body ∧ fd.IsHead head
| _ => False

/- Normalized formula representation of an FD spec. -/
def IsRepresentedBy
    (fd : FDSpec Γ)
    (φ : Formula D Γ) : Prop :=
  let r := Formula.stripForalls φ
  r.1 = fd.varList ∧
    fd.IsMatrix r.2

/- Matrix recognition for an FD spec is decidable. -/
def IsMatrix.decidable
    (fd : FDSpec Γ) :
    (φ : Formula D Γ) →
      Decidable (fd.IsMatrix φ)
| .imp body head => by
    haveI : Decidable (fd.IsBody body) :=
      inferInstance
    haveI : Decidable (fd.IsHead head) :=
      inferInstance
    change Decidable (fd.IsBody body ∧ fd.IsHead head)
    exact inferInstance
| .top => isFalse (fun h => h)
| .bot => isFalse (fun h => h)
| .eq _ _ => isFalse (fun h => h)
| .rel _ => isFalse (fun h => h)
| .and _ _ => isFalse (fun h => h)
| .or _ _ => isFalse (fun h => h)
| .not _ => isFalse (fun h => h)
| .iff _ _ => isFalse (fun h => h)
| .forall_ _ _ => isFalse (fun h => h)
| .exists_ _ _ => isFalse (fun h => h)

/- FD representation is decidable. -/
def IsRepresentedBy.decidable
    (fd : FDSpec Γ)
    (φ : Formula D Γ) :
    Decidable (fd.IsRepresentedBy φ) := by
  unfold IsRepresentedBy
  cases h : Formula.stripForalls φ with
  | mk xs matrix =>
      haveI : Decidable (fd.IsMatrix matrix) :=
        IsMatrix.decidable fd matrix
      change Decidable
        (xs = fd.varList ∧ fd.IsMatrix matrix)
      exact inferInstance

instance
    (fd : FDSpec Γ)
    (φ : Formula D Γ) :
    Decidable (fd.IsRepresentedBy φ) :=
  IsRepresentedBy.decidable fd φ

/- `toFormula` represents its own FD spec. -/
theorem isRepresentedBy_toFormula
    (fd : FDSpec Γ) :
    fd.IsRepresentedBy (fd.toFormula (D := D)) := by
  unfold IsRepresentedBy toFormula
  rw [Formula.stripForalls_forallMany]
  constructor
  · simp [matrix, Formula.stripForalls]
  · simp [matrix, body, leftAtom, rightAtom,
      eqHead, IsMatrix, IsBody, IsAtom, IsHead,
      tupleSigma, Formula.stripForalls]

end FDSpec

end Dependency

end RelCalc

------------------------------------------------------------
-- FD And Key Predicates
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- The raw relation name if a formula is a relation atom. -/
def relName? : Formula D Γ → Option A
| .rel a => some a.rel.1
| _ => none

/- Boolean recognizer for binary same-relation FD shape. -/
def isFDShape
    (φ : Formula D Γ) : Bool :=
  let r := stripForalls φ
  match r.2 with
  | .imp (.and lhs rhs) (.eq (.var _) (.var _)) =>
      decide
        (lhs.relName?.isSome ∧
          lhs.relName? = rhs.relName?)
  | _ => false

/-
  The binary same-relation shape of a functional
  dependency matrix.
-/
def IsFDShape
    (φ : Formula D Γ) : Prop :=
  φ.isFDShape = true

/- FD-shape recognition is decidable. -/
def IsFDShape.decidable
    (φ : Formula D Γ) :
    Decidable φ.IsFDShape := by
  unfold IsFDShape
  infer_instance

instance
    (φ : Formula D Γ) :
    Decidable φ.IsFDShape :=
  IsFDShape.decidable φ

/-
  A formula is an FD when it is an EGD with a two-atom
  same-relation antecedent.
-/
def IsFD
    (φ : Formula D Γ) : Prop :=
  φ.IsEGD ∧ φ.IsFDShape

/- FD recognition is decidable. -/
def IsFD.decidable
    (φ : Formula D Γ) :
    Decidable φ.IsFD := by
  unfold IsFD
  infer_instance

instance
    (φ : Formula D Γ) :
    Decidable φ.IsFD :=
  IsFD.decidable φ

/- Every recognized FD is an EGD. -/
theorem IsFD.toIsEGD
    {φ : Formula D Γ}
    (h : φ.IsFD) :
    φ.IsEGD := by
  exact h.1

namespace DependencyList

/-
  A list contains some formula representing the given FD
  spec. This avoids any formula-equality requirement.
-/
def RepresentsFDSpec
    (fd : Dependency.FDSpec Γ) :
    List (Formula D Γ) → Prop
| [] => False
| φ :: rest =>
    fd.IsRepresentedBy φ ∨ RepresentsFDSpec fd rest

/- List-level FD-spec representation is decidable. -/
def RepresentsFDSpec.decidable
    (fd : Dependency.FDSpec Γ) :
    (deps : List (Formula D Γ)) →
      Decidable (RepresentsFDSpec fd deps)
| [] => isFalse (fun h => h)
| φ :: rest => by
    haveI : Decidable (fd.IsRepresentedBy φ) :=
      inferInstance
    haveI : Decidable (RepresentsFDSpec fd rest) :=
      RepresentsFDSpec.decidable fd rest
    change Decidable
      (fd.IsRepresentedBy φ ∨
        RepresentsFDSpec fd rest)
    exact inferInstance

instance
    (fd : Dependency.FDSpec Γ)
    (deps : List (Formula D Γ)) :
    Decidable (RepresentsFDSpec (D := D) fd deps) :=
  RepresentsFDSpec.decidable fd deps

end DependencyList

/-
  `K` is a superkey for relation `X` in a dependency
  list.
-/
def IsSuperkeyFor
    (X : Γ.syms)
    (K : Finset (Fin (Γ.arity X)))
    (deps : List (Formula D Γ)) : Prop :=
  ∀ j : Fin (Γ.arity X),
    DependencyList.RepresentsFDSpec
      ({ rel := X, lhs := K, rhs := j } :
        Dependency.FDSpec Γ)
      deps

/- Superkey recognition is decidable. -/
def IsSuperkeyFor.decidable
    (X : Γ.syms)
    (K : Finset (Fin (Γ.arity X)))
    (deps : List (Formula D Γ)) :
    Decidable (IsSuperkeyFor X K deps) := by
  unfold IsSuperkeyFor
  infer_instance

instance
    (X : Γ.syms)
    (K : Finset (Fin (Γ.arity X)))
    (deps : List (Formula D Γ)) :
    Decidable (IsSuperkeyFor X K deps) :=
  IsSuperkeyFor.decidable X K deps

/-
  `K` is a candidate key when it is a superkey and no proper
  subset of `K` is a superkey.
-/
def IsCandidateKeyFor
    (X : Γ.syms)
    (K : Finset (Fin (Γ.arity X)))
    (deps : List (Formula D Γ)) : Prop :=
  IsSuperkeyFor X K deps ∧
    ∀ L ∈ K.powerset,
      L ≠ K → ¬ IsSuperkeyFor X L deps

/- Candidate-key recognition is decidable. -/
def IsCandidateKeyFor.decidable
    (X : Γ.syms)
    (K : Finset (Fin (Γ.arity X)))
    (deps : List (Formula D Γ)) :
    Decidable (IsCandidateKeyFor X K deps) := by
  unfold IsCandidateKeyFor
  infer_instance

instance
    (X : Γ.syms)
    (K : Finset (Fin (Γ.arity X)))
    (deps : List (Formula D Γ)) :
    Decidable (IsCandidateKeyFor X K deps) :=
  IsCandidateKeyFor.decidable X K deps

end Formula

end RelCalc
