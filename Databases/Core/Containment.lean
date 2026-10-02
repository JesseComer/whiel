-- Author: Jesse Comer
import Databases.UnnamedModel.Instance

/-
  This file defines a small shared interface for objects
  with instance-to-relation query semantics.

  Key definitions include:
    * `QueryEval`
    * `QueryEval.eval`
    * `QueryEval.Contained`

  Concrete language instances should be declared next to
  the corresponding evaluator definitions.
-/

------------------------------------------------------------
-- Query Evaluation Interface
------------------------------------------------------------

class QueryEval
    (Q : Type)
    (D : Type)
    [Domain D]
    {A : Type}
    [RelationNames A]
    (Γ : UnnamedSchema A)
    (n : Nat) where
  eval : Q → Instance D Γ → FinRelation D n

namespace QueryEval

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}
variable {n : Nat}
variable {Q R : Type}

/- Same-schema, same-arity query containment. -/
def Contained
    [QueryEval Q D Γ n]
    [QueryEval R D Γ n]
    (q : Q)
    (r : R) : Prop :=
  ∀ I : Instance D Γ,
    QueryEval.eval
        (Q := Q) (D := D) (Γ := Γ) (n := n)
        q I ⊆
      QueryEval.eval
        (Q := R) (D := D) (Γ := Γ) (n := n)
        r I

/- Containment is reflexive. -/
theorem Contained.refl
    [QueryEval Q D Γ n]
    (q : Q) :
    Contained (D := D) (Γ := Γ) (n := n) q q := by
  intro I t ht
  exact ht

/- Containment is transitive. -/
theorem Contained.trans
    [QueryEval Q D Γ n]
    [QueryEval R D Γ n]
    {S : Type}
    [QueryEval S D Γ n]
    {q : Q}
    {r : R}
    {s : S}
    (hqr :
      Contained (D := D) (Γ := Γ) (n := n) q r)
    (hrs :
      Contained (D := D) (Γ := Γ) (n := n) r s) :
    Contained (D := D) (Γ := Γ) (n := n) q s := by
  intro I t ht
  exact hrs I (hqr I ht)

end QueryEval
