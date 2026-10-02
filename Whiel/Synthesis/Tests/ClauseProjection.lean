-- Author: Jesse Comer
import Whiel.Vampire.ClauseProjection

/-
  Focused checks for targeted clause projection from the
  proposition shapes emitted by Vampire.
-/

------------------------------------------------------------
-- Conjunction Projection
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace ClauseProjection

variable {A B C D E F G : Prop}

theorem nestedConjunct
    (h : A ∧ B ∧ C ∧ D) : C := by
  vampire_project using h

theorem selectedUniversal
    {Dα : Type}
    {P Q : Dα → Prop}
    (h : A ∧ (∀ x, P x ∨ Q x) ∧ B) :
    ∀ x, P x ∨ Q x := by
  vampire_project using h

theorem rebuiltConjunction
    (h : A ∧ B ∧ C) : B ∧ A := by
  vampire_project using h

end ClauseProjection
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Distributed Clauses
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace ClauseProjection

variable {A B C D E F G : Prop}

theorem projectedClause
    (h : (A ∧ B ∧ C) ∨ D) :
    D ∨ B := by
  vampire_project using h

theorem projectedClauseTail
    (h : (A ∧ B ∧ C) ∨ D ∨ E ∨ F) :
    B ∨ D ∨ E ∨ F := by
  vampire_project using h

theorem universalClause
    {Dα : Type}
    {P Q R S : Dα → Prop}
    (h : ∀ x, (P x ∧ Q x ∧ R x) ∨ S x) :
    ∀ x, S x ∨ Q x := by
  vampire_project using h

theorem manyUniversals
    {Dα : Type}
    {P Q R : Dα → Dα → Prop}
    (h : ∀ x y, P x y ∧ Q x y ∧ R x y) :
    ∀ x y, Q x y := by
  vampire_project using h

theorem selectedDisjunctionConjunct
    (h : ((((A ∧ B ∧ C) ∨ D ∨ E) ∧ F) ∧ G)) :
    B ∨ D ∨ E := by
  vampire_project using h

theorem reorderedInnerDisjunction
    (h : (((A ∨ B) ∧ C) ∨ D)) :
    B ∨ A ∨ D := by
  vampire_project using h

theorem distributedNestedConjunction
    (h : (((A ∧ B ∧ C) ∨ D) ∧ E)) :
    C ∨ D := by
  vampire_project using h

theorem forallOverDisjunction
    {Dα : Type}
    {P : Dα → Prop}
    (h : A ∨ ∀ sourceValue, P sourceValue) :
    ∀ targetValue, A ∨ P targetValue := by
  vampire_project using h

theorem nestedForallDistribution
    {Dα : Type}
    {P : Dα → Dα → Prop}
    {R : Dα → Dα → Dα → Prop}
    (h : A ∧
      (∀ x y, P x y ∨ ∀ z, R x y z)) :
    ∀ x y z, P x y ∨ R x y z := by
  vampire_project using h

theorem orderedNestedForallDistribution
    {Dα : Type}
    {P Q : Dα → Dα → Prop}
    {R S : Dα → Dα → Dα → Prop}
    (h :
      (∀ a b, Q a b ∨ ∀ c, S a b c) ∧
      (∀ x y, P x y ∨ ∀ z, R x y z)) :
    ∀ x y z, P x y ∨ R x y z := by
  vampire_project_ordered using h

theorem orderedNamedBinderReordering
    {Dα : Type}
    {P : Dα → Dα → Dα → Dα → Prop}
    (h : (∀ a d b c, P a b c d) ∧ True) :
    ∀ a b c d, P a b c d := by
  vampire_project_ordered using h

theorem exhaustivePermutationControl
    {Dα : Type}
    {P : Dα → Dα → Prop}
    (h : A ∨ ∀ a b, P b a) :
    ∀ x y, A ∨ P x y := by
  vampire_project using h

theorem orderedPermutationFailsClosed
    {Dα : Type}
    {P : Dα → Dα → Prop}
    (h : A ∨ ∀ a b, P b a) :
    ∀ x y, A ∨ P x y := by
  fail_if_success vampire_project_ordered using h
  intro x y
  exact Or.elim h Or.inl fun hp => Or.inr (hp y x)

theorem orderedEightBinderProjection
    {Dα : Type}
    {P : Dα → Dα → Dα → Dα → Dα → Dα → Dα → Dα → Prop}
    (h : ∀ a b c d e f g h, P a b c d e f g h) :
    ∀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈, P x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ := by
  vampire_project_ordered using h

theorem orderedEightBinderPermutationFailsClosed
    {Dα : Type}
    {P : Dα → Dα → Dα → Dα → Dα → Dα → Dα → Dα → Prop}
    (h : ∀ a b c d e f g h, P h g f e d c b a) :
    ∀ a b c d e f g h, P a b c d e f g h := by
  fail_if_success vampire_project_ordered using h
  intro a b c d e f g hValue
  exact h hValue g f e d c b a

end ClauseProjection
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Failure and Trust Checks
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace ClauseProjection

variable {A B C : Prop}

theorem rejectsUnrelatedGoal
    (h : A ∧ B)
    (hC : C) : C ∧ A := by
  fail_if_success vampire_project using h
  exact ⟨hC, h.1⟩

/-- info: 'Whiel.Synthesis.Tests.ClauseProjection.nestedConjunct' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.Tests.ClauseProjection.nestedConjunct

/-- info: 'Whiel.Synthesis.Tests.ClauseProjection.projectedClause' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.Tests.ClauseProjection.projectedClause

/-- info: 'Whiel.Synthesis.Tests.ClauseProjection.universalClause' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.Tests.ClauseProjection.universalClause

/-- info: 'Whiel.Synthesis.Tests.ClauseProjection.forallOverDisjunction' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.Tests.ClauseProjection.forallOverDisjunction

/-- info: 'Whiel.Synthesis.Tests.ClauseProjection.nestedForallDistribution' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.Tests.ClauseProjection.nestedForallDistribution

/-- info: 'Whiel.Synthesis.Tests.ClauseProjection.orderedNestedForallDistribution' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.Tests.ClauseProjection.orderedNestedForallDistribution

/-- info: 'Whiel.Synthesis.Tests.ClauseProjection.orderedNamedBinderReordering' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.Tests.ClauseProjection.orderedNamedBinderReordering

/-- info: 'Whiel.Synthesis.Tests.ClauseProjection.orderedEightBinderProjection' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.Tests.ClauseProjection.orderedEightBinderProjection

/-- info: 'Whiel.Synthesis.Tests.ClauseProjection.exhaustivePermutationControl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.Tests.ClauseProjection.exhaustivePermutationControl

end ClauseProjection
end Tests
end Synthesis
end Whiel
