-- Author: Jesse Comer
import Whiel.Hoare.Abstract

/-
  Semantic counterexamples to Whiel Hoare triples.

  Key definitions:
    * `Whiel.Hoare.counterExample`

  Invalidity follows by:
    * `Whiel.Hoare.invalid_of_counterExample`
-/

------------------------------------------------------------
-- Hoare Counterexamples
------------------------------------------------------------

namespace Whiel

namespace Hoare

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  A terminating execution which falsifies a Hoare triple.
-/
def counterExample
    {α β : Type}
    [ToAssertion D Γ α]
    [ToAssertion D Γ β]
    (pre : α)
    (C : Cmd D Γ)
    (post : β)
    (I J : Instance D Γ) : Prop :=
  toAssertion pre I ∧
    Cmd.BigStep C I J ∧
      ¬ toAssertion post J

/- A semantic counterexample proves Hoare invalidity. -/
theorem invalid_of_counterExample
    {α β : Type}
    [ToAssertion D Γ α]
    [ToAssertion D Γ β]
    {pre : α}
    {C : Cmd D Γ}
    {post : β}
    {I J : Instance D Γ}
    (h : counterExample pre C post I J) :
    ¬ HoareValid pre C post := by
  intro hValid
  exact h.2.2 (hValid I J h.1 h.2.1)

end Hoare

end Whiel
