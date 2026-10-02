-- Author: Jesse Comer
import Whiel.Vampire.EmptyCounterexample

/-
  API-facing Vampire counterexample terminology. The
  semantics remain those of RelCalc source entailments;
  this namespace only distinguishes general and
  adom-empty counterexamples at the Vampire boundary.

  Key definitions:
    * `Whiel.Vampire.CounterExample`
    * `Whiel.Vampire.AdomEmptyCounterExample`
    * `Whiel.Vampire.EmptyActiveDomainCounterExample`
    * `Whiel.Vampire.emptyActiveDomainCounterExample?`

  The executable correctness theorem is:
    * `emptyActiveDomainCounterExample?_eq_false_iff`
-/

------------------------------------------------------------
-- Semantic Counterexamples
------------------------------------------------------------

namespace Whiel

namespace Vampire

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Source assumptions hold and the conjecture fails. -/
def CounterExample
    (E : RelCalc.SentenceEntailment (D := D) Γ)
    (I : Instance D Γ) : Prop :=
  E.SatisfiesAxioms I ∧
    ¬ E.conjecture.SatIn I (E.activeDomain I)

/- A Vampire counterexample with empty instance adom. -/
def AdomEmptyCounterExample
    (E : RelCalc.SentenceEntailment (D := D) Γ)
    (I : Instance D Γ) : Prop :=
  I.AdomEmpty ∧ CounterExample E I

/- Existence of an adom-empty Vampire counterexample. -/
def HasAdomEmptyCounterExample
    (E : RelCalc.SentenceEntailment (D := D) Γ) : Prop :=
  ∃ I : Instance D Γ, AdomEmptyCounterExample E I

/- Absence of an adom-empty Vampire counterexample. -/
def NoAdomEmptyCounterExample
    (E : RelCalc.SentenceEntailment (D := D) Γ) : Prop :=
  ¬ HasAdomEmptyCounterExample E

/-
  A counterexample whose full source active domain is empty.
-/
def EmptyActiveDomainCounterExample
    (E : RelCalc.SentenceEntailment (D := D) Γ)
    (I : Instance D Γ) : Prop :=
  E.activeFinset I = ∅ ∧ CounterExample E I

/- Existence at an empty full source active domain. -/
def HasEmptyActiveDomainCounterExample
    (E : RelCalc.SentenceEntailment (D := D) Γ) :
    Prop :=
  ∃ I : Instance D Γ,
    EmptyActiveDomainCounterExample E I

/- Absence at an empty full source active domain. -/
def NoEmptyActiveDomainCounterExample
    (E : RelCalc.SentenceEntailment (D := D) Γ) :
    Prop :=
  ¬ HasEmptyActiveDomainCounterExample E

/- Compatibility with the legacy RelCalc predicate. -/
theorem
    emptyActiveDomain_iff_emptyCounterexample
    (E : RelCalc.SentenceEntailment (D := D) Γ)
    (I : Instance D Γ) :
    EmptyActiveDomainCounterExample E I ↔
      E.EmptyCounterexample I :=
  Iff.rfl

/- Compatibility with legacy RelCalc existence. -/
theorem
    hasEmptyActiveDomain_iff_hasEmptyCounterexample
    (E : RelCalc.SentenceEntailment (D := D) Γ) :
    HasEmptyActiveDomainCounterExample E ↔
      E.HasEmptyCounterexample :=
  Iff.rfl

/- Compatibility with the legacy absence condition. -/
theorem
    noEmptyActiveDomain_iff_noEmptyCounterexample
    (E : RelCalc.SentenceEntailment (D := D) Γ) :
    NoEmptyActiveDomainCounterExample E ↔
      E.NoEmptyCounterexample :=
  Iff.rfl

/- Empty full active domain implies adom-empty. -/
theorem
    EmptyActiveDomainCounterExample.toAdomEmpty
    {E : RelCalc.SentenceEntailment (D := D) Γ}
    {I : Instance D Γ}
    (h : EmptyActiveDomainCounterExample E I) :
    AdomEmptyCounterExample E I := by
  refine ⟨?_, h.2⟩
  have hParts : I.Adom = ∅ ∧ E.constants = ∅ := by
    simpa [RelCalc.SentenceEntailment.activeFinset]
      using h.1
  exact hParts.1

end Vampire

end Whiel

------------------------------------------------------------
-- Executable Empty-Active-Domain Check
------------------------------------------------------------

namespace Whiel

namespace Vampire

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Search specifically at an empty full active domain. -/
def emptyActiveDomainCounterExample?
    (E : RelCalc.SentenceEntailment (D := D) Γ)
    [Fintype Γ.syms] : Bool :=
  E.emptyCounterexample?

/- A negative check proves absence of such examples. -/
theorem
    noEmptyActiveDomainCounterExample_of_check_eq_false
    [Fintype Γ.syms]
    (E : RelCalc.SentenceEntailment (D := D) Γ)
    (h : emptyActiveDomainCounterExample? E = false) :
    NoEmptyActiveDomainCounterExample E := by
  rw [
    noEmptyActiveDomain_iff_noEmptyCounterexample]
  exact
    E.noEmptyCounterexample_of_emptyCounterexample?_eq_false
      h

/- The named checker exactly decides the named condition. -/
theorem
    emptyActiveDomainCounterExample?_eq_false_iff
    [Fintype Γ.syms]
    (E : RelCalc.SentenceEntailment (D := D) Γ) :
    emptyActiveDomainCounterExample? E = false ↔
      NoEmptyActiveDomainCounterExample E := by
  rw [
    noEmptyActiveDomain_iff_noEmptyCounterexample]
  exact E.emptyCounterexample?_eq_false_iff

end Vampire

end Whiel
