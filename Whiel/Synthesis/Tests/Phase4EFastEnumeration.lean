-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Fast.Freshness
import Whiel.Synthesis.DisjunctiveClause.Subsumption

/-
  Focused, benchmark-independent checks for the first fast
  disjunctive-clause enumerator and its coverage metadata.
-/

------------------------------------------------------------
-- Fast-Enumerator Contract
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace Phase4EFastEnumeration

open DisjunctiveClause
open Whiel.Synthesis.Enumerators

/- An old-only suffix is rejected at one counted node. -/
example :
    let result :=
      sublistsLenWithFreshResult 2
        ([(0, false), (1, false)] :
          List (Marked Nat))
    result.values = [] ∧
      result.stats =
        { visitedNodes := 1
          noFreshPrunes := 1
          tooShortPrunes := 0 } := by
  decide

/- An impossible requested width is rejected at one node. -/
example :
    let result :=
      sublistsLenWithFreshResult 3
        ([(0, false), (1, true)] :
          List (Marked Nat))
    result.values = [] ∧
      result.stats =
        { visitedNodes := 1
          noFreshPrunes := 0
          tooShortPrunes := 1 } := by
  decide

/- A long old-only suffix does not open an exponential tree. -/
example :
    let oldValues :=
      List.replicate 64
        ((0, false) : Marked Nat)
    let result :=
      sublistsLenWithFreshResult 32 oldValues
    result.values = [] ∧
      result.stats.visitedNodes = 1 ∧
      result.stats.noFreshPrunes = 1 := by
  decide

/- Direct generation preserves filtered `sublistsLen` order. -/
example :
    sublistsLenWithFresh 2
        ([(0, false), (1, true), (2, false)] :
          List (Marked Nat)) =
      [[(1, true), (2, false)],
        [(0, false), (1, true)]] := by
  rfl

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

example
    (alphabet : Alphabet D Γ) :
    FastEnumerator.CoversReference alphabet
      (Fast.outputThrough alphabet) :=
  Fast.coversReference alphabet

example
    (alphabet : Alphabet D Γ)
    (formula : QFAssertExpr D Γ) :
    formula ∈ Fast.outputThrough alphabet 1 ↔
      formula ∈ referenceProposal alphabet 0 :=
  Fast.mem_outputThrough_iff_mem_referenceProposal
    alphabet 0 formula

example
    (alphabet : Alphabet D Γ)
    (formula : QFAssertExpr D Γ) :
    formula ∈ Fast.outputThrough alphabet 2 ↔
      formula ∈ referenceProposal alphabet 1 :=
  Fast.mem_outputThrough_iff_mem_referenceProposal
    alphabet 1 formula

example
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    (Fast.outputThrough alphabet
      (stage + 1)).toFinset =
        referenceProposal alphabet stage :=
  Fast.outputThrough_toFinset_eq_referenceProposal
    alphabet stage

example
    (alphabet : Alphabet D Γ)
    (state : Fast.State (D := D) (Γ := Γ)) :
    (Fast.advance alphabet state).formulas.Nodup :=
  Fast.advance_formulas_nodup alphabet state

example
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    (Fast.advance alphabet
      (Fast.run alphabet (stage + 1)).1).formulas.Disjoint
        (Fast.outputThrough alphabet (stage + 1)) :=
  Fast.advance_formulas_disjoint_prior_output
    alphabet stage

example
    (alphabet : Alphabet D Γ)
    (completedStages : Nat) :
    (Fast.outputThrough alphabet completedStages).Nodup :=
  Fast.outputThrough_nodup alphabet completedStages

/- Finset insertion order cannot affect structural output. -/
example
    (leftRelation rightRelation : Γ.syms)
    (leftConstant rightConstant : D) :
    Fast.outputThrough
        ({ relations := {leftRelation, rightRelation}
           constants := {leftConstant, rightConstant} } :
          Alphabet D Γ) 2 =
      Fast.outputThrough
        ({ relations := {rightRelation, leftRelation}
           constants := {rightConstant, leftConstant} } :
          Alphabet D Γ) 2 := by
  congr 2 <;> ext value <;> simp [or_comm]

example
    (alphabet : Alphabet D Γ) :
    (Fast.advance alphabet
      (Fast.initialState (D := D) (Γ := Γ))).stage = 0 :=
  rfl

end Phase4EFastEnumeration

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Coverage-Metadata Theorems
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace Phase4EFastEnumeration

open DisjunctiveClause
open Whiel.Synthesis.Enumerators

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

example
    {source target : LiteralList D Γ}
    (hSubset : source ⊆ target) :
    QFAssertExpr.entails source.formula target.formula :=
  LiteralList.formula_entails_of_subset hSubset

end Phase4EFastEnumeration

end Tests

end Synthesis

end Whiel
