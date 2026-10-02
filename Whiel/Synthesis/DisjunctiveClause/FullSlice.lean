-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.FullEnumeration

/-
  Extensional finite slice for the full bounded
  disjunctive-clause grammar.

  Eligibility is declared independently in `FullSpec`. The
  order-free executable Finset in `FullEnumeration` supplies
  the finiteness witness and exact correspondence.

  Main declarations:
    * `slice` and `mem_slice_iff`
    * `baseSlice_subset_slice`
    * `slice_eq_baseSlice_of_maxRAOps_eq_zero`
    * `FullEnumeration.representations_sound`
    * `FullEnumeration.representations_complete`
-/

------------------------------------------------------------
-- Extensional Full Slice
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

open LiteralList

private def sliceSet
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Set (Clause D Γ) :=
  {formula |
    ∃ literalList : LiteralList D Γ,
      literalList.IsNormalized ∧
        literalList.IsEligible alphabet parameters ∧
        literalList.formula = formula}

private theorem finite_sliceSet
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    (sliceSet alphabet parameters).Finite := by
  have hSet :
      sliceSet alphabet parameters =
        (↑(FullEnumeration.clauses
          alphabet parameters) : Set (Clause D Γ)) := by
    ext formula
    simp only [sliceSet, Set.mem_setOf_eq,
      FullEnumeration.clauses, Finset.mem_coe,
      Finset.mem_image]
    constructor
    · rintro
        ⟨literalList, hNormalized, hEligible, rfl⟩
      exact
        ⟨literalList,
          (FullEnumeration.mem_representations_iff
            alphabet parameters literalList).mpr
              ⟨hNormalized, hEligible⟩,
          rfl⟩
    · rintro ⟨literalList, hMember, rfl⟩
      have hProperties :=
        (FullEnumeration.mem_representations_iff
          alphabet parameters literalList).mp hMember
      exact
        ⟨literalList, hProperties.1,
          hProperties.2, rfl⟩
  rw [hSet]
  exact Finset.finite_toSet _

/-
  The finite set of all normalized, fully eligible
  disjunctive clauses at one parameter choice.
-/
def slice
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Slice D Γ where
  clauses := sliceSet alphabet parameters
  finite := finite_sliceSet alphabet parameters
  subset_class := by
    rintro formula
      ⟨literalList, hNormalized, _, rfl⟩
    exact
      literalList.formula_mem_clauseClass hNormalized

/- Exact extensional membership in the full slice. -/
@[simp] theorem mem_slice_iff
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (formula : Clause D Γ) :
    formula ∈ (slice alphabet parameters).clauses ↔
      ∃ literalList : LiteralList D Γ,
        literalList.IsNormalized ∧
          literalList.IsEligible alphabet parameters ∧
          literalList.formula = formula := by
  simp [slice, sliceSet]

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Base-Slice Compatibility
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

open LiteralList

/- Every base-slice member belongs to the full slice. -/
theorem baseSlice_subset_slice
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    (baseSlice alphabet parameters).clauses ⊆
      (slice alphabet parameters).clauses := by
  intro formula hMember
  rcases
      (mem_baseSlice_iff alphabet parameters formula).mp
        hMember with
    ⟨literalList, hNormalized, hEligible, rfl⟩
  apply
    (mem_slice_iff alphabet parameters
      literalList.formula).mpr
  exact
    ⟨literalList, hNormalized,
      literalList.isEligible_of_isBaseEligible
        alphabet parameters hEligible,
      rfl⟩

private theorem slice_ext
    {left right : Slice D Γ}
    (hClauses : left.clauses = right.clauses) :
    left = right := by
  cases left
  cases right
  simp_all

/- At RA cost zero, the full and base slices agree. -/
theorem slice_eq_baseSlice_of_maxRAOps_eq_zero
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (hMaxCost : parameters.maxRAOps = 0) :
    slice alphabet parameters =
      baseSlice alphabet parameters := by
  apply slice_ext
  ext formula
  constructor
  · intro hMember
    rcases
        (mem_slice_iff alphabet parameters formula).mp
          hMember with
      ⟨literalList, hNormalized, hEligible, rfl⟩
    apply
      (mem_baseSlice_iff alphabet parameters
        literalList.formula).mpr
    have hBaseEligible :
        literalList.IsBaseEligible alphabet parameters := by
      exact
        (isEligible_iff_isBaseEligible_of_maxRAOps_eq_zero
          literalList alphabet parameters hMaxCost).mp
            hEligible
    exact
      ⟨literalList, hNormalized,
        hBaseEligible, rfl⟩
  · intro hMember
    exact
      baseSlice_subset_slice alphabet parameters hMember

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Enumerator Correspondence
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace FullEnumeration

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Every internal-universe representation belongs to the
  full slice.
-/
theorem representations_sound
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {representation : Representation D Γ}
    (hMember :
      representation ∈
        representations alphabet parameters) :
    decode representation ∈
      (slice alphabet parameters).clauses := by
  apply
    (mem_slice_iff alphabet parameters
      (decode representation)).mpr
  exact
    ⟨representation,
      representation_normalized
        alphabet parameters hMember,
      representation_eligible
        alphabet parameters hMember,
      rfl⟩

/-
  Every full-slice formula occurs in the internal universe
  with exactly the declared syntax.
-/
theorem representations_complete
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (formula : Clause D Γ)
    (hMember :
      formula ∈ (slice alphabet parameters).clauses) :
    ∃ representation ∈
      representations alphabet parameters,
      decode representation = formula := by
  rcases
      (mem_slice_iff alphabet parameters formula).mp
        hMember with
    ⟨literalList, hNormalized, hEligible, rfl⟩
  exact
    ⟨literalList,
      representations_cover alphabet parameters
        literalList hNormalized hEligible,
      rfl⟩

/- Semantic completeness follows from exact completeness. -/
theorem representations_complete_up_to_equiv
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (formula : Clause D Γ)
    (hMember :
      formula ∈ (slice alphabet parameters).clauses) :
    ∃ representation ∈
      representations alphabet parameters,
      QFAssertExpr.equiv
        (decode representation) formula := by
  rcases representations_complete
      alphabet parameters formula hMember with
    ⟨representation, hRepresentation, hFormula⟩
  subst formula
  exact
    ⟨representation, hRepresentation,
      QFAssertExpr.equiv_refl _⟩

end FullEnumeration

end DisjunctiveClause

end Synthesis

end Whiel
