-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.FullSlice
import Whiel.Synthesis.DisjunctiveClause.Order
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sublists

/-
  Canonical readable realization of the full bounded slice.

  `FullEnumeration.representations` is an order-free finite
  universe used by the specification proofs. This module
  sorts the eligible literals once and enumerates bounded
  sublists. It does not construct literal permutations. The
  structural order is derived from the ordered relation-name
  and domain carriers.

  Main declarations:
    * `canonicalize`
    * `representations` and `clauses`
    * `sameLiterals_iff_eq_of_mem_representations`
    * `representations_complete_up_to_equiv`
-/

------------------------------------------------------------
-- Canonical Literal Lists
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace CanonicalEnumeration

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

local instance : LinearOrder (Literal D Γ) :=
  StructuralOrder.literalLinearOrder

/- Sort a literal set in the configured canonical order. -/
def canonicalize
    (literalList : LiteralList D Γ) :
    LiteralList D Γ :=
  literalList.toFinset.sort (· ≤ ·)

/- Canonicalization removes repeated literals. -/
theorem canonicalize_normalized
    (literalList : LiteralList D Γ) :
    (canonicalize literalList).IsNormalized := by
  exact Finset.sort_nodup _ _

/- Canonicalization preserves a normalized literal set. -/
theorem canonicalize_sameLiterals
    (literalList : LiteralList D Γ)
    (hNormalized : literalList.IsNormalized) :
    (canonicalize literalList).SameLiterals
      literalList := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact canonicalize_normalized literalList
  · exact hNormalized
  · simp [canonicalize]

/- Equal literal sets have equal canonical forms. -/
theorem canonicalize_eq_of_sameLiterals
    {left right : LiteralList D Γ}
    (hSame : left.SameLiterals right) :
    canonicalize left = canonicalize right := by
  unfold canonicalize
  rw [List.toFinset_eq_of_perm left right hSame]

/- Canonicalization preserves full eligibility. -/
theorem canonicalize_eligible
    (literalList : LiteralList D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (hNormalized : literalList.IsNormalized)
    (hEligible :
      literalList.IsEligible alphabet parameters) :
    (canonicalize literalList).IsEligible
      alphabet parameters := by
  have hSame :=
    canonicalize_sameLiterals literalList hNormalized
  constructor
  · rw [hSame.length_eq]
    exact hEligible.1
  · intro literal hLiteral
    exact hEligible.2 literal
      (hSame.mem_iff.mp hLiteral)

end CanonicalEnumeration

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Canonical Full-Slice Realization
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace CanonicalEnumeration

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

local instance : LinearOrder (Literal D Γ) :=
  StructuralOrder.literalLinearOrder

/-
  One sorted representative for every eligible literal set.
-/
def literalOrder
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    List (Literal D Γ) :=
  (FullEnumeration.literals alphabet parameters).sort
    (· ≤ ·)

@[simp] theorem mem_literalOrder_iff
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (literal : Literal D Γ) :
    literal ∈ literalOrder alphabet parameters ↔
      literal.IsEligible alphabet parameters := by
  rw [literalOrder, Finset.mem_sort,
    FullEnumeration.mem_literals_iff]

theorem literalOrder_nodup
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    (literalOrder alphabet parameters).Nodup := by
  exact Finset.sort_nodup _ _

theorem literalOrder_pairwise
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    (literalOrder alphabet parameters).Pairwise
      (· ≤ ·) := by
  exact Finset.pairwise_sort _ _

/- Bounded sublists of the canonical literal order. -/
def boundedLiteralLists
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    List (LiteralList D Γ) :=
  let literals := literalOrder alphabet parameters
  (List.range
    (min parameters.maxClauseWidth
      literals.length + 1)).flatMap fun width =>
        literals.sublistsLen width

@[simp] theorem mem_boundedLiteralLists_iff
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (literalList : LiteralList D Γ) :
    literalList ∈
        boundedLiteralLists alphabet parameters ↔
      literalList.Sublist
          (literalOrder alphabet parameters) ∧
        literalList.length ≤
          parameters.maxClauseWidth := by
  simp only [boundedLiteralLists,
    List.mem_flatMap, List.mem_range,
    List.mem_sublistsLen]
  constructor
  · rintro
      ⟨width, hWidth, hSublist, hLength⟩
    refine ⟨hSublist, ?_⟩
    rw [hLength]
    exact
      (Nat.lt_succ_iff.mp hWidth).trans
        (Nat.min_le_left _ _)
  · rintro ⟨hSublist, hWidth⟩
    refine
      ⟨literalList.length, ?_, hSublist, rfl⟩
    rw [Nat.lt_succ_iff]
    exact
      Nat.le_min.mpr
        ⟨hWidth, hSublist.length_le⟩

/- One representation for each bounded literal subset. -/
def representations
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Finset (LiteralList D Γ) :=
  (boundedLiteralLists alphabet parameters).toFinset

/- Decode every canonical representation. -/
def clauses
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Candidate D Γ :=
  (representations alphabet parameters).image
    FullEnumeration.decode

/- Exact membership in the direct canonical realization. -/
@[simp] theorem mem_representations_iff
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (representation : LiteralList D Γ) :
    representation ∈
        representations alphabet parameters ↔
      representation.Sublist
          (literalOrder alphabet parameters) ∧
        representation.length ≤
          parameters.maxClauseWidth := by
  simp [representations]

/- Every emitted representation is normalized. -/
theorem representation_normalized
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {representation : LiteralList D Γ}
    (hMember :
      representation ∈ representations
        alphabet parameters) :
    representation.IsNormalized := by
  have hSublist :=
    ((mem_representations_iff alphabet parameters
      representation).mp hMember).1
  exact
    hSublist.nodup
      (literalOrder_nodup alphabet parameters)

/- Every emitted representation is fully eligible. -/
theorem representation_eligible
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {representation : LiteralList D Γ}
    (hMember :
      representation ∈ representations
        alphabet parameters) :
    representation.IsEligible alphabet parameters := by
  have hProperties :=
    (mem_representations_iff alphabet parameters
      representation).mp hMember
  constructor
  · exact hProperties.2
  · intro literal hLiteral
    apply
      (mem_literalOrder_iff alphabet parameters
        literal).mp
    exact hProperties.1.subset hLiteral

/- Emitted representations follow the literal order. -/
theorem representation_pairwise
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {representation : LiteralList D Γ}
    (hMember :
      representation ∈ representations
        alphabet parameters) :
    representation.Pairwise (· ≤ ·) := by
  exact
    (literalOrder_pairwise alphabet parameters).sublist
      ((mem_representations_iff alphabet parameters
        representation).mp hMember).1

/- The realization emits at most one list per set. -/
theorem sameLiterals_iff_eq_of_mem_representations
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {left right : LiteralList D Γ}
    (hLeft :
      left ∈ representations alphabet parameters)
    (hRight :
      right ∈ representations alphabet parameters) :
    left.SameLiterals right ↔ left = right := by
  constructor
  · intro hSame
    exact hSame.eq_of_pairwise'
      (representation_pairwise
        alphabet parameters hLeft)
      (representation_pairwise
        alphabet parameters hRight)
  · rintro rfl
    exact List.Perm.refl _

/- Every normalized eligible set has one output. -/
theorem representations_cover
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (literalList : LiteralList D Γ)
    (hNormalized : literalList.IsNormalized)
    (hEligible :
      literalList.IsEligible alphabet parameters) :
    ∃ representation ∈
        representations alphabet parameters,
      representation.SameLiterals literalList := by
  have hSubset :
      literalList ⊆ literalOrder alphabet parameters := by
    intro literal hLiteral
    exact
      (mem_literalOrder_iff alphabet parameters
        literal).mpr
          (hEligible.2 literal hLiteral)
  rcases hNormalized.subperm hSubset with
    ⟨representation, hSame, hSublist⟩
  have hWidth :
      representation.length ≤
        parameters.maxClauseWidth := by
    rw [hSame.length_eq]
    exact hEligible.1
  exact
    ⟨representation,
      (mem_representations_iff alphabet parameters
        representation).mpr ⟨hSublist, hWidth⟩,
      hSame⟩

/- An eligible normalized list has its sorted output. -/
theorem canonicalize_mem_representations
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (literalList : LiteralList D Γ)
    (hNormalized : literalList.IsNormalized)
    (hEligible :
      literalList.IsEligible alphabet parameters) :
    canonicalize literalList ∈
      representations alphabet parameters := by
  rcases
      representations_cover alphabet parameters
        literalList hNormalized hEligible with
    ⟨representation, hRepresentation, hSame⟩
  have hCanonicalSame :=
    canonicalize_sameLiterals literalList hNormalized
  have hPerm :
      representation.SameLiterals
        (canonicalize literalList) :=
    hSame.trans hCanonicalSame.symm
  have hEqual :=
    hPerm.eq_of_pairwise'
      (representation_pairwise alphabet parameters
        hRepresentation)
      (Finset.pairwise_sort _ _)
  change
    literalList.toFinset.sort (· ≤ ·) ∈
      representations alphabet parameters
  rw [← hEqual]
  exact hRepresentation

/- Every emitted formula belongs to the full slice. -/
theorem representations_sound
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {representation : LiteralList D Γ}
    (hMember :
      representation ∈ representations
        alphabet parameters) :
    FullEnumeration.decode representation ∈
      (slice alphabet parameters).clauses := by
  apply
    (mem_slice_iff alphabet parameters
      (FullEnumeration.decode representation)).mpr
  exact
    ⟨representation,
      representation_normalized
        alphabet parameters hMember,
      representation_eligible
        alphabet parameters hMember,
      rfl⟩

/-
  Every full-slice formula has an equivalent canonical
  emitted representation.
-/
theorem representations_complete_up_to_equiv
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (formula : Clause D Γ)
    (hMember :
      formula ∈ (slice alphabet parameters).clauses) :
    ∃ representation ∈
        representations alphabet parameters,
      QFAssertExpr.equiv
        (FullEnumeration.decode representation)
        formula := by
  rcases
      (mem_slice_iff alphabet parameters formula).mp
        hMember with
    ⟨literalList, hNormalized, hEligible, rfl⟩
  rcases
      representations_cover alphabet parameters
        literalList hNormalized hEligible with
    ⟨representation, hRepresentation, hSame⟩
  exact
    ⟨representation, hRepresentation,
      representation.formula_equiv_of_sameLiterals
        hSame⟩

end CanonicalEnumeration

end DisjunctiveClause

end Synthesis

end Whiel
