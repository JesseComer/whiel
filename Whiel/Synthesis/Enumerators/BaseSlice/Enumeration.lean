-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.Spec
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sublists

/-
  Readable executable realization of the disjunctive base
  slice.

  Given an alphabet and parameters, this module computes one
  normalized literal-list representative for every eligible
  literal set. Their decoding is sound for and
  equivalence-complete with the extensional
  `DisjunctiveClause.baseSlice`.

  `Spec.lean` defines the clause class, the slice, and exact
  slice membership. This module proves that its finite
  output is sound and complete for that independent
  specification.

  Intermediate term, atom, and literal lists implement the
  readable construction. They are not part of the conceptual
  interface.

  Main declarations:
    * `Representation`, `decode`, and `baseRepresentations`
    * `baseRepresentations_sound`
    * `baseRepresentations_complete_up_to_equiv`
-/

------------------------------------------------------------
-- Ordered Alphabet Views
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace Alphabet

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Relations in the carrier's canonical order. -/
def relationList
    [LinearOrder A]
    (alphabet : Alphabet D Γ) :
    List Γ.syms :=
  alphabet.relations.sort

/- Constants in the carrier's canonical order. -/
def constantList
    [LinearOrder D]
    (alphabet : Alphabet D Γ) :
    List D :=
  alphabet.constants.sort

@[simp] theorem mem_relationList_iff
    [LinearOrder A]
    (alphabet : Alphabet D Γ)
    (relation : Γ.syms) :
    relation ∈ alphabet.relationList ↔
      relation ∈ alphabet.relations := by
  simp [relationList]

@[simp] theorem mem_constantList_iff
    [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (constant : D) :
    constant ∈ alphabet.constantList ↔
      constant ∈ alphabet.constants := by
  simp [constantList]

theorem relationList_nodup
    [LinearOrder A]
    (alphabet : Alphabet D Γ) :
    alphabet.relationList.Nodup := by
  simp [relationList]

theorem constantList_nodup
    [LinearOrder D]
    (alphabet : Alphabet D Γ) :
    alphabet.constantList.Nodup := by
  simp [constantList]

end Alphabet

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Enabled Kinds and Base Terms
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

namespace BaseSlice

open DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- All atom kinds in stable order. -/
def allAtomKinds : List AtomKind :=
  [.equality, .containment]

/- All literal signs in stable order. -/
def allLiteralSigns : List LiteralSign :=
  [.positive, .negative]

/- Enabled atom kinds in stable order. -/
def atomKinds
    (parameters : Parameters) :
    List AtomKind :=
  allAtomKinds.filter fun kind =>
    kind ∈ parameters.enabledAtomKinds

/- Enabled literal signs in stable order. -/
def literalSigns
    (parameters : Parameters) :
    List LiteralSign :=
  allLiteralSigns.filter fun sign =>
    sign ∈ parameters.enabledLiteralSigns

@[simp] theorem mem_allAtomKinds
    (kind : AtomKind) :
    kind ∈ allAtomKinds := by
  cases kind <;> simp [allAtomKinds]

@[simp] theorem mem_allLiteralSigns
    (sign : LiteralSign) :
    sign ∈ allLiteralSigns := by
  cases sign <;> simp [allLiteralSigns]

@[simp] theorem mem_atomKinds_iff
    (parameters : Parameters)
    (kind : AtomKind) :
    kind ∈ atomKinds parameters ↔
      kind ∈ parameters.enabledAtomKinds := by
  simp [atomKinds]

@[simp] theorem mem_literalSigns_iff
    (parameters : Parameters)
    (sign : LiteralSign) :
    sign ∈ literalSigns parameters ↔
      sign ∈ parameters.enabledLiteralSigns := by
  simp [literalSigns]

/-
  All enabled base terms.

  Source relations are never arity-filtered. Empty terms use
  `emptyArities`, which adds every enabled relation arity to
  the explicit output-arity range.
-/
def baseTerms
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    List (Term D Γ) :=
  ((if RABase.top ∈ parameters.enabledRABases then
      [Term.top]
    else
      []) ++
    (if RABase.empty ∈ parameters.enabledRABases then
      (emptyArities alphabet parameters).sort.map
        Term.empty
    else
      []) ++
    (if RABase.relation ∈
        parameters.enabledRABases then
      alphabet.relationList.map Term.relation
    else
      []) ++
    (if RABase.singleton ∈
        parameters.enabledRABases then
      alphabet.constantList.map Term.singleton
    else
      [])).dedup

theorem baseTerms_nodup
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    (baseTerms alphabet parameters).Nodup :=
  List.nodup_dedup _

end BaseSlice

end Enumerators

end Synthesis

end Whiel

------------------------------------------------------------
-- Base Atoms and Literals
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

namespace BaseSlice

open DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Enabled comparisons for one pair of base terms. -/
def atomsForBasePair
    (parameters : Parameters)
    (left right : Term D Γ) :
    List (Atom D Γ) :=
  if sameArity :
      left.arity = right.arity then
    (atomKinds parameters).map fun kind =>
      Atom.ofTerms kind left right sameArity
  else
    []

/- All enabled comparisons over base terms. -/
def baseAtoms
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    List (Atom D Γ) :=
  let terms := baseTerms alphabet parameters
  (terms.flatMap fun left =>
    terms.flatMap fun right =>
      atomsForBasePair parameters left right).dedup

/- All enabled signed base atoms. -/
def baseLiterals
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    List (Literal D Γ) :=
  ((baseAtoms alphabet parameters).flatMap fun atom =>
    (literalSigns parameters).map fun sign =>
      ⟨sign, atom⟩).dedup

theorem baseAtoms_nodup
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    (baseAtoms alphabet parameters).Nodup :=
  List.nodup_dedup _

theorem baseLiterals_nodup
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    (baseLiterals alphabet parameters).Nodup :=
  List.nodup_dedup _

end BaseSlice

end Enumerators

end Synthesis

end Whiel

------------------------------------------------------------
-- Bounded Clauses and the Base Slice
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

namespace BaseSlice

open DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Readable representation used by this realization. -/
abbrev Representation
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) :=
  LiteralList D Γ

/- Decode a literal list to its QF clause. -/
def decode
    (literalList : Representation D Γ) :
    Clause D Γ :=
  literalList.formula

/- Literal sublists through the requested clause width. -/
def boundedLiteralLists
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    List (List (Literal D Γ)) :=
  let literals := baseLiterals alphabet parameters
  (List.range
    (min parameters.maxClauseWidth
      literals.length + 1)).flatMap fun width =>
        literals.sublistsLen width

/-
  Every bounded sublist is normalized because the source
  literal list is duplicate-free.
-/
theorem boundedLiteralLists_normalized
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {literalList : LiteralList D Γ}
    (hMember :
      literalList ∈
        boundedLiteralLists alphabet parameters) :
    literalList.IsNormalized := by
  unfold boundedLiteralLists at hMember
  rcases List.mem_flatMap.mp hMember with
    ⟨_, _, hSublists⟩
  exact
    (List.mem_sublistsLen.mp hSublists).1.nodup
      (baseLiterals_nodup alphabet parameters)

/-
  One duplicate-free representative of each bounded literal
  set. The final `dedup` is deliberately simple; a later
  realization may prove it unnecessary.
-/
def baseRepresentations
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    List (Representation D Γ) :=
  (boundedLiteralLists alphabet parameters).dedup

/-
  Every emitted representation satisfies the separate
  normalization invariant.
-/
theorem baseRepresentation_normalized
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {literalList : Representation D Γ}
    (hMember :
      literalList ∈
        baseRepresentations alphabet parameters) :
    literalList.IsNormalized := by
  apply
    boundedLiteralLists_normalized
      alphabet parameters
  simpa [baseRepresentations] using hMember

/- Decode every base-slice clause representative. -/
def baseClauses
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    List (Clause D Γ) :=
  (baseRepresentations alphabet parameters).map
    decode

theorem baseRepresentations_nodup
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    (baseRepresentations
      alphabet parameters).Nodup :=
  List.nodup_dedup _

@[simp] theorem decode_empty :
    decode ([] : Representation D Γ) =
        QFAssertExpr.«false» :=
  rfl

@[simp] theorem decode_singleton
    (literal : Literal D Γ) :
    decode ([literal] : Representation D Γ) =
      literal.formula :=
  rfl

end BaseSlice

end Enumerators

end Synthesis

end Whiel

------------------------------------------------------------
-- Enumeration Correspondence
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

namespace BaseSlice

open DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

@[simp] theorem mem_baseTerms_iff
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (term : Term D Γ) :
    term ∈ baseTerms alphabet parameters ↔
      term.IsBaseEligible alphabet parameters := by
  simp only [baseTerms, List.mem_dedup,
    List.mem_append, List.mem_ite_nil_right,
    List.mem_singleton, List.mem_map,
    Finset.mem_sort,
    Alphabet.mem_relationList_iff,
    Alphabet.mem_constantList_iff,
    Term.IsBaseEligible]
  aesop

@[simp] theorem mem_atomsForBasePair_iff
    (parameters : Parameters)
    (left right : Term D Γ)
    (atom : Atom D Γ) :
    atom ∈ atomsForBasePair parameters left right ↔
      ∃ sameArity :
          left.arity = right.arity,
        ∃ kind,
          kind ∈ parameters.enabledAtomKinds ∧
            atom =
              Atom.ofTerms kind left right
                sameArity := by
  unfold atomsForBasePair
  split
  · rename_i sameArity
    simp only [List.mem_map]
    constructor
    · rintro ⟨kind, hKind, hAtom⟩
      exact
        ⟨sameArity, kind,
          (mem_atomKinds_iff
            parameters kind).mp hKind,
          hAtom.symm⟩
    · rintro
        ⟨otherArity, kind, hKind, hAtom⟩
      refine
        ⟨kind,
          (mem_atomKinds_iff
            parameters kind).mpr hKind, ?_⟩
      rw [hAtom]
  · rename_i hDifferent
    constructor
    · simp
    · rintro ⟨sameArity, _⟩
      exact (hDifferent sameArity).elim

@[simp] theorem mem_baseAtoms_iff
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (atom : Atom D Γ) :
    atom ∈ baseAtoms alphabet parameters ↔
      atom.IsBaseEligible
        alphabet parameters := by
  simp only [baseAtoms, List.mem_dedup,
    List.mem_flatMap, mem_atomsForBasePair_iff,
    mem_baseTerms_iff, Atom.IsBaseEligible]
  constructor
  · rintro
      ⟨left, hLeft, right, hRight,
        sameArity, kind, hKind, hAtom⟩
    exact
      ⟨kind, hKind, left, hLeft, right,
        hRight, sameArity, hAtom⟩
  · rintro
      ⟨kind, hKind, left, hLeft, right,
        hRight, sameArity, hAtom⟩
    exact
      ⟨left, hLeft, right, hRight,
        sameArity, kind, hKind, hAtom⟩

@[simp] theorem mem_baseLiterals_iff
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (literal : Literal D Γ) :
    literal ∈ baseLiterals alphabet parameters ↔
      literal.IsBaseEligible
        alphabet parameters := by
  cases literal with
  | mk sign atom =>
      simp [baseLiterals,
        Literal.IsBaseEligible,
        mem_baseAtoms_iff, and_comm]

@[simp] theorem mem_boundedLiteralLists_iff
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (literals : List (Literal D Γ)) :
    literals ∈
        boundedLiteralLists alphabet parameters ↔
      literals.Sublist
          (baseLiterals alphabet parameters) ∧
        literals.length ≤
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
      ⟨literals.length, ?_, hSublist, rfl⟩
    rw [Nat.lt_succ_iff]
    exact
      Nat.le_min.mpr
        ⟨hWidth, hSublist.length_le⟩

@[simp] theorem mem_baseRepresentations_iff
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (literalList : Representation D Γ) :
    literalList ∈
        baseRepresentations alphabet parameters ↔
      literalList.Sublist
          (baseLiterals alphabet parameters) ∧
        literalList.length ≤
          parameters.maxClauseWidth := by
  simp [baseRepresentations]

/-
  Every emitted representation satisfies base eligibility.
-/
theorem baseRepresentation_eligible
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {literalList : Representation D Γ}
    (hMember :
      literalList ∈
        baseRepresentations alphabet parameters) :
    literalList.IsBaseEligible
      alphabet parameters := by
  have hBounded :=
    (mem_baseRepresentations_iff
      alphabet parameters literalList).mp hMember
  refine ⟨hBounded.2, ?_⟩
  intro literal hLiteral
  apply
    (mem_baseLiterals_iff
      alphabet parameters literal).mp
  exact hBounded.1.subset hLiteral

/-
  Two emitted representations have the same literals exactly
  when they are equal. Thus the realization emits one
  representative of each eligible literal set.
-/
theorem sameLiterals_iff_eq_of_mem_baseRepresentations
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {left right : Representation D Γ}
    (hLeft :
      left ∈
        baseRepresentations alphabet parameters)
    (hRight :
      right ∈
        baseRepresentations alphabet parameters) :
    left.SameLiterals right ↔
      left = right := by
  have hLeftSublist :=
    ((mem_baseRepresentations_iff
      alphabet parameters left).mp hLeft).1
  have hRightSublist :=
    ((mem_baseRepresentations_iff
      alphabet parameters right).mp hRight).1
  constructor
  · intro hSame
    have hLists :
        left = right :=
      ((baseLiterals_nodup
          alphabet parameters).perm_iff_eq_of_sublist
        hLeftSublist hRightSublist).mp hSame
    exact hLists
  · rintro rfl
    exact List.Perm.refl _

/-
  Every eligible duplicate-free literal list has one
  enumerated permutation.
-/
theorem baseRepresentations_cover
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (literalList : LiteralList D Γ)
    (hNormalized : literalList.IsNormalized)
    (hEligible :
      literalList.IsBaseEligible alphabet parameters) :
    ∃ representation ∈
        baseRepresentations alphabet parameters,
      representation.SameLiterals literalList := by
  have hSubset :
      literalList ⊆
        baseLiterals alphabet parameters := by
    intro literal hLiteral
    exact
      (mem_baseLiterals_iff
        alphabet parameters literal).mpr
          (hEligible.2 literal hLiteral)
  rcases hNormalized.subperm hSubset with
    ⟨canonical, hPerm, hSublist⟩
  have hCanonicalWidth :
      canonical.length ≤
        parameters.maxClauseWidth := by
    rw [hPerm.length_eq]
    exact hEligible.1
  let representation : Representation D Γ :=
    canonical
  refine ⟨representation, ?_, hPerm⟩
  apply
    (mem_baseRepresentations_iff
      alphabet parameters representation).mpr
  exact ⟨hSublist, hCanonicalWidth⟩

/-
  Soundness: every emitted representation decodes to an
  exact member of the extensional base slice.
-/
theorem baseRepresentations_sound
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {representation : Representation D Γ}
    (hMember :
      representation ∈
        baseRepresentations alphabet parameters) :
    decode representation ∈
      (baseSlice alphabet parameters).clauses := by
  apply
    (DisjunctiveClause.mem_baseSlice_iff
      alphabet parameters
      (decode representation)).mpr
  exact
    ⟨representation,
      baseRepresentation_normalized
        alphabet parameters hMember,
      baseRepresentation_eligible
        alphabet parameters hMember,
      rfl⟩

/-
  Completeness: every formula in the extensional base slice
  is equivalent to a decoded emitted representation.

  Equivalence, rather than syntactic equality, accounts for
  the enumerator choosing one literal ordering.
-/
theorem baseRepresentations_complete_up_to_equiv
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (formula : Clause D Γ)
    (hMember :
      formula ∈
        (baseSlice alphabet parameters).clauses) :
    ∃ representation ∈
        baseRepresentations alphabet parameters,
      QFAssertExpr.equiv
        (decode representation) formula := by
  rcases
      (DisjunctiveClause.mem_baseSlice_iff
        alphabet parameters formula).mp hMember with
    ⟨literalList, hNormalized, hEligible, rfl⟩
  rcases
      baseRepresentations_cover
        alphabet parameters literalList
          hNormalized hEligible with
    ⟨representation, hMember, hSame⟩
  exact
    ⟨representation, hMember,
      representation.formula_equiv_of_sameLiterals
        hSame⟩

/-
  The eager decoded clause list inherits exact soundness.
-/
theorem baseClauses_sound
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    {formula : Clause D Γ}
    (hMember :
      formula ∈ baseClauses alphabet parameters) :
    formula ∈
      (baseSlice alphabet parameters).clauses := by
  rcases List.mem_map.mp hMember with
    ⟨representation, hRepresentation, rfl⟩
  exact
    baseRepresentations_sound
      alphabet parameters hRepresentation

/-
  The eager decoded clause list inherits completeness up to
  formula equivalence.
-/
theorem baseClauses_complete_up_to_equiv
    [LinearOrder A] [LinearOrder D]
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (formula : Clause D Γ)
    (hMember :
      formula ∈
        (baseSlice alphabet parameters).clauses) :
    ∃ emitted ∈ baseClauses alphabet parameters,
      QFAssertExpr.equiv emitted formula := by
  rcases
      baseRepresentations_complete_up_to_equiv
        alphabet parameters formula hMember with
    ⟨representation, hRepresentation, hEquiv⟩
  exact
    ⟨decode representation,
      List.mem_map.mpr
        ⟨representation, hRepresentation, rfl⟩,
      hEquiv⟩

end BaseSlice

end Enumerators

end Synthesis

end Whiel
