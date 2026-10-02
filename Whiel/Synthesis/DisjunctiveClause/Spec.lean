-- Author: Jesse Comer
import Whiel.Synthesis.Spec
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.List

/-
  Logical specification of disjunctive clauses.

  This module defines the checked clause syntax, its QF
  meaning, the finite enumeration alphabet and parameters,
  and the base-slice specification. Executable
  enumeration is separate.

  Main declarations:
    * `Term`, `Atom`, `Literal`, and `LiteralList`
    * `clauseClass` and `Slice`
    * `Alphabet` and `Parameters`
    * `baseSlice` and `mem_baseSlice_iff`
    * `LiteralList.formula_equiv_of_sameLiterals`
-/

------------------------------------------------------------
-- Checked Relational-Algebra Atoms
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The two supported atomic comparison relations. -/
inductive AtomKind
| equality
| containment
deriving DecidableEq, Repr

/-
  An RA term packaged with its checked output arity.

  This is the non-dependent form used by heterogeneous
  finite term collections.
-/
structure Term
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) where
  arity : Nat
  expr : RawRAExpr A D
  wellFormed :
    expr.arity? Γ = some arity
deriving DecidableEq

namespace Term

/- Recover the typed RA expression. -/
def typed
    (term : Term D Γ) :
    RAExpr D Γ term.arity where
  expr := term.expr
  wf := term.wellFormed

/- The nullary top base. -/
def top :
    Term D Γ where
  arity := 0
  expr := .top
  wellFormed := by
    simp [RawRAExpr.arity?]

/- The empty base at one arity. -/
def empty
    (arity : Nat) :
    Term D Γ where
  arity := arity
  expr := .empty arity
  wellFormed := by
    simp [RawRAExpr.arity?]

/- One schema-relation base. -/
def relation
    (relation : Γ.syms) :
    Term D Γ where
  arity := Γ.arity relation
  expr := .rel relation.1
  wellFormed := (RAExpr.rel relation).wf

/- One unary singleton base. -/
def singleton
    (constant : D) :
    Term D Γ where
  arity := 1
  expr := .single constant
  wellFormed := by
    simp [RawRAExpr.arity?]

end Term

/- Two raw RA expressions checked at one shared arity. -/
structure Atom
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) where
  kind : AtomKind
  arity : Nat
  left : RawRAExpr A D
  right : RawRAExpr A D
  leftWellFormed :
    left.arity? Γ = some arity
  rightWellFormed :
    right.arity? Γ = some arity
deriving DecidableEq

namespace Atom

/- Compare two checked terms of equal arity. -/
def ofTerms
    (kind : AtomKind)
    (left right : Term D Γ)
    (sameArity :
      left.arity = right.arity) :
    Atom D Γ where
  kind := kind
  arity := left.arity
  left := left.expr
  right := right.expr
  leftWellFormed := left.wellFormed
  rightWellFormed := by
    rw [sameArity]
    exact right.wellFormed

/- Build a checked equality atom. -/
def eq
    {n : Nat}
    (left right : RAExpr D Γ n) :
    Atom D Γ where
  kind := .equality
  arity := n
  left := left.expr
  right := right.expr
  leftWellFormed := left.wf
  rightWellFormed := right.wf

/- Build a checked containment atom. -/
def subset
    {n : Nat}
    (left right : RAExpr D Γ n) :
    Atom D Γ where
  kind := .containment
  arity := n
  left := left.expr
  right := right.expr
  leftWellFormed := left.wf
  rightWellFormed := right.wf

/- Recover the typed left expression. -/
def leftExpr
    (atom : Atom D Γ) :
    RAExpr D Γ atom.arity where
  expr := atom.left
  wf := atom.leftWellFormed

/- Recover the typed right expression. -/
def rightExpr
    (atom : Atom D Γ) :
    RAExpr D Γ atom.arity where
  expr := atom.right
  wf := atom.rightWellFormed

/- Interpret a checked atom as a QF assertion. -/
def formula
    (atom : Atom D Γ) :
    Clause D Γ :=
  match atom.kind with
  | .equality =>
      QFAssertExpr.eq atom.leftExpr atom.rightExpr
  | .containment =>
      QFAssertExpr.subset
        atom.leftExpr atom.rightExpr

end Atom

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Literals, Literal Lists, and Their Meaning
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Literal polarity. -/
inductive LiteralSign
| positive
| negative
deriving DecidableEq, Repr

/- A signed checked atom. -/
structure Literal
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) where
  sign : LiteralSign
  atom : Atom D Γ
deriving DecidableEq

namespace Literal

/- Interpret a literal as a QF assertion. -/
def formula
    (literal : Literal D Γ) :
    Clause D Γ :=
  match literal.sign with
  | .positive => literal.atom.formula
  | .negative =>
      QFAssertExpr.not literal.atom.formula

end Literal

/-
  An ordered finite serialization of literals.

  Normalization is a separate property, so executable
  realizations need not carry proofs in their data.
-/
abbrev LiteralList
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) :=
  List (Literal D Γ)

namespace LiteralList

/- Normalized literal lists contain no repeated literal. -/
def IsNormalized
    (literalList : LiteralList D Γ) :
    Prop :=
  literalList.Nodup

/- Interpret the literal list as a QF disjunction. -/
def formula
    (literalList : LiteralList D Γ) :
    Clause D Γ :=
  QFAssertExpr.orList
    (literalList.map Literal.formula)

@[simp] theorem formula_nil :
    formula ([] : LiteralList D Γ) =
      QFAssertExpr.«false» :=
  rfl

@[simp] theorem formula_singleton
    (literal : Literal D Γ) :
    formula ([literal] : LiteralList D Γ) =
      literal.formula :=
  rfl

/- The disjunction holds exactly when one literal holds. -/
@[simp] theorem formula_eval_iff
    (literalList : LiteralList D Γ)
    (I : Instance D Γ) :
    literalList.formula.eval I ↔
      ∃ literal ∈ literalList,
        literal.formula.eval I := by
  simp [formula]

/- Two lists have the same abstract literal set. -/
def SameLiterals
    (left right : LiteralList D Γ) :
    Prop :=
  left.Perm right

/- Two literal permutations have equivalent meanings. -/
theorem formula_equiv_of_perm
    {left right : LiteralList D Γ}
    (hPerm : left.Perm right) :
    QFAssertExpr.equiv
      left.formula right.formula := by
  constructor
  · intro I hLeft
    rw [formula_eval_iff] at hLeft ⊢
    rcases hLeft with
      ⟨literal, hMember, hLiteral⟩
    exact
      ⟨literal, hPerm.mem_iff.mp hMember,
        hLiteral⟩
  · intro I hRight
    rw [formula_eval_iff] at hRight ⊢
    rcases hRight with
      ⟨literal, hMember, hLiteral⟩
    exact
      ⟨literal, hPerm.mem_iff.mpr hMember,
        hLiteral⟩

/- Lists with the same literals have equivalent meanings. -/
theorem formula_equiv_of_sameLiterals
    {left right : LiteralList D Γ}
    (hSame : left.SameLiterals right) :
    QFAssertExpr.equiv
      left.formula right.formula :=
  formula_equiv_of_perm hSame

end LiteralList

/- Formulas represented by duplicate-free literal lists. -/
def clauseClass :
    ClauseClass D Γ :=
  { clause |
      ∃ literalList : LiteralList D Γ,
        literalList.IsNormalized ∧
          literalList.formula = clause }

/- A finite slice of the disjunctive-clause class. -/
abbrev Slice
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) :=
  (clauseClass : ClauseClass D Γ).Slice

@[simp] theorem mem_clauseClass_iff
    (clause : Clause D Γ) :
    clause ∈
        (clauseClass : ClauseClass D Γ) ↔
      ∃ literalList : LiteralList D Γ,
        literalList.IsNormalized ∧
          literalList.formula = clause :=
  Iff.rfl

theorem LiteralList.formula_mem_clauseClass
    (literalList : LiteralList D Γ)
    (hNormalized : literalList.IsNormalized) :
    literalList.formula ∈
      (clauseClass :
        ClauseClass D Γ) :=
  ⟨literalList, hNormalized, rfl⟩

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Finite Alphabets and Parameters
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Finite symbols available to one enumeration request. -/
structure Alphabet
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) where
  relations : Finset Γ.syms
  constants : Finset D
deriving DecidableEq

/- Relational-algebra base constructors. -/
inductive RABase
| top
| empty
| relation
| singleton
deriving DecidableEq, Repr

/- Non-base relational-algebra constructors. -/
inductive RAOperator
| selection
| projection
| product
| union
| difference
deriving DecidableEq, Repr

/-
  Inclusive parameters for a finite clause slice.

  The base-slice realization uses the base, atom, sign,
  empty-arity, and clause-width fields. `maxRAOps`,
  operator selection, and operator-specific bounds become
  active in the complete realization.

  Source relations are never filtered by `maxOutputArity`.
  That bound supplies additional empty arities now and
  bounds derived RA results in the complete realization.
  Selection conditions are bounded by their syntax-node
  count. Projections are bounded by output-length excess
  over their input arity.
-/
structure Parameters where
  enabledRABases : Finset RABase
  enabledRAOperators : Finset RAOperator
  enabledAtomKinds : Finset AtomKind
  enabledLiteralSigns : Finset LiteralSign
  maxRAOps : Nat
  maxSelectionConditionNodes : Nat
  maxProjectionExcess : Nat
  maxOutputArity : Nat
  maxClauseWidth : Nat
deriving DecidableEq

/-
  Arities contributed by enabled schema-relation bases.
-/
def relationArities
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Finset Nat :=
  if .relation ∈ parameters.enabledRABases then
    alphabet.relations.image Γ.arity
  else
    ∅

/-
  Empty bases use the explicit arity bound together with
  all enabled schema-relation arities.
-/
def emptyArities
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Finset Nat :=
  Finset.range (parameters.maxOutputArity + 1) ∪
    relationArities alphabet parameters

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Problem Alphabets
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- Constants in the source or normalized problem. -/
def programConstants
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    Finset D :=
  inputPre.constants ∪ inputCmd.constants ∪
    inputPost.constants ∪ P.loopPre.constants ∪
    P.loopGuard.constants ∪ P.loopBody.constants ∪
    P.loopPost.constants

namespace Alphabet

/- The complete finite alphabet of one problem. -/
def ofPreproc
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    Alphabet D P.outSchema where
  relations := P.outSchema.syms.attach
  constants := programConstants P

@[simp] theorem mem_relations_ofPreproc
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (relation : P.outSchema.syms) :
    relation ∈ (ofPreproc P).relations := by
  simp [ofPreproc]

@[simp] theorem mem_constants_ofPreproc_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (constant : D) :
    constant ∈ (ofPreproc P).constants ↔
      constant ∈ programConstants P :=
  Iff.rfl

end Alphabet

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Base-Slice Eligibility
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  A term is base-eligible when it is an enabled top, empty,
  schema-relation, or singleton base from this request.
-/
def Term.IsBaseEligible
    (term : Term D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Prop :=
  (.top ∈ parameters.enabledRABases ∧
      term = Term.top) ∨
    (.empty ∈ parameters.enabledRABases ∧
      ∃ arity ∈ emptyArities alphabet parameters,
        term = Term.empty arity) ∨
    (.relation ∈ parameters.enabledRABases ∧
      ∃ relation ∈ alphabet.relations,
        term = Term.relation relation) ∨
    (.singleton ∈ parameters.enabledRABases ∧
      ∃ constant ∈ alphabet.constants,
        term = Term.singleton constant)

/-
  An atom is base-eligible when it is an enabled comparison
  between equal-arity base-eligible terms.
-/
def Atom.IsBaseEligible
    (atom : Atom D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Prop :=
  ∃ kind,
    kind ∈ parameters.enabledAtomKinds ∧
      ∃ left,
        left.IsBaseEligible alphabet parameters ∧
          ∃ right,
            right.IsBaseEligible
              alphabet parameters ∧
              ∃ sameArity :
                  left.arity = right.arity,
                atom =
                  Atom.ofTerms kind left right
                    sameArity

/-
  A literal is base-eligible when its sign and atom are
  base-eligible.
-/
def Literal.IsBaseEligible
    (literal : Literal D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Prop :=
  literal.sign ∈
      parameters.enabledLiteralSigns ∧
    literal.atom.IsBaseEligible
      alphabet parameters

/-
  A literal list is base-eligible when it respects the width
  bound and contains only base-eligible literals.

  Normalization remains a separate property.
-/
def LiteralList.IsBaseEligible
    (literalList : LiteralList D Γ)
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Prop :=
  literalList.length ≤
      parameters.maxClauseWidth ∧
    ∀ literal ∈ literalList,
      literal.IsBaseEligible alphabet parameters

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Extensional Base Slice
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private theorem finite_baseEligibleTerms
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    {term : Term D Γ |
      term.IsBaseEligible alphabet parameters}.Finite := by
  let support : Set (Term D Γ) :=
    {Term.top} ∪
      Term.empty ''
        (↑(emptyArities
          alphabet parameters) : Set Nat) ∪
      Term.relation ''
        (↑alphabet.relations : Set Γ.syms) ∪
      Term.singleton ''
        (↑alphabet.constants : Set D)
  have hSupport : support.Finite :=
    (((Set.finite_singleton Term.top).union
      ((Set.finite_mem_finset
        (emptyArities alphabet parameters)).image
          Term.empty)).union
      ((Set.finite_mem_finset alphabet.relations).image
        Term.relation)).union
      ((Set.finite_mem_finset alphabet.constants).image
        Term.singleton)
  apply hSupport.subset
  intro term hEligible
  rcases hEligible with
    hTop | hEmpty | hRelation | hSingleton
  · exact
      Set.mem_union_left _
        (Set.mem_union_left _
          (Set.mem_union_left _ hTop.2))
  · rcases hEmpty with
      ⟨_, arity, hArity, rfl⟩
    exact
      Set.mem_union_left _
        (Set.mem_union_left _
          (Set.mem_union_right _
            ⟨arity, hArity, rfl⟩))
  · rcases hRelation with
      ⟨_, relation, hMember, rfl⟩
    exact
      Set.mem_union_left _
        (Set.mem_union_right _
          ⟨relation, hMember, rfl⟩)
  · rcases hSingleton with
      ⟨_, constant, hMember, rfl⟩
    exact
      Set.mem_union_right _
        ⟨constant, hMember, rfl⟩

private theorem finite_baseEligibleAtoms
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    {atom : Atom D Γ |
      atom.IsBaseEligible alphabet parameters}.Finite := by
  let EligibleTerm :=
    {term : Term D Γ //
      term.IsBaseEligible alphabet parameters}
  let EnabledKind :=
    {kind : AtomKind //
      kind ∈ parameters.enabledAtomKinds}
  let Witness :=
    {data : EnabledKind × EligibleTerm × EligibleTerm //
      data.2.1.val.arity =
        data.2.2.val.arity}
  let make : Witness → Atom D Γ := fun witness =>
    Atom.ofTerms witness.val.1.val
      witness.val.2.1.val witness.val.2.2.val
      witness.property
  letI : Finite EligibleTerm :=
    Set.finite_coe_iff.mpr
      (finite_baseEligibleTerms alphabet parameters)
  letI : Finite EnabledKind :=
    Set.finite_coe_iff.mpr
      (Set.finite_mem_finset
        parameters.enabledAtomKinds)
  letI : Finite Witness := inferInstance
  have hRange : (Set.range make).Finite := by
    simpa only [Set.image_univ] using
      (Set.finite_univ.image make)
  apply hRange.subset
  intro atom hEligible
  rcases hEligible with
    ⟨kind, hKind, left, hLeft, right, hRight,
      sameArity, rfl⟩
  refine
    ⟨⟨(⟨kind, hKind⟩, ⟨left, hLeft⟩,
      ⟨right, hRight⟩), sameArity⟩, ?_⟩
  rfl

private theorem finite_baseEligibleLiterals
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    {literal : Literal D Γ |
      literal.IsBaseEligible
        alphabet parameters}.Finite := by
  let EligibleAtom :=
    {atom : Atom D Γ //
      atom.IsBaseEligible alphabet parameters}
  let EnabledSign :=
    {sign : LiteralSign //
      sign ∈ parameters.enabledLiteralSigns}
  let Witness := EnabledSign × EligibleAtom
  let make : Witness → Literal D Γ := fun witness =>
    ⟨witness.1.val, witness.2.val⟩
  letI : Finite EligibleAtom :=
    Set.finite_coe_iff.mpr
      (finite_baseEligibleAtoms alphabet parameters)
  letI : Finite EnabledSign :=
    Set.finite_coe_iff.mpr
      (Set.finite_mem_finset
        parameters.enabledLiteralSigns)
  letI : Finite Witness := inferInstance
  have hRange : (Set.range make).Finite := by
    simpa only [Set.image_univ] using
      (Set.finite_univ.image make)
  apply hRange.subset
  rintro ⟨sign, atom⟩ ⟨hSign, hAtom⟩
  exact
    ⟨(⟨sign, hSign⟩, ⟨atom, hAtom⟩), rfl⟩

private theorem finite_baseEligibleLiteralLists
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    {literalList : LiteralList D Γ |
      literalList.IsBaseEligible
        alphabet parameters}.Finite := by
  let EligibleLiteral :=
    {literal : Literal D Γ //
      literal.IsBaseEligible alphabet parameters}
  let erase :
      List EligibleLiteral → LiteralList D Γ :=
    List.map Subtype.val
  let source : Set (List EligibleLiteral) :=
    {literalList |
      literalList.length ≤
        parameters.maxClauseWidth}
  letI : Finite EligibleLiteral :=
    Set.finite_coe_iff.mpr
      (finite_baseEligibleLiterals
        alphabet parameters)
  have hSource : source.Finite :=
    List.finite_length_le EligibleLiteral
      parameters.maxClauseWidth
  have hImage : (erase '' source).Finite :=
    hSource.image erase
  apply hImage.subset
  intro literalList hEligible
  let lifted : List EligibleLiteral :=
    literalList.attach.map fun item =>
      ⟨item.val,
        hEligible.2 item.val item.property⟩
  refine ⟨lifted, ?_, ?_⟩
  · change
      lifted.length ≤ parameters.maxClauseWidth
    simpa [lifted] using hEligible.1
  · simp [erase, lifted]

private def baseSliceSet
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Set (Clause D Γ) :=
  {formula |
    ∃ literalList : LiteralList D Γ,
      literalList.IsNormalized ∧
        literalList.IsBaseEligible
          alphabet parameters ∧
          literalList.formula = formula}

private theorem finite_baseSliceSet
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    (baseSliceSet alphabet parameters).Finite := by
  let source : Set (LiteralList D Γ) :=
    {literalList |
      literalList.IsNormalized ∧
        literalList.IsBaseEligible
          alphabet parameters}
  have hSource : source.Finite :=
    (finite_baseEligibleLiteralLists
      alphabet parameters).subset (by
        intro literalList hMember
        exact hMember.2)
  have hImage :
      (LiteralList.formula '' source).Finite :=
    hSource.image LiteralList.formula
  apply hImage.subset
  intro formula hFormula
  rcases hFormula with
    ⟨literalList, hNormalized, hEligible, rfl⟩
  exact
    ⟨literalList, ⟨hNormalized, hEligible⟩, rfl⟩

/-
  The finite set of all normalized, base-eligible
  disjunctive clauses.

  This definition contains no enumeration order or runtime
  representation. Executable enumerators prove
  correspondence with its membership specification.
-/
def baseSlice
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    Slice D Γ where
  clauses := baseSliceSet alphabet parameters
  finite := finite_baseSliceSet alphabet parameters
  subset_class := by
    rintro formula
      ⟨literalList, hNormalized, _, rfl⟩
    exact
      literalList.formula_mem_clauseClass hNormalized

/-
  Extensional membership in the base slice.

  The formula decoded from every normalized eligible literal
  ordering belongs to the slice. Executable enumerators may
  choose one representative from each permutation class.
-/
@[simp] theorem mem_baseSlice_iff
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (formula : Clause D Γ) :
    formula ∈
        (baseSlice alphabet parameters).clauses ↔
      ∃ literalList : LiteralList D Γ,
        literalList.IsNormalized ∧
          literalList.IsBaseEligible
            alphabet parameters ∧
            literalList.formula = formula := by
  simp [baseSlice, baseSliceSet]

end DisjunctiveClause

end Synthesis

end Whiel
