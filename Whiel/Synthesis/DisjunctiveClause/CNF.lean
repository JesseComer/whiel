-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.Spec

/-
  Readable finite-CNF conversion for quantifier-free Whiel
  assertions.

  A CNF is a list of duplicate-free disjunctive clauses.
  Its meaning is the conjunction of the clause formulas.
  Conversion first pushes polarity through the input formula
  and distributes disjunction over conjunction. It then
  removes duplicate clauses.

  Main declarations:
    * `CNF.Form`
    * `CNF.clauses`
    * `CNF.formula_equiv`
    * `CNF.candidate`
    * `CNF.candidate_denote_equiv`
-/

------------------------------------------------------------
-- CNF Syntax and Meaning
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace CNF

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- A finite conjunction of disjunctive clauses. -/
abbrev Form
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) :=
  List (LiteralList D Γ)

/- Interpret a CNF as the conjunction of its clauses. -/
def formula
    (cnf : Form D Γ) :
    QFAssertExpr D Γ :=
  QFAssertExpr.andList
    (cnf.map LiteralList.formula)

/- CNF truth is member-wise clause truth. -/
@[simp] theorem formula_eval_iff
    (cnf : Form D Γ)
    (I : Instance D Γ) :
    (formula cnf).eval I ↔
      ∀ clause ∈ cnf, clause.formula.eval I := by
  simp [formula]

/- Appending CNFs conjoins their meanings. -/
@[simp] theorem formula_append_eval_iff
    (left right : Form D Γ)
    (I : Instance D Γ) :
    (formula (left ++ right)).eval I ↔
      (formula left).eval I ∧ (formula right).eval I := by
  rw [formula_eval_iff]
  constructor
  · intro h
    constructor
    · rw [formula_eval_iff]
      intro clause hMember
      exact h clause (List.mem_append_left _ hMember)
    · rw [formula_eval_iff]
      intro clause hMember
      exact h clause (List.mem_append_right _ hMember)
  · rintro ⟨hLeft, hRight⟩ clause hMember
    rw [List.mem_append] at hMember
    rcases hMember with hMember | hMember
    · exact (formula_eval_iff left I).mp hLeft
        clause hMember
    · exact (formula_eval_iff right I).mp hRight
        clause hMember

/- Removing duplicate clauses preserves CNF meaning. -/
@[simp] theorem formula_dedup_eval_iff
    (cnf : Form D Γ)
    (I : Instance D Γ) :
    (formula cnf.dedup).eval I ↔
      (formula cnf).eval I := by
  simp [formula_eval_iff]

end CNF

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Clause Disjunction
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace CNF

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Merge two clauses and remove repeated literals. -/
def mergeClauses
    (left right : LiteralList D Γ) :
    LiteralList D Γ :=
  (left ++ right).dedup

/- Every merged clause is normalized. -/
theorem mergeClauses_normalized
    (left right : LiteralList D Γ) :
    (mergeClauses left right).IsNormalized :=
  List.nodup_dedup _

/- Merging clauses disjoins their meanings. -/
@[simp] theorem mergeClauses_eval_iff
    (left right : LiteralList D Γ)
    (I : Instance D Γ) :
    (mergeClauses left right).formula.eval I ↔
      left.formula.eval I ∨ right.formula.eval I := by
  rw [LiteralList.formula_eval_iff,
    LiteralList.formula_eval_iff,
    LiteralList.formula_eval_iff]
  constructor
  · rintro ⟨literal, hMember, hLiteral⟩
    rw [mergeClauses, List.mem_dedup,
      List.mem_append] at hMember
    rcases hMember with hLeft | hRight
    · exact Or.inl ⟨literal, hLeft, hLiteral⟩
    · exact Or.inr ⟨literal, hRight, hLiteral⟩
  · rintro (⟨literal, hMember, hLiteral⟩ |
      ⟨literal, hMember, hLiteral⟩)
    · exact
        ⟨literal, by
          simp [mergeClauses, hMember], hLiteral⟩
    · exact
        ⟨literal, by
          simp [mergeClauses, hMember], hLiteral⟩

/- Distribute disjunction over two finite CNFs. -/
def disjoin
    (left right : Form D Γ) :
    Form D Γ :=
  left.flatMap fun leftClause =>
    right.map fun rightClause =>
      mergeClauses leftClause rightClause

@[simp] theorem mem_disjoin_iff
    {left right : Form D Γ}
    {clause : LiteralList D Γ} :
    clause ∈ disjoin left right ↔
      ∃ leftClause ∈ left,
        ∃ rightClause ∈ right,
          mergeClauses leftClause rightClause = clause := by
  simp [disjoin]

/- Every clause produced by distribution is normalized. -/
theorem disjoin_normalized
    (left right : Form D Γ)
    {clause : LiteralList D Γ}
    (hMember : clause ∈ disjoin left right) :
    clause.IsNormalized := by
  rw [mem_disjoin_iff] at hMember
  rcases hMember with
    ⟨leftClause, _, rightClause, _, rfl⟩
  exact mergeClauses_normalized leftClause rightClause

/- CNF distribution has the expected disjunctive meaning. -/
@[simp] theorem disjoin_eval_iff
    (left right : Form D Γ)
    (I : Instance D Γ) :
    (formula (disjoin left right)).eval I ↔
      (formula left).eval I ∨ (formula right).eval I := by
  constructor
  · intro hDisjoin
    by_cases hLeft : (formula left).eval I
    · exact Or.inl hLeft
    · apply Or.inr
      rw [formula_eval_iff] at hDisjoin ⊢
      have hWitness :
          ∃ leftClause ∈ left,
            ¬ leftClause.formula.eval I := by
        simpa [formula_eval_iff] using hLeft
      rcases hWitness with
        ⟨leftClause, hLeftMember, hLeftFalse⟩
      intro rightClause hRightMember
      have hMerged :=
        hDisjoin
          (mergeClauses leftClause rightClause)
          (mem_disjoin_iff.mpr
            ⟨leftClause, hLeftMember,
              rightClause, hRightMember, rfl⟩)
      exact
        (mergeClauses_eval_iff
          leftClause rightClause I).mp hMerged
          |>.resolve_left hLeftFalse
  · intro hEither
    rw [formula_eval_iff]
    intro clause hMember
    rw [mem_disjoin_iff] at hMember
    rcases hMember with
      ⟨leftClause, hLeftMember,
        rightClause, hRightMember, rfl⟩
    apply
      (mergeClauses_eval_iff
        leftClause rightClause I).mpr
    rcases hEither with hLeft | hRight
    · exact Or.inl
        ((formula_eval_iff left I).mp hLeft
          leftClause hLeftMember)
    · exact Or.inr
        ((formula_eval_iff right I).mp hRight
          rightClause hRightMember)

end CNF

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Structural Conversion
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace CNF

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The polarity under which a subformula is converted. -/
inductive Polarity
| positive
| negative
deriving DecidableEq, Repr

namespace Polarity

/- Reverse a conversion polarity. -/
def flip : Polarity → Polarity
| .positive => .negative
| .negative => .positive

end Polarity

/- Make one signed equality literal. -/
def equalityLiteral
    (polarity : Polarity)
    {n : Nat}
    (left right : RAExpr D Γ n) :
    Literal D Γ where
  sign :=
    match polarity with
    | .positive => .positive
    | .negative => .negative
  atom := Atom.eq left right

/- Make one signed containment literal. -/
def containmentLiteral
    (polarity : Polarity)
    {n : Nat}
    (left right : RAExpr D Γ n) :
    Literal D Γ where
  sign :=
    match polarity with
    | .positive => .positive
    | .negative => .negative
  atom := Atom.subset left right

/- A signed equality literal has its selected polarity. -/
@[simp] theorem equalityLiteral_eval_iff
    (polarity : Polarity)
    {n : Nat}
    (left right : RAExpr D Γ n)
    (I : Instance D Γ) :
    (equalityLiteral polarity left right).formula.eval I ↔
      match polarity with
      | .positive => left.eval I = right.eval I
      | .negative => left.eval I ≠ right.eval I := by
  cases polarity <;>
    rfl

/-
  A signed containment literal has its selected polarity.
-/
@[simp] theorem containmentLiteral_eval_iff
    (polarity : Polarity)
    {n : Nat}
    (left right : RAExpr D Γ n)
    (I : Instance D Γ) :
    (containmentLiteral polarity left
      right).formula.eval I ↔
      match polarity with
      | .positive => left.eval I ⊆ right.eval I
      | .negative => ¬ left.eval I ⊆ right.eval I := by
  cases polarity <;>
    rfl

/-
  Convert a formula under one polarity.

  Negation changes polarity. Positive conjunction and
  negative disjunction append clause lists. The dual cases
  distribute disjunction over conjunction.
-/
def ofFormula :
    Polarity → QFAssertExpr D Γ → Form D Γ
| .positive, .«true» => []
| .negative, .«true» => [[]]
| .positive, .«false» => [[]]
| .negative, .«false» => []
| polarity, .eq left right =>
    [[equalityLiteral polarity left right]]
| polarity, .subset left right =>
    [[containmentLiteral polarity left right]]
| .positive, .and left right =>
    ofFormula .positive left ++
      ofFormula .positive right
| .negative, .and left right =>
    disjoin (ofFormula .negative left)
      (ofFormula .negative right)
| .positive, .or left right =>
    disjoin (ofFormula .positive left)
      (ofFormula .positive right)
| .negative, .or left right =>
    ofFormula .negative left ++
      ofFormula .negative right
| polarity, .not formula =>
    ofFormula polarity.flip formula

/- Every raw converted clause is duplicate-free. -/
theorem ofFormula_normalized
    (polarity : Polarity)
    (input : QFAssertExpr D Γ)
    {clause : LiteralList D Γ}
    (hMember : clause ∈ ofFormula polarity input) :
    clause.IsNormalized := by
  induction input generalizing polarity clause with
  | «true» =>
      cases polarity with
      | positive => simp [ofFormula] at hMember
      | negative =>
          simp only [ofFormula, List.mem_singleton]
            at hMember
          subst clause
          simp [LiteralList.IsNormalized]
  | «false» =>
      cases polarity with
      | positive =>
          simp only [ofFormula, List.mem_singleton]
            at hMember
          subst clause
          simp [LiteralList.IsNormalized]
      | negative => simp [ofFormula] at hMember
  | eq left right =>
      cases polarity <;>
        simp only [ofFormula, List.mem_singleton]
          at hMember <;>
        subst clause <;>
        simp [LiteralList.IsNormalized]
  | subset left right =>
      cases polarity <;>
        simp only [ofFormula, List.mem_singleton]
          at hMember <;>
        subst clause <;>
        simp [LiteralList.IsNormalized]
  | and left right leftIH rightIH =>
      cases polarity with
      | positive =>
          simp only [ofFormula, List.mem_append] at hMember
          rcases hMember with hLeft | hRight
          · exact leftIH .positive hLeft
          · exact rightIH .positive hRight
      | negative =>
          exact disjoin_normalized _ _ hMember
  | or left right leftIH rightIH =>
      cases polarity with
      | positive =>
          exact disjoin_normalized _ _ hMember
      | negative =>
          simp only [ofFormula, List.mem_append] at hMember
          rcases hMember with hLeft | hRight
          · exact leftIH .negative hLeft
          · exact rightIH .negative hRight
  | not formula ih =>
      simp only [ofFormula] at hMember
      exact ih polarity.flip hMember

/- Conversion under a polarity has the expected meaning. -/
@[simp] theorem ofFormula_eval_iff
    (polarity : Polarity)
    (input : QFAssertExpr D Γ)
    (I : Instance D Γ) :
    (formula (ofFormula polarity input)).eval I ↔
      match polarity with
      | .positive => input.eval I
      | .negative => ¬ input.eval I := by
  induction input generalizing polarity with
  | «true» =>
      cases polarity <;>
        simp [ofFormula, formula]
  | «false» =>
      cases polarity <;>
        simp [ofFormula, formula]
  | eq left right =>
      cases polarity <;>
        simp [ofFormula, formula]
  | subset left right =>
      cases polarity <;>
        simp [ofFormula, formula]
  | and left right leftIH rightIH =>
      cases polarity with
      | positive =>
          rw [ofFormula, formula_append_eval_iff,
            leftIH .positive, rightIH .positive]
          rfl
      | negative =>
          rw [ofFormula, disjoin_eval_iff,
            leftIH .negative, rightIH .negative]
          simp only [Guard.eval_and_iff]
          tauto
  | or left right leftIH rightIH =>
      cases polarity with
      | positive =>
          rw [ofFormula, disjoin_eval_iff,
            leftIH .positive, rightIH .positive]
          rfl
      | negative =>
          rw [ofFormula, formula_append_eval_iff,
            leftIH .negative, rightIH .negative]
          simp only [Guard.eval_or_iff]
          tauto
  | not input ih =>
      cases polarity with
      | positive =>
          rw [ofFormula, Polarity.flip, ih .negative]
          rfl
      | negative =>
          rw [ofFormula, Polarity.flip, ih .positive]
          simp only [Guard.eval_not_iff]
          tauto

/- The public conversion also removes duplicate clauses. -/
def clauses
    (input : QFAssertExpr D Γ) :
    Form D Γ :=
  (ofFormula .positive input).dedup

/- Public CNF output contains no repeated clause. -/
theorem clauses_nodup
    (input : QFAssertExpr D Γ) :
    (clauses input).Nodup :=
  List.nodup_dedup _

/- Every public CNF clause is normalized. -/
theorem clauses_normalized
    (input : QFAssertExpr D Γ)
    {clause : LiteralList D Γ}
    (hMember : clause ∈ clauses input) :
    clause.IsNormalized := by
  apply ofFormula_normalized .positive input
  simpa [clauses] using hMember

/- The converted CNF formula is equivalent to the input. -/
theorem formula_equiv
    (input : QFAssertExpr D Γ) :
    QFAssertExpr.equiv
      (formula (clauses input)) input := by
  rw [QFAssertExpr.equiv_iff_eval_iff]
  intro I
  simpa [clauses] using
    (ofFormula_eval_iff .positive input I)

/- Every converted clause belongs to the declared class. -/
theorem formula_mem_clauseClass
    (input : QFAssertExpr D Γ)
    {clause : LiteralList D Γ}
    (hMember : clause ∈ clauses input) :
    clause.formula ∈
      (clauseClass : ClauseClass D Γ) :=
  clause.formula_mem_clauseClass
    (clauses_normalized input hMember)

end CNF

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Syntactic Support Preservation
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace CNF

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Equality literals use exactly their source atom support.
-/
@[simp] theorem equalityLiteral_symbols
    (polarity : Polarity)
    {n : Nat}
    (left right : RAExpr D Γ n) :
    (equalityLiteral polarity left right).formula.symbols =
      (QFAssertExpr.eq left right).symbols := by
  cases polarity <;>
    rfl

@[simp] theorem equalityLiteral_constants
    (polarity : Polarity)
    {n : Nat}
    (left right : RAExpr D Γ n) :
    (equalityLiteral polarity left
      right).formula.constants =
      (QFAssertExpr.eq left right).constants := by
  cases polarity <;>
    rfl

/-
  Containment literals use exactly their source atom
  support.
-/
@[simp] theorem containmentLiteral_symbols
    (polarity : Polarity)
    {n : Nat}
    (left right : RAExpr D Γ n) :
    (containmentLiteral polarity left
      right).formula.symbols =
      (QFAssertExpr.subset left right).symbols := by
  cases polarity <;>
    rfl

@[simp] theorem containmentLiteral_constants
    (polarity : Polarity)
    {n : Nat}
    (left right : RAExpr D Γ n) :
    (containmentLiteral polarity left
      right).formula.constants =
      (QFAssertExpr.subset left right).constants := by
  cases polarity <;>
    rfl

namespace LiteralList

/-
  Every literal uses only support from one source formula.
-/
def UsesOnly
    (clause : LiteralList D Γ)
    (input : QFAssertExpr D Γ) : Prop :=
  ∀ literal ∈ clause,
    literal.formula.symbols ⊆ input.symbols ∧
      literal.formula.constants ⊆ input.constants

namespace UsesOnly

/- Enlarge the permitted source support. -/
theorem mono
    {clause : LiteralList D Γ}
    {input output : QFAssertExpr D Γ}
    (hUses : LiteralList.UsesOnly clause input)
    (hSymbols : input.symbols ⊆ output.symbols)
    (hConstants : input.constants ⊆ output.constants) :
    LiteralList.UsesOnly clause output := by
  intro literal hMember
  exact
    ⟨Finset.Subset.trans
        (hUses literal hMember).1 hSymbols,
      Finset.Subset.trans
        (hUses literal hMember).2 hConstants⟩

end UsesOnly

private theorem symbols_orList_subset
    (formulas : List (QFAssertExpr D Γ))
    (bound : Finset A)
    (hFormulas :
      ∀ formula ∈ formulas,
        formula.symbols ⊆ bound) :
    (QFAssertExpr.orList formulas).symbols ⊆ bound := by
  induction formulas with
  | nil =>
      simp [QFAssertExpr.orList, Guard.symbols]
  | cons formula formulas ih =>
      cases formulas with
      | nil =>
          simpa [QFAssertExpr.orList] using
            hFormulas formula (by simp)
      | cons next rest =>
          intro symbol hSymbol
          simp only [QFAssertExpr.orList, Guard.symbols,
            Finset.mem_union] at hSymbol
          rcases hSymbol with hHead | hTail
          · exact hFormulas formula (by simp) hHead
          · apply ih
            · intro item hItem
              exact hFormulas item (by simp [hItem])
            · exact hTail

private theorem constants_orList_subset
    (formulas : List (QFAssertExpr D Γ))
    (bound : Finset D)
    (hFormulas :
      ∀ formula ∈ formulas,
        formula.constants ⊆ bound) :
    (QFAssertExpr.orList formulas).constants ⊆ bound := by
  induction formulas with
  | nil =>
      simp [QFAssertExpr.orList, Guard.constants]
  | cons formula formulas ih =>
      cases formulas with
      | nil =>
          simpa [QFAssertExpr.orList] using
            hFormulas formula (by simp)
      | cons next rest =>
          intro constant hConstant
          simp only [QFAssertExpr.orList, Guard.constants,
            Finset.mem_union] at hConstant
          rcases hConstant with hHead | hTail
          · exact hFormulas formula (by simp) hHead
          · apply ih
            · intro item hItem
              exact hFormulas item (by simp [hItem])
            · exact hTail

/-
  A supported clause formula introduces no source symbol.
-/
theorem formula_symbols_subset
    {clause : LiteralList D Γ}
    {input : QFAssertExpr D Γ}
    (hUses : UsesOnly clause input) :
    clause.formula.symbols ⊆ input.symbols := by
  apply symbols_orList_subset
  intro formula hFormula
  rw [List.mem_map] at hFormula
  rcases hFormula with
    ⟨literal, hLiteral, rfl⟩
  exact (hUses literal hLiteral).1

/- A supported clause formula introduces no constant. -/
theorem formula_constants_subset
    {clause : LiteralList D Γ}
    {input : QFAssertExpr D Γ}
    (hUses : UsesOnly clause input) :
    clause.formula.constants ⊆ input.constants := by
  apply constants_orList_subset
  intro formula hFormula
  rw [List.mem_map] at hFormula
  rcases hFormula with
    ⟨literal, hLiteral, rfl⟩
  exact (hUses literal hLiteral).2

end LiteralList

/- Merging clauses preserves a common support bound. -/
theorem mergeClauses_usesOnly
    {left right : LiteralList D Γ}
    {input : QFAssertExpr D Γ}
    (hLeft : LiteralList.UsesOnly left input)
    (hRight : LiteralList.UsesOnly right input) :
    LiteralList.UsesOnly
      (mergeClauses left right) input := by
  intro literal hMember
  rw [mergeClauses, List.mem_dedup,
    List.mem_append] at hMember
  rcases hMember with hMember | hMember
  · exact hLeft literal hMember
  · exact hRight literal hMember

/- Every converted literal comes from the input formula. -/
theorem ofFormula_usesOnly
    (polarity : Polarity)
    (input : QFAssertExpr D Γ)
    {clause : LiteralList D Γ}
    (hMember : clause ∈ ofFormula polarity input) :
    LiteralList.UsesOnly clause input := by
  induction input generalizing polarity clause with
  | «true» =>
      cases polarity with
      | positive => simp [ofFormula] at hMember
      | negative =>
          simp only [ofFormula, List.mem_singleton]
            at hMember
          subst clause
          simp [LiteralList.UsesOnly]
  | «false» =>
      cases polarity with
      | positive =>
          simp only [ofFormula, List.mem_singleton]
            at hMember
          subst clause
          simp [LiteralList.UsesOnly]
      | negative => simp [ofFormula] at hMember
  | eq left right =>
      cases polarity <;>
        simp only [ofFormula, List.mem_singleton]
          at hMember <;>
        subst clause <;>
        simp [LiteralList.UsesOnly]
  | subset left right =>
      cases polarity <;>
        simp only [ofFormula, List.mem_singleton]
          at hMember <;>
        subst clause <;>
        simp [LiteralList.UsesOnly]
  | and left right leftIH rightIH =>
      cases polarity with
      | positive =>
          simp only [ofFormula, List.mem_append] at hMember
          rcases hMember with hMember | hMember
          · apply LiteralList.UsesOnly.mono
              (leftIH .positive hMember)
            · intro symbol hSymbol
              simp [Guard.symbols, hSymbol]
            · intro constant hConstant
              simp [Guard.constants, hConstant]
          · apply LiteralList.UsesOnly.mono
              (rightIH .positive hMember)
            · intro symbol hSymbol
              simp [Guard.symbols, hSymbol]
            · intro constant hConstant
              simp [Guard.constants, hConstant]
      | negative =>
          simp only [ofFormula] at hMember
          rw [mem_disjoin_iff] at hMember
          rcases hMember with
            ⟨leftClause, hLeft,
              rightClause, hRight, rfl⟩
          apply mergeClauses_usesOnly
          · apply LiteralList.UsesOnly.mono
              (leftIH .negative hLeft)
            · intro symbol hSymbol
              simp [Guard.symbols, hSymbol]
            · intro constant hConstant
              simp [Guard.constants, hConstant]
          · apply LiteralList.UsesOnly.mono
              (rightIH .negative hRight)
            · intro symbol hSymbol
              simp [Guard.symbols, hSymbol]
            · intro constant hConstant
              simp [Guard.constants, hConstant]
  | or left right leftIH rightIH =>
      cases polarity with
      | positive =>
          simp only [ofFormula] at hMember
          rw [mem_disjoin_iff] at hMember
          rcases hMember with
            ⟨leftClause, hLeft,
              rightClause, hRight, rfl⟩
          apply mergeClauses_usesOnly
          · apply LiteralList.UsesOnly.mono
              (leftIH .positive hLeft)
            · intro symbol hSymbol
              simp [Guard.symbols, hSymbol]
            · intro constant hConstant
              simp [Guard.constants, hConstant]
          · apply LiteralList.UsesOnly.mono
              (rightIH .positive hRight)
            · intro symbol hSymbol
              simp [Guard.symbols, hSymbol]
            · intro constant hConstant
              simp [Guard.constants, hConstant]
      | negative =>
          simp only [ofFormula, List.mem_append] at hMember
          rcases hMember with hMember | hMember
          · apply LiteralList.UsesOnly.mono
              (leftIH .negative hMember)
            · intro symbol hSymbol
              simp [Guard.symbols, hSymbol]
            · intro constant hConstant
              simp [Guard.constants, hConstant]
          · apply LiteralList.UsesOnly.mono
              (rightIH .negative hMember)
            · intro symbol hSymbol
              simp [Guard.symbols, hSymbol]
            · intro constant hConstant
              simp [Guard.constants, hConstant]
  | not formula ih =>
      simp only [ofFormula] at hMember
      simpa [LiteralList.UsesOnly, Guard.symbols,
        Guard.constants] using
          ih polarity.flip hMember

/- Public conversion preserves the input support bound. -/
theorem clauses_useOnlyInput
    (input : QFAssertExpr D Γ)
    {clause : LiteralList D Γ}
    (hMember : clause ∈ clauses input) :
    LiteralList.UsesOnly clause input := by
  apply ofFormula_usesOnly .positive input
  simpa [clauses] using hMember

end CNF

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Finite Candidate View
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace CNF

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Materialize converted clause formulas as a Candidate.
-/
def candidate
    (input : QFAssertExpr D Γ) :
    Candidate D Γ :=
  ((clauses input).map LiteralList.formula).toFinset

/- Candidate membership comes from one converted clause. -/
@[simp] theorem mem_candidate_iff
    (input : QFAssertExpr D Γ)
    (formula : Clause D Γ) :
    formula ∈ candidate input ↔
      ∃ clause ∈ clauses input,
        clause.formula = formula := by
  simp [candidate]

/-
  Every materialized candidate member belongs to the class.
-/
theorem candidate_subset_clauseClass
    (input : QFAssertExpr D Γ) :
    ∀ formula ∈ candidate input,
      formula ∈
        (clauseClass : ClauseClass D Γ) := by
  intro formula hMember
  rw [mem_candidate_iff] at hMember
  rcases hMember with
    ⟨clause, hClause, rfl⟩
  exact formula_mem_clauseClass input hClause

/- Candidate members introduce no symbols or constants. -/
theorem candidate_member_support
    (input : QFAssertExpr D Γ)
    {formula : Clause D Γ}
    (hMember : formula ∈ candidate input) :
    formula.symbols ⊆ input.symbols ∧
      formula.constants ⊆ input.constants := by
  rw [mem_candidate_iff] at hMember
  rcases hMember with
    ⟨clause, hClause, rfl⟩
  have hUses := clauses_useOnlyInput input hClause
  exact
    ⟨LiteralList.formula_symbols_subset hUses,
      LiteralList.formula_constants_subset hUses⟩

/- Candidate denotation is the CNF formula meaning. -/
@[simp] theorem candidate_denote_iff
    (input : QFAssertExpr D Γ)
    (I : Instance D Γ) :
    (candidate input).denote I ↔
      (formula (clauses input)).eval I := by
  simp [candidate, Candidate.denote, formula_eval_iff]

/-
  Every QF assertion has an equivalent finite CNF candidate.
-/
theorem candidate_denote_equiv
    (input : QFAssertExpr D Γ) :
    Assertion.equiv
      (candidate input).denote input.eval := by
  constructor
  · intro I hCandidate
    exact
      (formula_equiv input).1 I
        ((candidate_denote_iff input I).mp
          hCandidate)
  · intro I hInput
    apply (candidate_denote_iff input I).mpr
    exact (formula_equiv input).2 I hInput

end CNF

end DisjunctiveClause

end Synthesis

end Whiel
