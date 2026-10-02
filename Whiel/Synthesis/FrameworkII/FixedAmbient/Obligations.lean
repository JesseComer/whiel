-- Author: Jesse Comer
import Whiel.Hoare.Concrete
import Whiel.Synthesis.FrameworkII.FixedAmbient.Task

/-
  Exact same-schema Framework-II obligations.

  For N retained clauses, every formula below is over the
  one ambient schema `Gamma`: N initialization VCs, N
  maintenance VCs, and one termination VC.
-/

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}
variable {body : Cmd D Gamma}

/- One checked clause and its assigned level. -/
structure LeveledClause
    (D : Type) [Domain D]
    (Gamma : UnnamedSchema WhielNames) where
  formula : QFAssertExpr D Gamma
  level : Nat

/- An ordered family of checked clauses. -/
structure LeveledFamily
    (D : Type) [Domain D]
    (Gamma : UnnamedSchema WhielNames) where
  clauses : List (LeveledClause D Gamma)

namespace LeveledFamily

/- Clauses at exactly one level, in family order. -/
def atLevel
    (family : LeveledFamily D Gamma)
    (level : Nat) : List (LeveledClause D Gamma) :=
  family.clauses.filter fun clause =>
    clause.level = level

/- Clauses strictly below one level. -/
def below
    (family : LeveledFamily D Gamma)
    (level : Nat) : List (LeveledClause D Gamma) :=
  family.clauses.filter fun clause =>
    clause.level < level

/- Clauses at or below one level. -/
def upTo
    (family : LeveledFamily D Gamma)
    (level : Nat) : List (LeveledClause D Gamma) :=
  family.clauses.filter fun clause =>
    clause.level <= level

/- Erase level metadata while preserving order. -/
def formulas
    (clauses : List (LeveledClause D Gamma)) :
    List (QFAssertExpr D Gamma) :=
  clauses.map fun clause => clause.formula

/- Semantic levels consumed by the Hoare rule. -/
def semanticLevels
    (family : LeveledFamily D Gamma) :
    Nat -> List (Assertion D Gamma) :=
  fun level =>
    (family.atLevel level).map fun clause =>
      clause.formula.eval

/- Every semantic member comes from one exact row. -/
theorem mem_semanticLevels_iff
    (family : LeveledFamily D Gamma)
    (level : Nat)
    (assertion : Assertion D Gamma) :
    assertion ∈ family.semanticLevels level ↔
      ∃ clause ∈ family.clauses,
        clause.level = level ∧
          clause.formula.eval = assertion := by
  constructor
  · intro hAssertion
    rcases List.mem_map.mp hAssertion with
      ⟨clause, hClause, hEval⟩
    have hFiltered := List.mem_filter.mp hClause
    exact ⟨clause, hFiltered.1,
      of_decide_eq_true hFiltered.2, hEval⟩
  · rintro ⟨clause, hClause, hLevel, hEval⟩
    apply List.mem_map.mpr
    exact ⟨clause,
      List.mem_filter.mpr
        ⟨hClause, decide_eq_true hLevel⟩,
      hEval⟩

end LeveledFamily

/- The exact prophecy premises for one candidate level. -/
structure ProphecyContext
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma) where
  level : Nat

namespace ProphecyContext

/- Lower rows retain the catalog order. -/
def orderedLowerClauses
    {task : Task body}
    {family : LeveledFamily D Gamma}
    {guard : Guard D Gamma}
    (context : ProphecyContext task family guard) :
    List (LeveledClause D Gamma) :=
  family.below context.level

/-
  Level zero has no terminal facts. Positive levels use
  the negated theta guard and theta of each lower row.
-/
def premises
    {task : Task body}
    {family : LeveledFamily D Gamma}
    {guard : Guard D Gamma}
    (context : ProphecyContext task family guard) :
    List (QFAssertExpr D Gamma) :=
  if context.level = 0 then
    []
  else
    QFAssertExpr.not (task.theta guard) ::
      (context.orderedLowerClauses.map fun clause =>
        task.theta clause.formula)

/- Conjunctive view of the separate premises. -/
def outFacts
    {task : Task body}
    {family : LeveledFamily D Gamma}
    {guard : Guard D Gamma}
    (context : ProphecyContext task family guard) :
    QFAssertExpr D Gamma :=
  QFAssertExpr.andList context.premises

/- Build the unique context at one level. -/
def build
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (level : Nat) : ProphecyContext task family guard :=
  ⟨level⟩

/- Level zero has no prophecy premise. -/
theorem premises_zero
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma) :
    (build task family guard 0).premises = [] := by
  rfl

/- The level-zero conjunction is true. -/
theorem outFacts_zero
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma) :
    (build task family guard 0).outFacts =
      QFAssertExpr.«true» := by
  rfl

/-
  The syntactic premises are exactly the semantic terminal
  facts used by the fixed-ambient Hoare theorem.
-/
theorem premises_eval_iff_prophecyBelow
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (level : Nat)
    (state : Instance D Gamma) :
    (∀ premise ∈
        (build task family guard level).premises,
      premise.eval state) ↔
      Hoare.FixedAmbientProphecy.prophecyBelow
        task.prophecyCollapse guard
          family.semanticLevels level state := by
  by_cases hZero : level = 0
  · subst level
    constructor
    · intro _
      exact
        Hoare.FixedAmbientProphecy.prophecyBelow_zero
          task.prophecyCollapse guard
            family.semanticLevels state
    · intro _ premise hPremise
      rw [premises_zero task family guard] at hPremise
      simp at hPremise
  · have hPositive : 0 < level :=
      Nat.pos_of_ne_zero hZero
    change
      (∀ premise ∈
        (if level = 0 then [] else
          QFAssertExpr.not (task.theta guard) ::
            ((family.below level).map fun clause =>
              task.theta clause.formula)),
        premise.eval state) <-> _
    rw [if_neg hZero]
    constructor
    · intro hFacts
      refine ⟨?_, ?_⟩
      · intro _
        have hNotTheta := hFacts
          (QFAssertExpr.not (task.theta guard))
          (by simp)
        intro hGuard
        apply hNotTheta
        exact (task.theta_eval_iff guard state).mpr
          hGuard
      · intro lower hLower assertion hAssertion
        rcases (family.mem_semanticLevels_iff
          lower assertion).mp hAssertion with
          ⟨clause, hClause, hLevel, hEval⟩
        subst assertion
        have hBelow :
            clause ∈ family.below level := by
          apply List.mem_filter.mpr
          exact ⟨hClause, decide_eq_true (by
            simpa [hLevel] using hLower)⟩
        have hTheta := hFacts
          (task.theta clause.formula)
          (by
            apply List.mem_cons.mpr
            apply Or.inr
            apply List.mem_map.mpr
            exact ⟨clause, hBelow, rfl⟩)
        exact (task.theta_eval_iff
          clause.formula state).mp hTheta
    · intro hProphecy formula hFormula
      simp only [List.mem_cons] at hFormula
      rcases hFormula with hGuard | hLower
      · subst formula
        intro hTheta
        apply hProphecy.1 hPositive
        exact (task.theta_eval_iff guard state).mp
          hTheta
      · rcases List.mem_map.mp hLower with
          ⟨clause, hClause, rfl⟩
        apply (task.theta_eval_iff
          clause.formula state).mpr
        have hRow : clause ∈ family.clauses :=
          (List.mem_filter.mp hClause).1
        have hLevel : clause.level < level :=
          of_decide_eq_true
            (List.mem_filter.mp hClause).2
        exact hProphecy.2 clause.level hLevel
          clause.formula.eval
          ((family.mem_semanticLevels_iff
            clause.level clause.formula.eval).mpr
              ⟨clause, hRow, rfl, rfl⟩)

/- The conjunction has the same exact semantics. -/
theorem outFacts_eval_iff_prophecyBelow
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (level : Nat)
    (state : Instance D Gamma) :
    (build task family guard level).outFacts.eval state ↔
      Hoare.FixedAmbientProphecy.prophecyBelow
        task.prophecyCollapse guard
          family.semanticLevels level state := by
  rw [outFacts, QFAssertExpr.andList_eval_iff]
  exact premises_eval_iff_prophecyBelow
    task family guard level state

end ProphecyContext

namespace LeveledFamily

/- Exact initialization job for one row. -/
def initVC
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard pre : QFAssertExpr D Gamma)
    (clause : LeveledClause D Gamma) :
    QFEntailment (D := D) Gamma where
  axioms :=
    pre ::
      (ProphecyContext.build task family guard
        clause.level).premises
  conjecture := clause.formula

/- Exact level-prefix maintenance job for one row. -/
def maintenanceVC
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (clause : LeveledClause D Gamma) :
    QFEntailment (D := D) Gamma where
  axioms :=
    formulas (family.upTo clause.level) ++
      (guard ::
        (ProphecyContext.build task family guard
          clause.level).premises)
  conjecture :=
    QFAssertExpr.wpLoopFree body hBody clause.formula

/- Collapse every row inside the same schema. -/
def collapsedPremises
    (task : Task body)
    (family : LeveledFamily D Gamma) :
    List (QFAssertExpr D Gamma) :=
  family.clauses.map fun clause =>
    task.collapseFormula clause.formula

/- Conjunctive view of all collapsed rows. -/
def collapsedCandidate
    (task : Task body)
    (family : LeveledFamily D Gamma) :
    QFAssertExpr D Gamma :=
  QFAssertExpr.andList
    (family.collapsedPremises task)

/- Exact same-schema termination job. -/
def terminationVC
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard post : QFAssertExpr D Gamma) :
    QFEntailment (D := D) Gamma where
  axioms :=
    QFAssertExpr.not guard ::
      family.collapsedPremises task
  conjecture := post

/-
  At a collapse fixed point, collapsed rows are exactly all
  clauses at all semantic levels.
-/
theorem collapsedPremises_eval_iff_holdsAt
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (state : Instance D Gamma)
    (hFixed : task.prophecyCollapse.collapse state =
      state) :
    (∀ premise ∈ family.collapsedPremises task,
      premise.eval state) ↔
      Hoare.FixedAmbientProphecy.holdsAt
        family.semanticLevels state := by
  constructor
  · intro hPremises level assertion hAssertion
    rcases (family.mem_semanticLevels_iff
      level assertion).mp hAssertion with
      ⟨clause, hClause, hLevel, hEval⟩
    subst level
    rw [← hEval]
    apply (task.collapseFormula_eval_iff_of_fixed
      clause.formula state hFixed).mp
    exact hPremises
      (task.collapseFormula clause.formula)
      (List.mem_map.mpr ⟨clause, hClause, rfl⟩)
  · intro hAll premise hPremise
    rcases List.mem_map.mp hPremise with
      ⟨clause, hClause, rfl⟩
    apply (task.collapseFormula_eval_iff_of_fixed
      clause.formula state hFixed).mpr
    exact hAll clause.level clause.formula.eval
      ((family.mem_semanticLevels_iff
        clause.level clause.formula.eval).mpr
          ⟨clause, hClause, rfl, rfl⟩)

/- Valid syntax proves semantic initialization. -/
theorem initObligation_of_valid
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard pre : QFAssertExpr D Gamma)
    (clause : LeveledClause D Gamma)
    (hValid : (family.initVC task guard pre clause).Valid) :
    Hoare.FixedAmbientProphecy.InitObligation
      task.prophecyCollapse guard family.semanticLevels
        pre.eval clause.level clause.formula.eval := by
  intro state hPre hProphecy
  apply hValid state
  intro premise hPremise
  simp only [initVC, List.mem_cons] at hPremise
  rcases hPremise with hPremise | hPremise
  · subst premise
    exact hPre
  · exact
      (ProphecyContext.premises_eval_iff_prophecyBelow
        task family guard clause.level state).mpr
          hProphecy premise hPremise

/- A valid prefix job proves the semantic step VC. -/
theorem stepObligation_of_valid
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (clause : LeveledClause D Gamma)
    (hValid :
      (family.maintenanceVC task guard hBody
        clause).Valid) :
    Hoare.FixedAmbientProphecy.StepObligation
      guard body task.prophecyCollapse
        family.semanticLevels clause.level
          clause.formula.eval := by
  intro state hLadder hGuard hProphecy
  have hSyntactic :
      (QFAssertExpr.wpLoopFree body hBody
        clause.formula).eval state := by
    apply hValid state
    intro premise hPremise
    simp only [maintenanceVC, List.mem_append]
      at hPremise
    rcases hPremise with hPrefix | hGuardOrFacts
    · rcases List.mem_map.mp hPrefix with
        ⟨row, hRow, rfl⟩
      have hRowInfo := List.mem_filter.mp hRow
      have hRowProphecy :=
        Hoare.FixedAmbientProphecy.prophecyBelow_mono
          task.prophecyCollapse guard
          family.semanticLevels
          (of_decide_eq_true hRowInfo.2) hProphecy
      exact hLadder row.level hRowProphecy
        row.formula.eval
        ((family.mem_semanticLevels_iff
          row.level row.formula.eval).mpr
            ⟨row, hRowInfo.1, rfl, rfl⟩)
    · simp only [List.mem_cons] at hGuardOrFacts
      rcases hGuardOrFacts with
        hGuardPremise | hFactsPremise
      · subst premise
        exact hGuard
      · exact
          (ProphecyContext.premises_eval_iff_prophecyBelow
            task family guard clause.level state).mpr
              hProphecy premise hFactsPremise
  exact
    (QFAssertExpr.wpLoopFree_eval_iff
      body hBody clause.formula state).mp hSyntactic

/- A valid collapse job proves semantic termination. -/
theorem termObligation_of_valid
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard post : QFAssertExpr D Gamma)
    (hValid :
      (family.terminationVC task guard post).Valid) :
    Hoare.FixedAmbientProphecy.TermObligation
      task.prophecyCollapse guard
        family.semanticLevels post.eval := by
  intro state hFixed hNotGuard hAll
  apply hValid state
  intro premise hPremise
  simp only [terminationVC, List.mem_cons] at hPremise
  rcases hPremise with hGuardPremise | hCollapsed
  · subst premise
    exact hNotGuard
  · exact
      (family.collapsedPremises_eval_iff_holdsAt
        task state hFixed).mpr hAll premise hCollapsed

end LeveledFamily

/- One certificate root, retaining its exact clause row. -/
inductive ValidityJob
    (D : Type) [Domain D]
    (Gamma : UnnamedSchema WhielNames)
| initialization (clause : LeveledClause D Gamma)
| maintenance (clause : LeveledClause D Gamma)
| termination

namespace LeveledFamily

/-
  The literal same-schema entailments, in certificate order:
  all initialization roots, all maintenance roots, then the
  single termination root.
-/
def entailments
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre post : QFAssertExpr D Gamma) :
    List (QFEntailment (D := D) Gamma) :=
  family.clauses.map
      (family.initVC task guard pre) ++
    family.clauses.map
      (family.maintenanceVC task guard hBody) ++
    [family.terminationVC task guard post]

/- The entailment list has exactly 2N+1 roots. -/
theorem entailments_length
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (pre post : QFAssertExpr D Gamma) :
    (family.entailments task guard hBody pre post).length =
      2 * family.clauses.length + 1 := by
  simp [entailments]
  omega

/- Every row contributes init and maintenance, then term. -/
def jobs
    (family : LeveledFamily D Gamma) :
    List (ValidityJob D Gamma) :=
  family.clauses.map ValidityJob.initialization ++
    family.clauses.map ValidityJob.maintenance ++
      [ValidityJob.termination]

/- N rows produce exactly 2N+1 roots. -/
theorem jobs_length
    (family : LeveledFamily D Gamma) :
    family.jobs.length =
      2 * family.clauses.length + 1 := by
  simp [jobs]
  omega

end LeveledFamily

end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Level Lists
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}

/- The placeholder row read past the end of a family. -/
instance : Inhabited (LeveledClause D Gamma) :=
  ⟨⟨QFAssertExpr.«true», 0⟩⟩

namespace LeveledFamily

/- Rows of consecutive levels, the first at `start`. -/
def rowsFrom (start : Nat) :
    List (List (QFAssertExpr D Gamma)) ->
      List (LeveledClause D Gamma)
| [] => []
| formulas :: rest =>
    formulas.map (fun formula => ⟨formula, start⟩) ++
      rowsFrom (start + 1) rest

/-
  The family of a level list: every formula in the outer
  entry at index `k` is a row at level `k`, in list order.
-/
def ofLevels
    (levels : List (List (QFAssertExpr D Gamma))) :
    LeveledFamily D Gamma :=
  ⟨rowsFrom 0 levels⟩

/- Row `i` of a family, in family order. -/
def row
    (family : LeveledFamily D Gamma)
    (i : Nat) : LeveledClause D Gamma :=
  family.clauses.getD i default

/- Rows from `start` are exactly the indexed formulas. -/
theorem mem_rowsFrom_iff
    (start : Nat)
    (levels : List (List (QFAssertExpr D Gamma)))
    (clause : LeveledClause D Gamma) :
    clause ∈ rowsFrom start levels ↔
      ∃ index formulas,
        levels[index]? = some formulas ∧
          clause.formula ∈ formulas ∧
            clause.level = start + index := by
  obtain ⟨formula, level⟩ := clause
  induction levels generalizing start with
  | nil => simp [rowsFrom]
  | cons formulas rest ih =>
      simp only [rowsFrom, List.mem_append, List.mem_map, ih]
      constructor
      · rintro (⟨_, hFormula, hRow⟩ |
          ⟨index, formulas', hIndex, hMem, hLevel⟩)
        · cases hRow
          exact ⟨0, formulas, rfl, hFormula, rfl⟩
        · exact ⟨index + 1, formulas', hIndex, hMem, by omega⟩
      · rintro ⟨index, formulas', hIndex, hMem, hLevel⟩
        cases index with
        | zero =>
            left
            simp only [List.getElem?_cons_zero,
              Option.some.injEq] at hIndex
            subst hIndex
            simp only [Nat.add_zero] at hLevel
            subst hLevel
            exact ⟨formula, hMem, rfl⟩
        | succ index =>
            right
            exact ⟨index, formulas', by simpa using hIndex,
              hMem, by omega⟩

/- Every row of a level list has the level of its entry. -/
theorem mem_ofLevels_iff
    (levels : List (List (QFAssertExpr D Gamma)))
    (clause : LeveledClause D Gamma) :
    clause ∈ (ofLevels levels).clauses ↔
      ∃ formulas,
        levels[clause.level]? = some formulas ∧
          clause.formula ∈ formulas := by
  change clause ∈ rowsFrom 0 levels ↔ _
  rw [mem_rowsFrom_iff]
  constructor
  · rintro ⟨index, formulas, hIndex, hMem, hLevel⟩
    rw [hLevel, Nat.zero_add]
    exact ⟨formulas, hIndex, hMem⟩
  · rintro ⟨formulas, hIndex, hMem⟩
    exact ⟨clause.level, formulas, hIndex, hMem,
      (Nat.zero_add _).symm⟩

end LeveledFamily

end FixedAmbient
end FrameworkII
end Synthesis
end Whiel
