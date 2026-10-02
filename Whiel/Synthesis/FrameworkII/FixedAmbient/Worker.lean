-- Author: Jesse Comer
import Whiel.Synthesis.FrameworkII.FixedAmbient.Components
import Whiel.Synthesis.FrameworkII.FixedAmbient.Precondition
import Whiel.Synthesis.FrameworkII.Refutation
import Whiel.Vampire.SolverName.Concrete

/-
  Typed worker operations for fixed-ambient Framework II.

  A compiled task keeps these values behind its wire
  callbacks. Rust identifies rows and requests operations;
  Lean reconstructs every clause and exact entailment over
  the lifted loop triple of the computed prophecy schema.
-/

namespace Whiel

namespace Synthesis

namespace FrameworkII

namespace FixedAmbient

open Concrete

open Runtime

variable {Gamma : UnnamedSchema WhielNames}

/- One catalog row after Lean clause admission. -/
structure CatalogRow
    (Gamma : UnnamedSchema WhielNames) where
  clauseId : Nat
  level : Nat
  clause : Clause Gamma

/- One typed snapshot of the Rust-owned core. -/
structure Snapshot
    (Gamma : UnnamedSchema WhielNames) where
  rows : List (CatalogRow Gamma)

namespace Snapshot

/- Forget runtime row metadata to form the proof family. -/
def family
    (snapshot : Snapshot Gamma) :
    LeveledFamily Data Gamma :=
  ⟨snapshot.rows.map fun row =>
    ⟨row.clause.formula, row.level⟩⟩

/- Locate one catalog row by its opaque numeric ID. -/
def findRow?
    (snapshot : Snapshot Gamma)
    (clauseId : Nat) : Option (CatalogRow Gamma) :=
  snapshot.rows.find? fun row =>
    row.clauseId == clauseId

end Snapshot

/- Exact selector for one of the `2N+1` jobs. -/
inductive ObligationSelector where
| initialization (clauseId : Nat)
| maintenance (clauseId : Nat)
| termination
deriving DecidableEq, Repr

/- One selected entailment reconstructed by Lean. -/
structure BuiltObligation
    (Gamma : UnnamedSchema WhielNames) where
  selector : ObligationSelector
  entailment : QFEntailment (D := Data) Gamma

/- Build the prophecy context used at one level. -/
def buildContext
    (loop : Hoare.LoopTriple Data Gamma)
    (task : Task loop.body)
    (snapshot : Snapshot Gamma)
    (level : Nat) :
    ProphecyContext task snapshot.family loop.guard :=
  ProphecyContext.build task snapshot.family
    loop.guard level

/- Reconstruct exactly one requested proof obligation. -/
def buildObligation
    (loop : Hoare.LoopTriple Data Gamma)
    (task : Task loop.body)
    (snapshot : Snapshot Gamma)
    (selector : ObligationSelector) :
    Except String (BuiltObligation Gamma) :=
  match selector with
  | .initialization clauseId =>
      match snapshot.findRow? clauseId with
      | none => .error "unknown initialization clause ID"
      | some row =>
          .ok
            { selector := selector
              entailment := snapshot.family.initVC task
                loop.guard loop.pre
                  ⟨row.clause.formula, row.level⟩ }
  | .maintenance clauseId =>
      match snapshot.findRow? clauseId with
      | none => .error "unknown maintenance clause ID"
      | some row =>
          .ok
            { selector := selector
              entailment :=
                snapshot.family.maintenanceVC task
                  loop.guard loop.body_loopFree
                    ⟨row.clause.formula, row.level⟩ }
  | .termination =>
      .ok
        { selector := selector
          entailment := snapshot.family.terminationVC task
            loop.guard loop.post }

/- Construct every exact job in stable `2N+1` order. -/
def buildAllObligations
    (loop : Hoare.LoopTriple Data Gamma)
    (task : Task loop.body)
    (snapshot : Snapshot Gamma) :
    List (BuiltObligation Gamma) :=
  let family := snapshot.family
  let initializations := snapshot.rows.map fun row =>
    { selector :=
        ObligationSelector.initialization row.clauseId
      entailment := family.initVC task loop.guard
        loop.pre ⟨row.clause.formula, row.level⟩ }
  let maintenances := snapshot.rows.map fun row =>
    { selector :=
        ObligationSelector.maintenance row.clauseId
      entailment := family.maintenanceVC task
        loop.guard loop.body_loopFree
          ⟨row.clause.formula, row.level⟩ }
  initializations ++ maintenances ++
    [ { selector := .termination
        entailment := family.terminationVC task
          loop.guard loop.post } ]

/- The worker materializes exactly `2N+1` obligations. -/
theorem buildAllObligations_length
    (loop : Hoare.LoopTriple Data Gamma)
    (task : Task loop.body)
    (snapshot : Snapshot Gamma) :
    (buildAllObligations loop task snapshot).length =
      2 * snapshot.rows.length + 1 := by
  simp [buildAllObligations]
  omega

/- Collapse one retained core within the ambient schema. -/
def collapseCore
    (loop : Hoare.LoopTriple Data Gamma)
    (task : Task loop.body)
    (snapshot : Snapshot Gamma) :
    List (Nat × QFAssertExpr Data Gamma) ×
      QFAssertExpr Data Gamma :=
  let rows := snapshot.rows.map fun row =>
    (row.clauseId,
      task.collapseFormula row.clause.formula)
  (rows, snapshot.family.collapsedCandidate task)

------------------------------------------------------------
-- Solver Preparation
------------------------------------------------------------

/- Proof-connected solver payload for one exact job. -/
structure PreparedEntailment
    (Gamma : UnnamedSchema WhielNames) where
  entailment : QFEntailment (D := Data) Gamma
  axiomBodies : List PreparedBodyData
  conjectureBody : PreparedBodyData
  support : PreparedSupportData

private def prepareFormulaBodies
    (env : Vampire.TPTP.NameEnv WhielNames Data)
    (role : String) : Nat ->
      List (QFAssertExpr Data Gamma) ->
        Option (List PreparedBodyData)
| _, [] => some []
| index, formula :: formulas => do
    let source : SolverBodySource Data Gamma :=
      .qf
        ("framework_ii.fixed_ambient." ++ role ++
          "." ++ toString index)
        formula
    let prepared ← prepareBody? env source
    let rest ← prepareFormulaBodies env role
      (index + 1) formulas
    pure (prepared.toData :: rest)

/- Prepare every TPTP body from one Lean-built job. -/
def prepareEntailment?
    (env : Vampire.TPTP.NameEnv WhielNames Data)
    (built : BuiltObligation Gamma) :
    Option (PreparedEntailment Gamma) := do
  let axiomBodies ← prepareFormulaBodies env "axiom"
    0 built.entailment.axioms
  let conjectureSource : SolverBodySource Data Gamma :=
    .qf "framework_ii.fixed_ambient.conjecture"
      built.entailment.conjecture
  let conjectureBody ←
    prepareBody? env conjectureSource
  let support ← prepareSupportBlock? env Gamma
    built.entailment.constants
  pure
    { entailment := built.entailment
      axiomBodies := axiomBodies
      conjectureBody := conjectureBody.toData
      support := support.toData }

------------------------------------------------------------
-- Axiom Role Tags
------------------------------------------------------------

/-
  The exact role of one emitted axiom, tying it back to the
  `Obligations.lean` construction that produced it:
  `initVC`'s `pre :: premises`, `maintenanceVC`'s
  `formulas (upTo level) ++ guard :: premises`, `premises`'s
  `not (theta guard) :: below.map theta`, and
  `terminationVC`'s `not guard :: collapsedPremises`.
-/
inductive AxiomRole where
| pre
| guard
| notThetaGuard
| plain
| theta
| notGuard
| collapsed
| support
deriving DecidableEq, Repr

namespace AxiomRole

/- Stable wire spelling of one axiom role. -/
def wireTag : AxiomRole -> String
| .pre => "pre"
| .guard => "guard"
| .notThetaGuard => "not_theta_guard"
| .plain => "plain"
| .theta => "theta"
| .notGuard => "not_guard"
| .collapsed => "collapsed"
| .support => "support"

end AxiomRole

/-
  One tagged axiom: its role, and the admitted clause
  identity when the role names a clause row.
-/
structure AxiomTag
    (Gamma : UnnamedSchema WhielNames) where
  role : AxiomRole
  identity : Option Lean.Json

/- Catalog rows strictly below one level, in row order. -/
def belowCatalogRows
    (snapshot : Snapshot Gamma)
    (level : Nat) : List (CatalogRow Gamma) :=
  snapshot.rows.filter fun row => row.level < level

/- Catalog rows at or below one level, in row order. -/
def uptoCatalogRows
    (snapshot : Snapshot Gamma)
    (level : Nat) : List (CatalogRow Gamma) :=
  snapshot.rows.filter fun row => row.level <= level

/-
  The exact axiom-role table for one selected job, in the
  same emission order `buildObligation` uses for
  `entailment.axioms`. Every row-derived filter mirrors the
  matching `LeveledFamily.below`/`upTo` filter over
  `snapshot.family`, which is the same predicate over the
  same list up to erasing each row's clause to a formula, so
  the table has exactly one entry per emitted axiom.
-/
def axiomTagsFor
    (snapshot : Snapshot Gamma)
    (selector : ObligationSelector) :
    Except String (List (AxiomTag Gamma)) :=
  match selector with
  | .initialization clauseId =>
      match snapshot.findRow? clauseId with
      | none => .error "unknown initialization clause ID"
      | some row =>
          .ok <|
            ({ role := .pre, identity := none } :
              AxiomTag Gamma) ::
              if row.level = 0 then []
              else
                { role := .notThetaGuard, identity := none } ::
                  (belowCatalogRows snapshot row.level).map
                    fun lower =>
                      { role := .theta
                        identity :=
                          some lower.clause.identityJson }
  | .maintenance clauseId =>
      match snapshot.findRow? clauseId with
      | none => .error "unknown maintenance clause ID"
      | some row =>
          .ok <|
            ((uptoCatalogRows snapshot row.level).map
                fun upto =>
                  ({ role := .plain
                     identity :=
                       some upto.clause.identityJson } :
                    AxiomTag Gamma)) ++
              ({ role := .guard, identity := none } ::
                if row.level = 0 then []
                else
                  { role := .notThetaGuard,
                    identity := none } ::
                    (belowCatalogRows snapshot row.level).map
                      fun lower =>
                        { role := .theta
                          identity :=
                            some lower.clause.identityJson })
  | .termination =>
      .ok <|
        ({ role := .notGuard, identity := none } :
          AxiomTag Gamma) ::
          snapshot.rows.map fun row =>
            { role := .collapsed
              identity := some row.clause.identityJson }

/- Proof-connected preparation of one formula component. -/
structure PreparedComponent
    (Gamma : UnnamedSchema WhielNames) where
  metadata : Component.Metadata Gamma
  body : PreparedBodyData
  support : PreparedSupportData

/- Prepare one immutable component and its support. -/
def prepareComponent?
    (env : Vampire.TPTP.NameEnv WhielNames Data)
    (metadata : Component.Metadata Gamma) :
    Option (PreparedComponent Gamma) := do
  let source : SolverBodySource Data Gamma :=
    .qf metadata.sourceId metadata.formula
  let body ← prepareBody? env source
  let support ← prepareSupportBlock? env Gamma
    metadata.formula.constants
  pure
    { metadata := metadata
      body := body.toData
      support := support.toData }

------------------------------------------------------------
-- Empty-Instance Checking
------------------------------------------------------------

/- Decided result of the exact empty-instance check. -/
inductive EmptyCheckResult
    (Gamma : UnnamedSchema WhielNames) where
| noCounterexample
| counterexample
    (assignment : Instance.NullaryAssignment Gamma)

/-
  Run the constant-blind adom-empty checker. It decides
  validity over every adom-empty instance, whatever
  constants the job mentions, which is what a reused solver
  proof needs (`QFEntailment.adomEmptyCounterexample?`); a
  negative answer also gives the FOL bridge's side condition
  (`QFEntailment.noEmpty_of_adomEmptyCounterexample?_eq_false`).
-/
def checkEmptyCounterexample
    (E : QFEntailment (D := Data) Gamma) :
    Except String (EmptyCheckResult Gamma) :=
  if !E.adomEmptyCounterexample? then
    .ok .noCounterexample
  else
    match findAdomEmptyCounterexample? E with
    | some assignment => .ok (.counterexample assignment)
    | none =>
        .error
          "empty checker returned no counterexample witness"

end FixedAmbient

end FrameworkII

end Synthesis

end Whiel

------------------------------------------------------------
-- Finite-Model Refutation Validation
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace FrameworkII

namespace FixedAmbient

open Concrete

variable {Gamma : UnnamedSchema WhielNames}

/- Validate one solver finite model against an exact job. -/
def validateRefutation
    (E : QFEntailment (D := Data) Gamma)
    (interpretation : Lean.Json) :
    Except String
      (Refutation.Validation Gamma E.constants) :=
  Refutation.validate E interpretation

end FixedAmbient

end FrameworkII

end Synthesis

end Whiel

------------------------------------------------------------
-- Direct Clause Evaluation
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace FrameworkII

namespace FixedAmbient

open Concrete

variable {Gamma : UnnamedSchema WhielNames}

/- Evaluate one admitted clause formula on one instance. -/
def evaluateClauseOnInstance
    (clause : Clause Gamma)
    (assignment : Instance Data Gamma) : Bool :=
  decide (clause.formula.eval assignment)

end FixedAmbient

end FrameworkII

end Synthesis

end Whiel

------------------------------------------------------------
-- Protected Precondition Rows
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace FrameworkII

namespace FixedAmbient

open Concrete

variable {Gamma : UnnamedSchema WhielNames}

/- One EDB-only precondition conjunct as a level-0 row. -/
structure PreconditionRow
    (Gamma : UnnamedSchema WhielNames) where
  ordinal : Nat
  clause : Clause Gamma

/- Lean theorem names closing each protected row. -/
def preconditionInitializationTheorem : String :=
  "Whiel.Synthesis.FrameworkII.FixedAmbient." ++
    "EdbPrecondition.initVC_valid"

def preconditionMaintenanceTheorem : String :=
  "Whiel.Synthesis.FrameworkII.FixedAmbient." ++
    "EdbPrecondition.maintenanceVC_valid"

/-
  Every EDB-only top-level conjunct of the lifted loop's
  precondition.
-/
def preconditionRows
    (loop : Hoare.LoopTriple Data Gamma) :
    List (PreconditionRow Gamma) :=
  (EdbPrecondition.extract loop.body loop.pre).map fun row =>
    { ordinal := row.ordinal
      clause := Clause.ofFormula row.formula }

/- Extracted rows are exactly the theorem-covered rows. -/
theorem preconditionRows_formula_mem
    (loop : Hoare.LoopTriple Data Gamma)
    (row : PreconditionRow Gamma)
    (hRow : row ∈ preconditionRows loop) :
    ∃ extracted ∈
        EdbPrecondition.extract loop.body loop.pre,
      extracted.formula = row.clause.formula := by
  unfold preconditionRows at hRow
  rcases List.mem_map.mp hRow with
    ⟨extracted, hMem, hEq⟩
  refine ⟨extracted, hMem, ?_⟩
  subst hEq
  rfl

end FixedAmbient

end FrameworkII

end Synthesis

end Whiel

------------------------------------------------------------
-- Protected Row Confirmation
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace FrameworkII

namespace FixedAmbient

open Concrete

variable {Gamma : UnnamedSchema WhielNames}

/- Typed guards with equal raw syntax are equal. -/
theorem Guard.eq_of_toRaw_eq
    {left right : QFAssertExpr Data Gamma}
    (hRaw : left.toRaw = right.toRaw) :
    left = right := by
  have hLeft := Guard.toRaw_toGuard? left
  have hRight := Guard.toRaw_toGuard? right
  rw [hRaw] at hLeft
  rw [hLeft] at hRight
  exact Option.some.inj hRight

/- Extracted rows keep both ordinal and formula. -/
theorem preconditionRows_ordinal_formula_mem
    (loop : Hoare.LoopTriple Data Gamma)
    (row : PreconditionRow Gamma)
    (hRow : row ∈ preconditionRows loop) :
    ∃ extracted ∈
        EdbPrecondition.extract loop.body loop.pre,
      extracted.ordinal = row.ordinal ∧
        extracted.formula = row.clause.formula := by
  unfold preconditionRows at hRow
  rcases List.mem_map.mp hRow with
    ⟨extracted, hMem, hEq⟩
  refine ⟨extracted, hMem, ?_, ?_⟩
  · subst hEq
    rfl
  · subst hEq
    rfl

/-
  One bound snapshot row confirmed by Lean to be an extracted
  protected precondition row. The confirmation carries every
  fact that closes the row's two verification conditions.
-/
structure PreconditionRowConfirmation
    (loop : Hoare.LoopTriple Data Gamma)
    (snapshot : Snapshot Gamma) where
  row : CatalogRow Gamma
  rowMem : row ∈ snapshot.rows
  ordinal : Nat
  precondition : PreconditionRow Gamma
  preconditionMem : precondition ∈ preconditionRows loop
  preconditionOrdinal : precondition.ordinal = ordinal
  formula_eq :
    precondition.clause.formula = row.clause.formula
  identity_eq :
    precondition.clause.identity = row.clause.identity
  level_eq : row.level = 0

private def selectorClauseId? :
    ObligationSelector -> Option Nat
| .initialization clauseId => some clauseId
| .maintenance clauseId => some clauseId
| .termination => none

/-
  Confirm that a bound job's row is one extracted protected
  precondition row at the claimed source ordinal.
-/
def confirmPreconditionRow
    (loop : Hoare.LoopTriple Data Gamma)
    (snapshot : Snapshot Gamma)
    (selector : ObligationSelector)
    (ordinal : Nat) :
    Except String
      (PreconditionRowConfirmation loop snapshot) := do
  let clauseId <- match selectorClauseId? selector with
    | some clauseId => pure clauseId
    | none =>
        throw "the termination job has no protected row"
  match hRow : snapshot.rows.find?
      (fun row => row.clauseId == clauseId) with
  | none => throw "confirmation names an unknown clause ID"
  | some row =>
      match hPre : (preconditionRows loop).find?
          (fun precondition =>
            precondition.ordinal == ordinal) with
      | none =>
          throw "no extracted precondition row has the ordinal"
      | some precondition =>
          if hLevel : row.level = 0 then
            if hRaw : precondition.clause.formula.toRaw =
                row.clause.formula.toRaw then
              if hIdentity : precondition.clause.identity =
                  row.clause.identity then
                pure
                  { row
                    rowMem := List.mem_of_find?_eq_some hRow
                    ordinal
                    precondition
                    preconditionMem :=
                      List.mem_of_find?_eq_some hPre
                    preconditionOrdinal := by
                      have hFound :=
                        List.find?_some hPre
                      simpa using hFound
                    formula_eq := Guard.eq_of_toRaw_eq hRaw
                    identity_eq := hIdentity
                    level_eq := hLevel }
              else
                throw "the bound row identity is not the extracted row"
            else
              throw "the bound row formula is not the extracted row"
          else
            throw "a protected row must be bound at level zero"

namespace PreconditionRowConfirmation

variable {loop : Hoare.LoopTriple Data Gamma}
variable {snapshot : Snapshot Gamma}

/- The confirmed row's family clause. -/
def clause
    (confirmation :
      PreconditionRowConfirmation loop snapshot) :
    LeveledClause Data Gamma :=
  ⟨confirmation.row.clause.formula, confirmation.row.level⟩

/- The confirmed clause is one extracted level-zero row. -/
theorem clause_eq_leveledClause
    (confirmation :
      PreconditionRowConfirmation loop snapshot) :
    ∃ extracted ∈
        EdbPrecondition.extract loop.body loop.pre,
      extracted.ordinal = confirmation.ordinal ∧
        EdbPrecondition.leveledClause extracted =
          confirmation.clause := by
  rcases preconditionRows_ordinal_formula_mem loop
      confirmation.precondition
      confirmation.preconditionMem with
    ⟨extracted, hMem, hOrdinal, hFormula⟩
  refine ⟨extracted, hMem, ?_, ?_⟩
  · rw [hOrdinal, confirmation.preconditionOrdinal]
  · unfold EdbPrecondition.leveledClause clause
    rw [hFormula, confirmation.formula_eq,
      confirmation.level_eq]

/- The confirmed clause belongs to the bound family. -/
theorem clause_mem_family
    (confirmation :
      PreconditionRowConfirmation loop snapshot) :
    confirmation.clause ∈ snapshot.family.clauses := by
  unfold Snapshot.family clause
  exact List.mem_map_of_mem confirmation.rowMem

/- Lean closes the confirmed row's initialization job. -/
theorem initVC_valid
    (task : Task loop.body)
    (confirmation :
      PreconditionRowConfirmation loop snapshot) :
    (snapshot.family.initVC task loop.guard loop.pre
      confirmation.clause).Valid := by
  rcases confirmation.clause_eq_leveledClause with
    ⟨extracted, hMem, _, hClause⟩
  rw [← hClause]
  exact EdbPrecondition.initVC_valid task snapshot.family
    loop.guard loop.pre extracted hMem

/- Lean closes the confirmed row's maintenance job. -/
theorem maintenanceVC_valid
    (task : Task loop.body)
    (confirmation :
      PreconditionRowConfirmation loop snapshot) :
    (snapshot.family.maintenanceVC task loop.guard
      loop.body_loopFree confirmation.clause).Valid := by
  rcases confirmation.clause_eq_leveledClause with
    ⟨extracted, hMem, _, hClause⟩
  have hInstalled := confirmation.clause_mem_family
  rw [← hClause] at hInstalled ⊢
  exact EdbPrecondition.maintenanceVC_valid task
    snapshot.family loop.guard loop.body_loopFree
    extracted loop.pre hMem hInstalled

end PreconditionRowConfirmation

/- Theorem names closing a confirmed row's two jobs. -/
def confirmationInitializationTheorem : String :=
  "Whiel.Synthesis.FrameworkII.FixedAmbient." ++
    "PreconditionRowConfirmation.initVC_valid"

def confirmationMaintenanceTheorem : String :=
  "Whiel.Synthesis.FrameworkII.FixedAmbient." ++
    "PreconditionRowConfirmation.maintenanceVC_valid"

end FixedAmbient

end FrameworkII

end Synthesis

end Whiel
