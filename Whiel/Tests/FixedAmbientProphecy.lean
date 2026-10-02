-- Author: Jesse Comer
import Whiel.Concrete.Data
import Whiel.Hoare.Concrete
import Whiel.Hoare.FixedAmbientProphecy
import Whiel.Hoare.ProphecySchema

/-
  Focused canary for fixed-ambient Framework II.

  One six-row `WhielNames` schema contains ordinary and
  prophecy copies of unary program symbols and one binary
  auxiliary symbol. A raw while loop genuinely iterates,
  and two nontrivial candidate levels discharge the exact
  semantic `2N+1` obligations without any schema cast.

  The final theorem proves the original syntactic Hoare
  triple. A closing section states the same loop over a
  program-name input schema, lets `Hoare.preprocess` decide
  every raw check, and shows that the computed prophecy
  schema rejects a positive raw index and a flag symbol.
-/

------------------------------------------------------------
-- One Fixed Ambient Schema
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace FixedAmbientProphecyCanary

open Concrete

def baseR : AlphaString :=
  ⟨"R", by decide⟩

def baseT : AlphaString :=
  ⟨"T", by decide⟩

def baseU : AlphaString :=
  ⟨"U", by decide⟩

def programR : ProgramNames :=
  .programSymbol baseR 0

def auxiliaryT : ProgramNames :=
  .auxiliarySymbol baseT 0

def programU : ProgramNames :=
  .programSymbol baseU 0

def ordinaryRName : WhielNames :=
  .ordinary programR

def ordinaryTName : WhielNames :=
  .ordinary auxiliaryT

def ordinaryUName : WhielNames :=
  .ordinary programU

def prophecyRName : WhielNames :=
  .prophecy programR

def prophecyTName : WhielNames :=
  .prophecy auxiliaryT

def prophecyUName : WhielNames :=
  .prophecy programU

def ambientSchema : UnnamedSchema WhielNames where
  syms :=
    {ordinaryRName, ordinaryTName, ordinaryUName,
      prophecyRName, prophecyTName, prophecyUName}
  arity := fun relation =>
    match relation.1 with
    | .ordinary (.auxiliarySymbol _ _) => 2
    | .prophecy (.auxiliarySymbol _ _) => 2
    | _ => 1

def ordinaryR : ambientSchema.syms :=
  ⟨ordinaryRName, by decide⟩

def ordinaryT : ambientSchema.syms :=
  ⟨ordinaryTName, by decide⟩

def ordinaryU : ambientSchema.syms :=
  ⟨ordinaryUName, by decide⟩

def prophecyR : ambientSchema.syms :=
  ⟨prophecyRName, by decide⟩

def prophecyT : ambientSchema.syms :=
  ⟨prophecyTName, by decide⟩

def prophecyU : ambientSchema.syms :=
  ⟨prophecyUName, by decide⟩

theorem ordinaryR_arity :
    ambientSchema.arity ordinaryR = 1 := by
  decide

theorem prophecyR_arity :
    ambientSchema.arity prophecyR = 1 := by
  decide

theorem ordinaryT_arity :
    ambientSchema.arity ordinaryT = 2 := by
  decide

theorem prophecyT_arity :
    ambientSchema.arity prophecyT = 2 := by
  decide

end FixedAmbientProphecyCanary

end Tests

end Whiel

------------------------------------------------------------
-- Structural Name Contract
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace FixedAmbientProphecyCanary

open Concrete

theorem prophecy_partner_unique
    (partner : WhielNames)
    (hPartner :
      ordinaryRName.prophecyPartner? = some partner) :
    partner = prophecyRName := by
  simpa [ordinaryRName, prophecyRName, programR]
    using hPartner.symm

theorem no_partner_of_prophecy :
    prophecyRName.prophecyPartner? = none := by
  rfl

theorem nonbase_name_rejected :
    ¬ WhielNames.BaseNameOnly
      (.ordinary (.programSymbol baseR 1)) := by
  decide

theorem prophecy_name_rejected :
    ¬ WhielNames.BaseNameOnly prophecyRName := by
  decide

end FixedAmbientProphecyCanary

end Tests

end Whiel

------------------------------------------------------------
-- Raw Loop and Surface Discipline
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace FixedAmbientProphecyCanary

open Concrete

def ordinaryREmpty :
    QFAssertExpr Data ambientSchema :=
  .eq (RAExpr.rel ordinaryR) (RAExpr.empty 1)

def ordinaryTEmpty :
    QFAssertExpr Data ambientSchema :=
  .eq (RAExpr.rel ordinaryT) (RAExpr.empty 2)

def ordinaryUEmpty :
    QFAssertExpr Data ambientSchema :=
  .eq (RAExpr.rel ordinaryU) (RAExpr.empty 1)

def prophecyREmpty :
    QFAssertExpr Data ambientSchema :=
  .eq (RAExpr.rel prophecyR) (RAExpr.empty 1)

def levelZeroFormula :
    QFAssertExpr Data ambientSchema :=
  .and ordinaryREmpty ordinaryTEmpty

def levelOneFormula :
    QFAssertExpr Data ambientSchema :=
  .and
    (.eq (RAExpr.rel ordinaryR)
      (RAExpr.rel prophecyR))
    (.eq (RAExpr.rel ordinaryT)
      (RAExpr.rel prophecyT))

def postFormula : QFAssertExpr Data ambientSchema :=
  .and levelZeroFormula ordinaryUEmpty

def loopGuard : Guard Data ambientSchema :=
  .not ordinaryUEmpty

def loopBody : Cmd Data ambientSchema :=
  .seq
    (.assign ordinaryR (RAExpr.empty 1))
    (.seq
      (.assign ordinaryT (RAExpr.empty 2))
      (.assign ordinaryU (RAExpr.empty 1)))

def inputPre : AssertExpr Data ambientSchema :=
  AssertExpr.ofQF levelZeroFormula

def inputCmd : Cmd Data ambientSchema :=
  .while loopGuard loopBody

def inputPost : AssertExpr Data ambientSchema :=
  AssertExpr.ofQF postFormula

private theorem eval_empty
    (arity : Nat)
    (state : Instance Data ambientSchema) :
    (RAExpr.empty arity).eval state = ∅ := by
  simp [RAExpr.eval, RAExpr.empty, RawRAExpr.eval?]

private theorem eval_rel
    (relation : ambientSchema.syms)
    (state : Instance Data ambientSchema) :
    (RAExpr.rel relation).eval state =
      state relation := by
  have hSpec :=
    RAExpr.raw_eval?_eq_eval
      (RAExpr.rel relation :
        RAExpr Data ambientSchema
          (ambientSchema.arity relation)) state
  have hRaw :
      (RAExpr.rel relation :
        RAExpr Data ambientSchema
          (ambientSchema.arity relation)).expr.eval?
          (Γ := ambientSchema) state =
        some ⟨ambientSchema.arity relation,
          state relation⟩ := by
    simp [RAExpr.rel, RawRAExpr.eval?,
      Instance.relation?, relation.2]
  rw [hRaw] at hSpec
  injection hSpec with hSigma
  injection hSigma with _hAr hRelation
  exact hRelation.symm

theorem ordinaryREmpty_eval_iff
    (state : Instance Data ambientSchema) :
    ordinaryREmpty.eval state ↔
      state ordinaryR = ∅ := by
  change (RAExpr.rel ordinaryR).eval state =
      (RAExpr.empty 1).eval state ↔ _
  have hRel :
      (RAExpr.rel ordinaryR).eval state =
        state ordinaryR :=
    eval_rel ordinaryR state
  rw [hRel, eval_empty]
  rfl

theorem ordinaryTEmpty_eval_iff
    (state : Instance Data ambientSchema) :
    ordinaryTEmpty.eval state ↔
      state ordinaryT = ∅ := by
  change (RAExpr.rel ordinaryT).eval state =
      (RAExpr.empty 2).eval state ↔ _
  have hRel :
      (RAExpr.rel ordinaryT).eval state =
        state ordinaryT :=
    eval_rel ordinaryT state
  rw [hRel, eval_empty]
  rfl

theorem ordinaryUEmpty_eval_iff
    (state : Instance Data ambientSchema) :
    ordinaryUEmpty.eval state ↔
      state ordinaryU = ∅ := by
  change (RAExpr.rel ordinaryU).eval state =
      (RAExpr.empty 1).eval state ↔ _
  have hRel :
      (RAExpr.rel ordinaryU).eval state =
        state ordinaryU :=
    eval_rel ordinaryU state
  rw [hRel, eval_empty]
  rfl

theorem levelZeroFormula_eval_iff
    (state : Instance Data ambientSchema) :
    levelZeroFormula.eval state ↔
      state ordinaryR = ∅ ∧
        state ordinaryT = ∅ := by
  exact and_congr
    (ordinaryREmpty_eval_iff state)
    (ordinaryTEmpty_eval_iff state)

theorem levelOneFormula_eval_iff
    (state : Instance Data ambientSchema) :
    levelOneFormula.eval state ↔
      state ordinaryR = state prophecyR ∧
        state ordinaryT = state prophecyT := by
  change
    ((RAExpr.rel ordinaryR).eval state =
        (RAExpr.rel prophecyR).eval state) ∧
      ((RAExpr.rel ordinaryT).eval state =
        (RAExpr.rel prophecyT).eval state) ↔ _
  have hOrdinaryR :
      (RAExpr.rel ordinaryR).eval state =
        state ordinaryR :=
    eval_rel ordinaryR state
  have hProphecyR :
      (RAExpr.rel prophecyR).eval state =
        state prophecyR :=
    eval_rel prophecyR state
  have hOrdinaryT :
      (RAExpr.rel ordinaryT).eval state =
        state ordinaryT :=
    eval_rel ordinaryT state
  have hProphecyT :
      (RAExpr.rel prophecyT).eval state =
        state prophecyT :=
    eval_rel prophecyT state
  rw [hOrdinaryR, hProphecyR,
    hOrdinaryT, hProphecyT]

theorem postFormula_eval_iff
    (state : Instance Data ambientSchema) :
    postFormula.eval state ↔
      (state ordinaryR = ∅ ∧
        state ordinaryT = ∅) ∧
      state ordinaryU = ∅ := by
  exact and_congr
    (levelZeroFormula_eval_iff state)
    (ordinaryUEmpty_eval_iff state)

end FixedAmbientProphecyCanary

end Tests

end Whiel

------------------------------------------------------------
-- Task Validation and Rejection
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace FixedAmbientProphecyCanary

open Concrete

def task : Hoare.WhielNamesProphecy.Task loopBody where
  assignedOrdinary := by
    intro relation hAssigned
    simp only [loopBody, Cmd.assignedSymbols,
      Finset.singleton_union, Finset.union_insert,
      Finset.mem_insert, Finset.mem_singleton]
      at hAssigned
    rcases hAssigned with h | h | h
    · subst relation
      trivial
    · subst relation
      trivial
    · subst relation
      trivial
  prophecyMem := by
    intro name hAssigned
    simp only [loopBody, Cmd.assignedSymbols,
      Finset.singleton_union, Finset.union_insert,
      Finset.mem_insert, Finset.mem_singleton]
      at hAssigned
    rcases hAssigned with h | h | h
    · injection h with hName
      subst name
      decide
    · injection h with hName
      subst name
      decide
    · injection h with hName
      subst name
      decide
  prophecyArity := by
    intro name _hAssigned
    cases name <;> rfl

theorem task_mixed_arities :
    ambientSchema.arity ordinaryR =
        ambientSchema.arity prophecyR ∧
      ambientSchema.arity ordinaryT =
        ambientSchema.arity prophecyT := by
  decide

def missingSchema : UnnamedSchema WhielNames where
  syms := {ordinaryRName}
  arity := fun _ => 1

def missingR : missingSchema.syms :=
  ⟨ordinaryRName, by decide⟩

def missingBody : Cmd Data missingSchema :=
  .assign missingR (RAExpr.empty 1)

theorem missing_prophecy_rejected :
    ¬ Nonempty
      (Hoare.WhielNamesProphecy.Task missingBody) := by
  intro hTask
  rcases hTask with ⟨candidate⟩
  have hAssigned :
      ordinaryRName ∈ missingBody.assignedSymbols := by
    simp [missingBody, missingR,
      Cmd.assignedSymbols]
  have hProphecy :=
    candidate.prophecyMem programR hAssigned
  exact (by decide : prophecyRName ∉ missingSchema.syms)
    hProphecy

def wrongAritySchema : UnnamedSchema WhielNames where
  syms := {ordinaryRName, prophecyRName}
  arity := fun relation =>
    if relation.1 = ordinaryRName then 1 else 2

def wrongArityR : wrongAritySchema.syms :=
  ⟨ordinaryRName, by decide⟩

def wrongArityBody : Cmd Data wrongAritySchema :=
  .assign wrongArityR (RAExpr.empty 1)

theorem wrong_arity_rejected :
    ¬ Nonempty
      (Hoare.WhielNamesProphecy.Task
        wrongArityBody) := by
  intro hTask
  rcases hTask with ⟨candidate⟩
  have hAssigned :
      ordinaryRName ∈
        wrongArityBody.assignedSymbols := by
    simp [wrongArityBody, wrongArityR,
      Cmd.assignedSymbols]
  have hArity :=
    candidate.prophecyArity programR hAssigned
  simp [wrongAritySchema, ordinaryRName,
    prophecyRName] at hArity

def prophecyWriteBody : Cmd Data ambientSchema :=
  .assign prophecyR (RAExpr.empty 1)

theorem prophecy_assignment_rejected :
    ¬ Nonempty
      (Hoare.WhielNamesProphecy.Task
        prophecyWriteBody) := by
  intro hTask
  rcases hTask with ⟨candidate⟩
  have hAssigned :
      prophecyRName ∈
        prophecyWriteBody.assignedSymbols := by
    simp [prophecyWriteBody, Cmd.assignedSymbols,
      prophecyR]
  have hOrdinary :=
    candidate.assignedOrdinary prophecyRName hAssigned
  exact hOrdinary

end FixedAmbientProphecyCanary

end Tests

end Whiel

------------------------------------------------------------
-- Structural Theta, Collapse, and Frame
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace FixedAmbientProphecyCanary

open Concrete

theorem theta_ordinaryR :
    task.thetaRelabeling.symbol ordinaryR = prophecyR := by
  apply Subtype.ext
  decide

theorem theta_ordinaryT :
    task.thetaRelabeling.symbol ordinaryT = prophecyT := by
  apply Subtype.ext
  decide

theorem collapse_prophecyR :
    task.collapseRelabeling.symbol prophecyR =
      ordinaryR := by
  apply Subtype.ext
  decide

theorem collapse_prophecyT :
    task.collapseRelabeling.symbol prophecyT =
      ordinaryT := by
  apply Subtype.ext
  decide

theorem semanticCollapse_ordinaryR
    (state : Instance Data ambientSchema) :
    task.semanticCollapse state ordinaryR =
      state prophecyR := by
  rfl

theorem semanticCollapse_ordinaryT
    (state : Instance Data ambientSchema) :
    task.semanticCollapse state ordinaryT =
      state prophecyT := by
  rfl

theorem semanticCollapse_ordinaryU
    (state : Instance Data ambientSchema) :
    task.semanticCollapse state ordinaryU =
      state prophecyU := by
  rfl

theorem theta_levelZero_eval_iff
    (state : Instance Data ambientSchema) :
    (task.theta levelZeroFormula).eval state ↔
      state prophecyR = ∅ ∧
        state prophecyT = ∅ := by
  rw [task.theta_eval_iff,
    levelZeroFormula_eval_iff,
    semanticCollapse_ordinaryR,
    semanticCollapse_ordinaryT]
  rfl

theorem exitLift_frames_program_symbols
    (state : Instance Data ambientSchema) :
    Instance.agreeOn task.programSymbols state
      (task.exitLift state) :=
  task.exitLift_agreeOn state

theorem collapse_after_exitLift
    (state : Instance Data ambientSchema) :
    task.semanticCollapse (task.exitLift state) =
      task.exitLift state :=
  task.semanticCollapse_exitLift state

end FixedAmbientProphecyCanary

end Tests

end Whiel

------------------------------------------------------------
-- A Genuine Loop Iteration
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace FixedAmbientProphecyCanary

open Concrete

theorem loopBody_outputs_empty
    {initial final : Instance Data ambientSchema}
    (hStep : Cmd.BigStep loopBody initial final) :
    final ordinaryR = ∅ ∧
      final ordinaryT = ∅ ∧
        final ordinaryU = ∅ := by
  unfold loopBody at hStep
  rw [Cmd.bigStep_seq_iff] at hStep
  rcases hStep with ⟨afterR, hR, hTU⟩
  rw [Cmd.bigStep_assign_iff] at hR
  rw [Cmd.bigStep_seq_iff] at hTU
  rcases hTU with ⟨afterT, hT, hU⟩
  rw [Cmd.bigStep_assign_iff] at hT
  rw [Cmd.bigStep_assign_iff] at hU
  subst afterR
  subst afterT
  subst final
  constructor
  · rw [Instance.update_lookup_ne _ ordinaryU
        ordinaryR (by decide),
      Instance.update_lookup_ne _ ordinaryT
        ordinaryR (by decide),
      Instance.update_lookup_eq]
    exact eval_empty 1 initial
  · constructor
    · rw [Instance.update_lookup_ne _ ordinaryU
          ordinaryT (by decide),
        Instance.update_lookup_eq]
      exact eval_empty 2 _
    · rw [Instance.update_lookup_eq]
      exact eval_empty 1 _

def iterationInput : Instance Data ambientSchema :=
  Instance.update
    (Instance.empty ambientSchema)
    ordinaryU
    {Vector.singleton (Data.num 0)}

theorem iterationInput_guard :
    loopGuard.eval iterationInput := by
  change ¬ ordinaryUEmpty.eval iterationInput
  rw [ordinaryUEmpty_eval_iff]
  rw [iterationInput, Instance.update_lookup_eq]
  exact Finset.singleton_ne_empty _

theorem genuine_iteration_exists :
    ∃ initial final : Instance Data ambientSchema,
      loopGuard.eval initial ∧
        Cmd.BigStep loopBody initial final ∧
          ¬ loopGuard.eval final := by
  let initial := iterationInput
  let afterR := Instance.update initial ordinaryR
    ((RAExpr.empty 1).eval initial)
  let afterT := Instance.update afterR ordinaryT
    ((RAExpr.empty 2).eval afterR)
  let final := Instance.update afterT ordinaryU
    ((RAExpr.empty 1).eval afterT)
  have hStep : Cmd.BigStep loopBody initial final := by
    unfold loopBody
    exact Cmd.BigStep.seq
      (Cmd.BigStep.assign initial ordinaryR
        (RAExpr.empty 1))
      (Cmd.BigStep.seq
        (Cmd.BigStep.assign afterR ordinaryT
          (RAExpr.empty 2))
        (Cmd.BigStep.assign afterT ordinaryU
          (RAExpr.empty 1)))
  have hEmpty := loopBody_outputs_empty hStep
  refine ⟨initial, final, ?_, hStep, ?_⟩
  · exact iterationInput_guard
  · intro hGuard
    exact hGuard
      ((ordinaryUEmpty_eval_iff final).mpr
        hEmpty.2.2)

/- The raw input loop takes that step and then exits. -/
theorem genuine_input_iteration_exists :
    ∃ initial final : Instance Data ambientSchema,
      Cmd.BigStep inputCmd initial final ∧
        initial ≠ final := by
  rcases genuine_iteration_exists with
    ⟨initial, final, hGuard, hBody, hExit⟩
  have hRun : Cmd.BigStep inputCmd initial final := by
    unfold inputCmd
    exact Cmd.BigStep.while_true hGuard hBody
      (Cmd.BigStep.while_false hExit)
  refine ⟨initial, final, hRun, ?_⟩
  intro hEqual
  subst final
  exact hExit hGuard

end FixedAmbientProphecyCanary

end Tests

end Whiel

------------------------------------------------------------
-- Two Semantic Candidate Levels
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace FixedAmbientProphecyCanary

open Concrete
open Hoare.FixedAmbientProphecy

def candidateLevels :
    Nat → List (Assertion Data ambientSchema)
| 0 => [levelZeroFormula.eval]
| 1 => [levelOneFormula.eval]
| _ => []

theorem empty_prophecyBelow_one :
    prophecyBelow task.prophecyCollapse loopGuard
      candidateLevels 1
      (Instance.empty ambientSchema) := by
  constructor
  · intro _hPositive hGuard
    apply hGuard
    apply (ordinaryUEmpty_eval_iff _).mpr
    change task.semanticCollapse
      (Instance.empty ambientSchema) ordinaryU = ∅
    rw [semanticCollapse_ordinaryU]
    rfl
  · intro lower hLower formula hFormula
    have hZero : lower = 0 := by omega
    subst lower
    have hFormulaEq :
        formula = levelZeroFormula.eval := by
      simpa [candidateLevels] using hFormula
    subst formula
    apply (levelZeroFormula_eval_iff _).mpr
    constructor
    · change task.semanticCollapse
        (Instance.empty ambientSchema) ordinaryR = ∅
      rw [semanticCollapse_ordinaryR]
      rfl
    · change task.semanticCollapse
        (Instance.empty ambientSchema) ordinaryT = ∅
      rw [semanticCollapse_ordinaryT]
      rfl

theorem initZero :
    InitObligation task.prophecyCollapse loopGuard
      candidateLevels levelZeroFormula.eval
      0 levelZeroFormula.eval := by
  intro _state hPre _hBelow
  exact hPre

theorem initOne :
    InitObligation task.prophecyCollapse loopGuard
      candidateLevels levelZeroFormula.eval
      1 levelOneFormula.eval := by
  intro state hPre hBelow
  have hThetaZero := hBelow.2 0 (by omega)
    levelZeroFormula.eval (by
      simp [candidateLevels])
  change levelZeroFormula.eval
    (task.semanticCollapse state) at hThetaZero
  have hOrdinary :=
    (levelZeroFormula_eval_iff state).mp hPre
  have hProphecy :=
    (levelZeroFormula_eval_iff
      (task.semanticCollapse state)).mp hThetaZero
  apply (levelOneFormula_eval_iff state).mpr
  rw [semanticCollapse_ordinaryR,
    semanticCollapse_ordinaryT] at hProphecy
  exact
    ⟨hOrdinary.1.trans hProphecy.1.symm,
      hOrdinary.2.trans hProphecy.2.symm⟩

theorem stepZero :
    StepObligation loopGuard loopBody
      task.prophecyCollapse candidateLevels
      0 levelZeroFormula.eval := by
  intro initial _hLadder _hGuard _hBelow final hStep
  have hEmpty := loopBody_outputs_empty hStep
  exact (levelZeroFormula_eval_iff final).mpr
    ⟨hEmpty.1, hEmpty.2.1⟩

theorem stepOne :
    StepObligation loopGuard loopBody
      task.prophecyCollapse candidateLevels
      1 levelOneFormula.eval := by
  intro initial _hLadder _hGuard hBelow final hStep
  have hThetaZero := hBelow.2 0 (by omega)
    levelZeroFormula.eval (by
      simp [candidateLevels])
  change levelZeroFormula.eval
    (task.semanticCollapse initial) at hThetaZero
  have hProphecy :=
    (levelZeroFormula_eval_iff
      (task.semanticCollapse initial)).mp hThetaZero
  rw [semanticCollapse_ordinaryR,
    semanticCollapse_ordinaryT] at hProphecy
  have hEmpty := loopBody_outputs_empty hStep
  have hProphecyR :
      final prophecyR = initial prophecyR :=
    hStep.no_update_preservation prophecyR (by decide)
  have hProphecyT :
      final prophecyT = initial prophecyT :=
    hStep.no_update_preservation prophecyT (by decide)
  apply (levelOneFormula_eval_iff final).mpr
  exact
    ⟨hEmpty.1.trans
        (hProphecyR.trans hProphecy.1).symm,
      hEmpty.2.1.trans
        (hProphecyT.trans hProphecy.2).symm⟩

theorem termination :
    TermObligation task.prophecyCollapse loopGuard
      candidateLevels postFormula.eval := by
  intro state _hFixed hExit hAll
  have hZero := hAll 0 levelZeroFormula.eval (by
    simp [candidateLevels])
  have hU : ordinaryUEmpty.eval state := by
    by_cases hEmpty : ordinaryUEmpty.eval state
    · exact hEmpty
    · exact (hExit hEmpty).elim
  exact (postFormula_eval_iff state).mpr
    ⟨(levelZeroFormula_eval_iff state).mp hZero,
      (ordinaryUEmpty_eval_iff state).mp hU⟩

theorem all_initialization :
    ∀ level,
      ∀ formula ∈ candidateLevels level,
        InitObligation task.prophecyCollapse loopGuard
          candidateLevels levelZeroFormula.eval
          level formula := by
  intro level formula hFormula
  cases level with
  | zero =>
      have hEq : formula = levelZeroFormula.eval := by
        simpa [candidateLevels] using hFormula
      subst formula
      exact initZero
  | succ level =>
      cases level with
      | zero =>
          have hEq : formula = levelOneFormula.eval := by
            simpa [candidateLevels] using hFormula
          subst formula
          exact initOne
      | succ level =>
          simp [candidateLevels] at hFormula

theorem all_steps :
    ∀ level,
      ∀ formula ∈ candidateLevels level,
        StepObligation loopGuard loopBody
          task.prophecyCollapse candidateLevels
          level formula := by
  intro level formula hFormula
  cases level with
  | zero =>
      have hEq : formula = levelZeroFormula.eval := by
        simpa [candidateLevels] using hFormula
      subst formula
      exact stepZero
  | succ level =>
      cases level with
      | zero =>
          have hEq : formula = levelOneFormula.eval := by
            simpa [candidateLevels] using hFormula
          subst formula
          exact stepOne
      | succ level =>
          simp [candidateLevels] at hFormula

end FixedAmbientProphecyCanary

end Tests

end Whiel

------------------------------------------------------------
-- Exact Raw Hoare Theorem
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace FixedAmbientProphecyCanary

open Concrete
open Hoare.FixedAmbientProphecy

theorem inputTriple_semantic_valid :
    HoareValid levelZeroFormula.eval inputCmd
      postFormula.eval := by
  unfold inputCmd
  apply hoareValid_while_of_leveled_vcs
    ambientSchema.programSymbols
    task.prophecyCollapse candidateLevels
    levelZeroFormula postFormula
  · decide
  · decide
  · decide
  · decide
  · exact all_initialization
  · exact all_steps
  · exact termination

theorem inputTriple_valid :
    HoareValid inputPre inputCmd inputPost := by
  rw [Hoare.hoareValid_assertExpr_eval_iff]
  intro initial final hPre hStep
  apply (AssertExpr.ofQF_eval_iff
    postFormula final).mpr
  exact inputTriple_semantic_valid initial final
    ((AssertExpr.ofQF_eval_iff
      levelZeroFormula initial).mp hPre)
    hStep

end FixedAmbientProphecyCanary

end Tests

end Whiel

------------------------------------------------------------
-- Program-Name Input Discipline
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace FixedAmbientProphecyCanary

open Concrete

/- The same loop, declared over a program-name schema. -/
def inputSchema : UnnamedSchema ProgramNames where
  syms := {programR, auxiliaryT, programU}
  arity := fun relation =>
    match relation.1 with
    | .auxiliarySymbol _ _ => 2
    | _ => 1

def programRRow : inputSchema.syms :=
  ⟨programR, by decide⟩

def auxiliaryTRow : inputSchema.syms :=
  ⟨auxiliaryT, by decide⟩

def programURow : inputSchema.syms :=
  ⟨programU, by decide⟩

def programPre : AssertExpr Data inputSchema :=
  AssertExpr.ofQF
    (.and (.eq (RAExpr.rel programRRow) (RAExpr.empty 1))
      (.eq (RAExpr.rel auxiliaryTRow) (RAExpr.empty 2)))

def programCmd : Cmd Data inputSchema :=
  .while (.not (.eq (RAExpr.rel programURow) (RAExpr.empty 1)))
    (.seq
      (.assign programRRow (RAExpr.empty 1))
      (.seq
        (.assign auxiliaryTRow (RAExpr.empty 2))
        (.assign programURow (RAExpr.empty 1))))

def programPost : AssertExpr Data inputSchema :=
  AssertExpr.ofQF
    (.and
      (.and (.eq (RAExpr.rel programRRow) (RAExpr.empty 1))
        (.eq (RAExpr.rel auxiliaryTRow) (RAExpr.empty 2)))
      (.eq (RAExpr.rel programURow) (RAExpr.empty 1)))

/- Every raw check is decided inside preprocessing. -/
def programPreproc :
    Hoare.Preproc programPre programCmd programPost :=
  Hoare.preprocess programPre programCmd programPost

/-
  This source is already a framed loop, so no flag is drawn
  and the preprocessed loop still lives over the input
  schema itself.
-/
theorem programPreproc_outSchema :
    programPreproc.outSchema.syms = inputSchema.syms := by
  decide +kernel

/- The computed schema has the six rows of the hand schema. -/
def programLoop :
    Hoare.LoopTriple Data programPreproc.outSchema :=
  Hoare.LoopTriple.ofPreproc programPreproc

example :
    programLoop.prophecySchema.syms = ambientSchema.syms := by
  decide +kernel

/- The lifted loop's task exists without a per-input proof. -/
example :
    Hoare.WhielNamesProphecy.Task programLoop.lift.body :=
  programLoop.task

/-
  The flag supply is seeded from the input schema, not
  imposed on it: a schema that already carries a flag
  relation is accepted, and the transformation draws
  identifiers strictly above the largest one it finds.
-/
def flagSchema : UnnamedSchema ProgramNames where
  syms := {programR, .flagSymbol 3 0}
  arity := fun relation =>
    match relation.1 with
    | .flagSymbol _ _ => 0
    | _ => 1

/- The seed is one above the schema's largest flag. -/
theorem flagSchema_seed :
    Preprocess.flagSeed flagSchema = 4 := by
  decide +kernel

def flagRow : flagSchema.syms :=
  ⟨programR, by decide⟩

def flagPre : AssertExpr Data flagSchema :=
  AssertExpr.ofQF
    (.eq (RAExpr.rel flagRow) (RAExpr.empty 1))

/-
  A nested source over that schema, so the transformation
  must actually draw a flag.
-/
def flagCmd : Cmd Data flagSchema :=
  .while (.not (.eq (RAExpr.rel flagRow) (RAExpr.empty 1)))
    (.while (.eq (RAExpr.rel flagRow) (RAExpr.empty 1))
      (.assign flagRow (RAExpr.empty 1)))

/- Preprocessing accepts it. -/
def flagPreproc : Hoare.Preproc flagPre flagCmd flagPre :=
  Hoare.preprocess flagPre flagCmd flagPre

/-
  The drawn flag is `flag_4_0`, above the input schema's own
  `flag_3_0`, and the input's flag is untouched.
-/
theorem flagPreproc_outSchema :
    flagPreproc.outSchema.syms =
      {programR, .flagSymbol 3 0, .flagSymbol 4 0} := by
  decide +kernel

end FixedAmbientProphecyCanary

end Tests

end Whiel
