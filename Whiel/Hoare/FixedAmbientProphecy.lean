-- Author: Jesse Comer
import Whiel.AssertExpr.Relabeling
import Whiel.Concrete.WhielNames
import Whiel.Hoare.Abstract

/-
  Prophecy semantics for a program already typed over one
  ambient schema. The generic soundness theorem needs only
  an in-place collapse package and a program-symbol frame.
  The concrete specialization derives both structural maps
  from `WhielNames` constructors.
-/

------------------------------------------------------------
-- Generic Fixed-Ambient Collapse
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace FixedAmbientProphecy

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Gamma : UnnamedSchema A}

/-
  In-place prophecy collapse and exit instantiation. The
  exit lift preserves the program-facing frame, while
  collapse depends only on relations the body cannot write.
-/
structure Collapse
    (programSymbols assigned : Finset A) where
  collapse : Instance D Gamma -> Instance D Gamma
  collapse_congr :
    forall left right : Instance D Gamma,
      (forall relation : Gamma.syms,
        relation.1 ∉ assigned ->
          left relation = right relation) ->
      collapse left = collapse right
  exitLift : Instance D Gamma -> Instance D Gamma
  exitLift_agreeOn :
    forall state : Instance D Gamma,
      Instance.agreeOn programSymbols state
        (exitLift state)
  collapse_exitLift :
    forall state : Instance D Gamma,
      collapse (exitLift state) = exitLift state

end FixedAmbientProphecy

end Hoare

end Whiel

------------------------------------------------------------
-- Generic Levels and Ladder Invariant
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace FixedAmbientProphecy

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Gamma : UnnamedSchema A}
variable {programSymbols assigned : Finset A}

/- Terminal facts available below one candidate level. -/
def prophecyBelow
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols assigned)
    (guard : Guard D Gamma)
    (levels : Nat -> List (Assertion D Gamma))
    (level : Nat)
    (state : Instance D Gamma) : Prop :=
  (0 < level ->
      ¬ guard.eval (prophecy.collapse state)) ∧
    forall lower,
      lower < level ->
        ∀ formula ∈ levels lower,
          formula (prophecy.collapse state)

/- Every clause at every level holds in one state. -/
def holdsAt
    (levels : Nat -> List (Assertion D Gamma))
    (state : Instance D Gamma) : Prop :=
  forall level, ∀ formula ∈ levels level,
    formula state

/- Each level follows from its lower terminal facts. -/
def ladderInv
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols assigned)
    (guard : Guard D Gamma)
    (levels : Nat -> List (Assertion D Gamma)) :
    Assertion D Gamma :=
  fun state =>
    forall level,
      prophecyBelow prophecy guard levels level state ->
        ∀ formula ∈ levels level,
          formula state

/- Level zero has no terminal assumptions. -/
theorem prophecyBelow_zero
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols assigned)
    (guard : Guard D Gamma)
    (levels : Nat -> List (Assertion D Gamma))
    (state : Instance D Gamma) :
    prophecyBelow prophecy guard levels 0 state := by
  refine ⟨?_, ?_⟩
  · intro hPositive
    exact absurd hPositive (Nat.lt_irrefl 0)
  · intro lower hLower
    exact absurd hLower (Nat.not_lt_zero lower)

/- Higher-level terminal facts imply lower-level ones. -/
theorem prophecyBelow_mono
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols assigned)
    (guard : Guard D Gamma)
    (levels : Nat -> List (Assertion D Gamma))
    {lower upper : Nat}
    (hLevels : lower ≤ upper)
    {state : Instance D Gamma}
    (hBelow :
      prophecyBelow prophecy guard levels upper state) :
    prophecyBelow prophecy guard levels lower state := by
  refine ⟨?_, ?_⟩
  · intro hPositive
    exact hBelow.1
      (Nat.lt_of_lt_of_le hPositive hLevels)
  · intro level hLevel formula hFormula
    exact hBelow.2 level
      (Nat.lt_of_lt_of_le hLevel hLevels)
      formula hFormula

/- Terminal facts are framed by unassigned relations. -/
theorem prophecyBelow_congr
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols assigned)
    (guard : Guard D Gamma)
    (levels : Nat -> List (Assertion D Gamma))
    (level : Nat)
    {left right : Instance D Gamma}
    (hAgree : forall relation : Gamma.syms,
      relation.1 ∉ assigned ->
        left relation = right relation) :
    prophecyBelow prophecy guard levels level left ↔
      prophecyBelow prophecy guard levels level right := by
  unfold prophecyBelow
  rw [prophecy.collapse_congr left right hAgree]

/-
  The level family truncated to the levels strictly below
  one bound. Every level at or above the bound is empty.
-/
def levelsBelow
    (levels : Nat -> List (Assertion D Gamma))
    (bound : Nat) :
    Nat -> List (Assertion D Gamma) :=
  fun level => if level < bound then levels level else []

/- Truncation is the identity strictly below the bound. -/
theorem levelsBelow_of_lt
    (levels : Nat -> List (Assertion D Gamma))
    {bound level : Nat}
    (hLevel : level < bound) :
    levelsBelow levels bound level = levels level := by
  simp [levelsBelow, hLevel]

/- Truncation empties every level at or above the bound. -/
theorem levelsBelow_of_le
    (levels : Nat -> List (Assertion D Gamma))
    {bound level : Nat}
    (hLevel : bound ≤ level) :
    levelsBelow levels bound level = [] := by
  simp [levelsBelow, Nat.not_lt_of_le hLevel]

/- Terminal facts read only the strictly lower levels. -/
theorem prophecyBelow_congr_levels
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols assigned)
    (guard : Guard D Gamma)
    {left right : Nat -> List (Assertion D Gamma)}
    (level : Nat)
    (hAgree : forall lower, lower < level ->
      left lower = right lower)
    (state : Instance D Gamma) :
    prophecyBelow prophecy guard left level state ↔
      prophecyBelow prophecy guard right level state := by
  constructor
  · rintro ⟨hGuard, hLower⟩
    refine ⟨hGuard, ?_⟩
    intro lower hLowerLevel formula hFormula
    exact hLower lower hLowerLevel formula
      ((hAgree lower hLowerLevel) ▸ hFormula)
  · rintro ⟨hGuard, hLower⟩
    refine ⟨hGuard, ?_⟩
    intro lower hLowerLevel formula hFormula
    exact hLower lower hLowerLevel formula
      ((hAgree lower hLowerLevel).symm ▸ hFormula)

/- Truncation is invisible at or below its own bound. -/
theorem prophecyBelow_levelsBelow_iff
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols assigned)
    (guard : Guard D Gamma)
    (levels : Nat -> List (Assertion D Gamma))
    {bound level : Nat}
    (hLevel : level ≤ bound)
    (state : Instance D Gamma) :
    prophecyBelow prophecy guard
        (levelsBelow levels bound) level state ↔
      prophecyBelow prophecy guard levels level state := by
  apply prophecyBelow_congr_levels prophecy guard level
  intro lower hLower
  exact levelsBelow_of_lt levels
    (Nat.lt_of_lt_of_le hLower hLevel)

/-
  At a fixed exit state, the ladder yields every level.
-/
theorem holdsAt_of_ladderInv
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols assigned)
    (guard : Guard D Gamma)
    (levels : Nat -> List (Assertion D Gamma))
    {state : Instance D Gamma}
    (hFixed : prophecy.collapse state = state)
    (hExit : ¬ guard.eval state)
    (hInvariant : ladderInv prophecy guard levels state) :
    holdsAt levels state := by
  have hAll : forall level,
      prophecyBelow prophecy guard levels level state := by
    intro level
    induction level with
    | zero =>
        exact prophecyBelow_zero prophecy guard levels state
    | succ level ih =>
        refine ⟨?_, ?_⟩
        · intro _hPositive
          rw [hFixed]
          exact hExit
        · intro lower hLower formula hFormula
          rcases Nat.lt_succ_iff_lt_or_eq.mp hLower with
            hBefore | hCurrent
          · exact ih.2 lower hBefore formula hFormula
          · subst lower
            rw [hFixed]
            exact hInvariant level ih formula hFormula
  intro level formula hFormula
  exact hInvariant level (hAll level) formula hFormula

end FixedAmbientProphecy

end Hoare

end Whiel

------------------------------------------------------------
-- Generic Fixed-Ambient Leveled Rule
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace FixedAmbientProphecy

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Gamma : UnnamedSchema A}
variable {programSymbols : Finset A}

/- Initialization of one clause at one level. -/
def InitObligation
    {assigned : Finset A}
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols assigned)
    (guard : Guard D Gamma)
    (levels : Nat -> List (Assertion D Gamma))
    (pre : Assertion D Gamma)
    (level : Nat)
    (formula : Assertion D Gamma) : Prop :=
  forall state : Instance D Gamma,
    pre state ->
      prophecyBelow prophecy guard levels level state ->
        formula state

/- Maintenance of one clause at one level. -/
def StepObligation
    (guard : Guard D Gamma)
    (body : Cmd D Gamma)
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols body.assignedSymbols)
    (levels : Nat -> List (Assertion D Gamma))
    (level : Nat)
    (formula : Assertion D Gamma) : Prop :=
  forall state : Instance D Gamma,
    ladderInv prophecy guard levels state ->
      guard.eval state ->
        prophecyBelow prophecy guard levels level state ->
          wp body formula state

/- Establishment of the postcondition at a fixed exit. -/
def TermObligation
    {assigned : Finset A}
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols assigned)
    (guard : Guard D Gamma)
    (levels : Nat -> List (Assertion D Gamma))
    (post : Assertion D Gamma) : Prop :=
  forall state : Instance D Gamma,
    prophecy.collapse state = state ->
      ¬ guard.eval state ->
        holdsAt levels state ->
          post state

/- The per-clause obligations make the ladder inductive. -/
theorem ladderInv_inductive
    {guard : Guard D Gamma}
    {body : Cmd D Gamma}
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols body.assignedSymbols)
    (levels : Nat -> List (Assertion D Gamma))
    {pre : Assertion D Gamma}
    (hInit : forall level,
      ∀ formula ∈ levels level,
        InitObligation prophecy guard levels pre
          level formula)
    (hStep : forall level,
      ∀ formula ∈ levels level,
        StepObligation guard body prophecy levels
          level formula) :
    HoareValid pre (.while guard body)
      (Assertion.andNotGuard
        (ladderInv prophecy guard levels) guard) := by
  apply hoareValid_while_of_vcs
    (inv := ladderInv prophecy guard levels)
  · intro state hPre level hBelow formula hFormula
    exact hInit level formula hFormula state hPre hBelow
  · intro before hBefore after hRun
      level hBelowAfter formula hFormula
    have hAgree : forall relation : Gamma.syms,
        relation.1 ∉ body.assignedSymbols ->
          before relation = after relation := by
      intro relation hNotAssigned
      exact
        (hRun.no_update_preservation relation
          hNotAssigned).symm
    have hBelowBefore :
        prophecyBelow prophecy guard levels level
          before :=
      (prophecyBelow_congr prophecy guard levels
        level hAgree).mpr hBelowAfter
    exact hStep level formula hFormula before
      hBefore.1 hBefore.2 hBelowBefore after hRun
  · intro state hState
    exact hState

/-
  The overlay of one program state and one prophecy state:
  program rows from the program state, every other row from
  the prophecy state.
-/
def overlay
    (symbols : Finset A)
    (programState prophecyState : Instance D Gamma) :
    Instance D Gamma :=
  fun relation =>
    if relation.1 ∈ symbols then
      programState relation
    else
      prophecyState relation

/- The overlay agrees with the program state on its rows. -/
theorem agreeOn_overlay
    (symbols : Finset A)
    (programState prophecyState : Instance D Gamma) :
    Instance.agreeOn symbols programState
      (overlay symbols programState prophecyState) := by
  intro relation hRelation
  simp [overlay, hRelation]

/- Outside the symbols, the overlay is the prophecy state. -/
theorem overlay_eq_right_of_not_mem
    (symbols : Finset A)
    (programState prophecyState : Instance D Gamma)
    (relation : Gamma.syms)
    (hRelation : relation.1 ∉ symbols) :
    overlay symbols programState prophecyState relation =
      prophecyState relation := by
  simp [overlay, hRelation]

/-
  Generic fixed-ambient Framework-II soundness. The raw
  loop and every obligation have the literal same schema.
-/
theorem hoareValid_while_of_leveled_vcs
    (programSymbols : Finset A)
    {guard : Guard D Gamma}
    {body : Cmd D Gamma}
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols body.assignedSymbols)
    (levels : Nat -> List (Assertion D Gamma))
    (pre post : Guard D Gamma)
    (hPreSymbols : pre.symbols ⊆ programSymbols)
    (hGuardSymbols : guard.symbols ⊆ programSymbols)
    (hBodySymbols : body.symbols ⊆ programSymbols)
    (hPostSymbols : post.symbols ⊆ programSymbols)
    (hInit : forall level,
      ∀ formula ∈ levels level,
        InitObligation prophecy guard levels pre.eval
          level formula)
    (hStep : forall level,
      ∀ formula ∈ levels level,
        StepObligation guard body prophecy levels
          level formula)
    (hTerm :
      TermObligation prophecy guard levels post.eval) :
    HoareValid pre.eval (.while guard body) post.eval := by
  intro initial final hPre hRun
  let exitState : Instance D Gamma :=
    prophecy.exitLift final
  let framedInitial : Instance D Gamma :=
    overlay programSymbols initial exitState
  have hAgreeInitial :
      Instance.agreeOn programSymbols initial
        framedInitial :=
    agreeOn_overlay programSymbols initial exitState
  have hPreAgree :
      Instance.agreeOn pre.symbols initial
        framedInitial :=
    Instance.agreeOn_of_subset hPreSymbols hAgreeInitial
  have hPreFramed : pre.eval framedInitial :=
    (Guard.eval_reduct_property pre hPreAgree).mp hPre
  have hLoopSymbols :
      (Cmd.while guard body).symbols ⊆
        programSymbols := by
    intro name hName
    rcases Finset.mem_union.mp hName with
      hGuard | hBody
    · exact hGuardSymbols hGuard
    · exact hBodySymbols hBody
  rcases hRun.frame hLoopSymbols hAgreeInitial with
    ⟨framedFinal, hFramedRun, hAgreeFinal⟩
  have hFinalEq : framedFinal = exitState := by
    apply Instance.ext
    intro relation
    by_cases hProgram : relation.1 ∈ programSymbols
    · exact (hAgreeFinal relation hProgram).symm.trans
        (prophecy.exitLift_agreeOn final relation
          hProgram)
    · have hNotAssigned :
          relation.1 ∉
            (Cmd.while guard body).assignedSymbols := by
        intro hAssigned
        have hSymbol : relation.1 ∈
            (Cmd.while guard body).symbols :=
          Cmd.assignedSymbols_subset_symbols
            (.while guard body) hAssigned
        exact hProgram (hLoopSymbols hSymbol)
      calc
        framedFinal relation =
            framedInitial relation :=
          hFramedRun.no_update_preservation relation
            hNotAssigned
        _ = exitState relation :=
          overlay_eq_right_of_not_mem
            programSymbols initial exitState relation
              hProgram
  subst framedFinal
  have hLadder :=
    ladderInv_inductive prophecy levels hInit hStep
  have hEnd :=
    hLadder framedInitial exitState hPreFramed
      hFramedRun
  have hFixed :
      prophecy.collapse exitState = exitState :=
    prophecy.collapse_exitLift final
  have hAll : holdsAt levels exitState :=
    holdsAt_of_ladderInv prophecy guard levels
      hFixed hEnd.2 hEnd.1
  have hPostExit : post.eval exitState :=
    hTerm exitState hFixed hEnd.2 hAll
  have hPostAgree :
      Instance.agreeOn post.symbols final
        exitState :=
    Instance.agreeOn_of_subset hPostSymbols
      (prophecy.exitLift_agreeOn final)
  exact
    (Guard.eval_reduct_property post hPostAgree).mpr
      hPostExit

end FixedAmbientProphecy

end Hoare

end Whiel

------------------------------------------------------------
-- Concrete Whiel-Name Correspondence
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace WhielNamesProphecy

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}
variable {body : Cmd D Gamma}

/-
  The exact correspondence required by one ambient loop:
  every assignment targets an ordinary name whose matching
  prophecy row exists at the same arity.
-/
structure Task
    (body : Cmd D Gamma) where
  assignedOrdinary :
    forall relation,
      relation ∈ body.assignedSymbols ->
        relation.IsOrdinary
  prophecyMem :
    forall name,
      WhielNames.ordinary name ∈
          body.assignedSymbols ->
        WhielNames.prophecy name ∈ Gamma.syms
  prophecyArity :
    forall name
      (hAssigned : WhielNames.ordinary name ∈
        body.assignedSymbols),
      Gamma.arity
          ⟨WhielNames.ordinary name,
            Cmd.assignedSymbols_subset_syms body
              hAssigned⟩ =
        Gamma.arity
          ⟨WhielNames.prophecy name,
            prophecyMem name hAssigned⟩

/- Replace assigned ordinary names by their prophecies. -/
def thetaName
    (assigned : Finset WhielNames) :
    WhielNames -> WhielNames
  | .ordinary name =>
      if .ordinary name ∈ assigned then
        .prophecy name
      else
        .ordinary name
  | .prophecy name => .prophecy name

/- Replace selected prophecies by their ordinary names. -/
def collapseName
    (assigned : Finset WhielNames) :
    WhielNames -> WhielNames
  | .ordinary name => .ordinary name
  | .prophecy name =>
      if .ordinary name ∈ assigned then
        .ordinary name
      else
        .prophecy name

namespace Task

/- Every ordinary schema row is in the program frame. -/
def programSymbols
    (_task : Task body) : Finset WhielNames :=
  Gamma.programSymbols

/- Theta as one structural self-relabeling. -/
def thetaRelabeling
    (task : Task body) :
    UnnamedSchema.Relabeling Gamma Gamma where
  name := thetaName body.assignedSymbols
  maps := by
    intro relation hRelation
    cases relation with
    | ordinary name =>
        by_cases hAssigned :
            WhielNames.ordinary name ∈
              body.assignedSymbols
        · simpa [thetaName, hAssigned] using
            task.prophecyMem name hAssigned
        · simpa [thetaName, hAssigned] using
            hRelation
    | prophecy name =>
        simpa [thetaName] using hRelation
  arity_eq := by
    intro relation hRelation
    cases relation with
    | ordinary name =>
        by_cases hAssigned :
            WhielNames.ordinary name ∈
              body.assignedSymbols
        · simpa [thetaName, hAssigned] using
            task.prophecyArity name hAssigned
        · apply congrArg Gamma.arity
          apply Subtype.ext
          simp [thetaName, hAssigned]
    | prophecy name =>
        apply congrArg Gamma.arity
        apply Subtype.ext
        simp [thetaName]

/- Collapse as the reverse structural self-relabeling. -/
def collapseRelabeling
    (task : Task body) :
    UnnamedSchema.Relabeling Gamma Gamma where
  name := collapseName body.assignedSymbols
  maps := by
    intro relation hRelation
    cases relation with
    | ordinary name =>
        simpa [collapseName] using hRelation
    | prophecy name =>
        by_cases hAssigned :
            WhielNames.ordinary name ∈
              body.assignedSymbols
        · simpa [collapseName, hAssigned] using
            Cmd.assignedSymbols_subset_syms body
              hAssigned
        · simpa [collapseName, hAssigned] using
            hRelation
  arity_eq := by
    intro relation hRelation
    cases relation with
    | ordinary name =>
        apply congrArg Gamma.arity
        apply Subtype.ext
        simp [collapseName]
    | prophecy name =>
        by_cases hAssigned :
            WhielNames.ordinary name ∈
              body.assignedSymbols
        · simpa [collapseName, hAssigned] using
            (task.prophecyArity name hAssigned).symm
        · apply congrArg Gamma.arity
          apply Subtype.ext
          simp [collapseName, hAssigned]

/- Structural theta on one quantifier-free formula. -/
def theta
    (task : Task body)
    (formula : QFAssertExpr D Gamma) :
    QFAssertExpr D Gamma :=
  formula.onRelabeling task.thetaRelabeling

/- Structural exit collapse on one formula. -/
def collapseFormula
    (task : Task body)
    (formula : QFAssertExpr D Gamma) :
    QFAssertExpr D Gamma :=
  formula.onRelabeling task.collapseRelabeling

/- Read every assigned ordinary row from its prophecy. -/
def semanticCollapse
    (task : Task body)
    (state : Instance D Gamma) : Instance D Gamma :=
  Instance.onRelabeling task.thetaRelabeling state

/- Copy assigned ordinary values into prophecy rows. -/
def exitLift
    (task : Task body)
    (state : Instance D Gamma) : Instance D Gamma :=
  Instance.onRelabeling task.collapseRelabeling state

/- The body cannot assign any prophecy row. -/
theorem prophecy_not_assigned
    (task : Task body)
    (name : ProgramNames) :
    WhielNames.prophecy name ∉
      body.assignedSymbols := by
  intro hAssigned
  exact task.assignedOrdinary
    (WhielNames.prophecy name) hAssigned

/- Every theta target is outside the body's write set. -/
theorem thetaTarget_not_assigned
    (task : Task body)
    (relation : Gamma.syms) :
    (task.thetaRelabeling.symbol relation).1 ∉
      body.assignedSymbols := by
  rcases relation with ⟨relation, hRelation⟩
  cases relation with
  | ordinary name =>
      by_cases hAssigned :
          WhielNames.ordinary name ∈
            body.assignedSymbols
      · simp only [UnnamedSchema.Relabeling.symbol,
          thetaRelabeling, thetaName, hAssigned,
          if_pos]
        exact task.prophecy_not_assigned name
      · simp [UnnamedSchema.Relabeling.symbol,
          thetaRelabeling, thetaName, hAssigned]
  | prophecy name =>
      simp only [UnnamedSchema.Relabeling.symbol,
        thetaRelabeling, thetaName]
      exact task.prophecy_not_assigned name

/- Semantic collapse depends only on unassigned rows. -/
theorem semanticCollapse_congr
    (task : Task body)
    (left right : Instance D Gamma)
    (hAgree : forall relation : Gamma.syms,
      relation.1 ∉ body.assignedSymbols ->
        left relation = right relation) :
    task.semanticCollapse left =
      task.semanticCollapse right := by
  apply Instance.ext
  intro relation
  unfold semanticCollapse Instance.onRelabeling
  rw [hAgree (task.thetaRelabeling.symbol relation)
    (task.thetaTarget_not_assigned relation)]

/- Exit lifting preserves every ordinary schema row. -/
theorem exitLift_agreeOn
    (task : Task body)
    (state : Instance D Gamma) :
    Instance.agreeOn task.programSymbols state
      (task.exitLift state) := by
  intro relation hProgram
  have hOrdinary : relation.1.IsOrdinary :=
    (Finset.mem_filter.mp hProgram).2
  cases hRelation : relation.1 with
  | ordinary name =>
      symm
      unfold exitLift
      apply Instance.onRelabeling_apply_of_name_eq
      simp [collapseRelabeling, collapseName,
        hRelation]
  | prophecy name =>
      simp [WhielNames.IsOrdinary, hRelation]
        at hOrdinary

private theorem collapse_theta_name
    (_task : Task body)
    (relation : WhielNames) :
    collapseName body.assignedSymbols
        (thetaName body.assignedSymbols relation) =
      collapseName body.assignedSymbols relation := by
  cases relation with
  | ordinary name =>
      by_cases hAssigned :
          WhielNames.ordinary name ∈
            body.assignedSymbols
      · simp [thetaName, collapseName, hAssigned]
      · simp [thetaName, collapseName, hAssigned]
  | prophecy name =>
      simp [thetaName]

private theorem theta_collapse_name
    (_task : Task body)
    (relation : WhielNames) :
    thetaName body.assignedSymbols
        (collapseName body.assignedSymbols relation) =
      thetaName body.assignedSymbols relation := by
  cases relation with
  | ordinary name =>
      simp [collapseName]
  | prophecy name =>
      by_cases hAssigned :
          WhielNames.ordinary name ∈
            body.assignedSymbols
      · simp [collapseName, thetaName, hAssigned]
      · simp [collapseName, thetaName, hAssigned]

/- Collapsing an exit-lifted state is a fixed point. -/
theorem semanticCollapse_exitLift
    (task : Task body)
    (state : Instance D Gamma) :
    task.semanticCollapse (task.exitLift state) =
      task.exitLift state := by
  rw [semanticCollapse, exitLift,
    ← Instance.onRelabeling_comp]
  apply Instance.onRelabeling_eq_of_name_eq
  intro relation
  simpa [UnnamedSchema.Relabeling.comp,
    thetaRelabeling, collapseRelabeling] using
    task.collapse_theta_name relation

/- Exit lifting after collapse is absorbed by collapse. -/
theorem exitLift_semanticCollapse
    (task : Task body)
    (state : Instance D Gamma) :
    task.exitLift (task.semanticCollapse state) =
      task.semanticCollapse state := by
  rw [exitLift, semanticCollapse,
    ← Instance.onRelabeling_comp]
  apply Instance.onRelabeling_eq_of_name_eq
  intro relation
  simpa [UnnamedSchema.Relabeling.comp,
    thetaRelabeling, collapseRelabeling] using
    task.theta_collapse_name relation

/- A collapse fixed point is also exit-lift fixed. -/
theorem exitLift_eq_of_semanticCollapse_eq
    (task : Task body)
    (state : Instance D Gamma)
    (hFixed : task.semanticCollapse state = state) :
    task.exitLift state = state := by
  calc
    task.exitLift state =
        task.exitLift (task.semanticCollapse state) := by
      exact congrArg task.exitLift hFixed.symm
    _ = task.semanticCollapse state :=
      task.exitLift_semanticCollapse state
    _ = state := hFixed

/- Package the generic fixed-ambient collapse contract. -/
def prophecyCollapse
    (task : Task body) :
    FixedAmbientProphecy.Collapse
      (D := D) (Gamma := Gamma)
      task.programSymbols body.assignedSymbols where
  collapse := task.semanticCollapse
  collapse_congr := task.semanticCollapse_congr
  exitLift := task.exitLift
  exitLift_agreeOn := task.exitLift_agreeOn
  collapse_exitLift := task.semanticCollapse_exitLift

/- Structural theta evaluates through semantic collapse. -/
theorem theta_eval_iff
    (task : Task body)
    (formula : QFAssertExpr D Gamma)
    (state : Instance D Gamma) :
    (task.theta formula).eval state ↔
      formula.eval (task.semanticCollapse state) := by
  exact Guard.eval_onRelabeling
    task.thetaRelabeling formula state

/- Structural collapse evaluates through exit lifting. -/
theorem collapseFormula_eval_iff
    (task : Task body)
    (formula : QFAssertExpr D Gamma)
    (state : Instance D Gamma) :
    (task.collapseFormula formula).eval state ↔
      formula.eval (task.exitLift state) := by
  exact Guard.eval_onRelabeling
    task.collapseRelabeling formula state

/- Collapse formulas are neutral at fixed points. -/
theorem collapseFormula_eval_iff_of_fixed
    (task : Task body)
    (formula : QFAssertExpr D Gamma)
    (state : Instance D Gamma)
    (hFixed : task.semanticCollapse state = state) :
    (task.collapseFormula formula).eval state ↔
      formula.eval state := by
  rw [task.collapseFormula_eval_iff,
    task.exitLift_eq_of_semanticCollapse_eq state
      hFixed]

end Task

end WhielNamesProphecy

end Hoare

end Whiel
