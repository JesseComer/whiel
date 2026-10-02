-- Author: Jesse Comer
import Databases.Core.Notation
import Whiel.Vampire.ExactReconstruction

/-
  Focused checks for exact NameEnv-driven application of a
  raw leancheck theorem. The positive cases exercise mixed
  relation and function arities, nullary constants, a carrier
  spelling its own names, connective association, equality
  orientation, and symbol-free theorems both with and without
  carrier infrastructure. Negative cases check the fail-closed
  telescope guards.
-/

------------------------------------------------------------
-- Mixed-Arity Closed Entailment
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace ExactReconstruction

inductive Rel
| flag
| edge
| cube
deriving DecidableEq

instance : Repr Rel where
  reprPrec
  | .flag, _ => "flag"
  | .edge, _ => "edge"
  | .cube, _ => "cube"

instance : RelationNames Rel where
  decEq := inferInstance
  repr := inferInstance

instance : Vampire.SolverName Rel where
  solverName := Vampire.SolverName.ofRepr "r"

inductive Fun
| constant
| next
| pair
deriving DecidableEq

instance : Repr Fun where
  reprPrec
  | .constant, _ => "constant"
  | .next, _ => "next"
  | .pair, _ => "pair"

instance : FunctionNames Fun where
  decEq := inferInstance
  repr := inferInstance

instance : Vampire.SolverName Fun where
  solverName := Vampire.SolverName.ofRepr "f"

def signature : Signature Rel Fun :=
  sig![
    rels:
      Rel.flag (arity: 0),
      Rel.edge (arity: 2),
      Rel.cube (arity: 3)
    funs:
      Fun.constant (arity: 0),
      Fun.next (arity: 1),
      Fun.pair (arity: 2)
  ]

def flagSymbol : Signature.Rel signature :=
  signature.sym Rel.flag

def edgeSymbol : Signature.Rel signature :=
  signature.sym Rel.edge

def cubeSymbol : Signature.Rel signature :=
  signature.sym Rel.cube

def constantSymbol : Signature.Fun signature :=
  signature.func Fun.constant

def nextSymbol : Signature.Fun signature :=
  signature.func Fun.next

def pairSymbol : Signature.Fun signature :=
  signature.func Fun.pair

def constantTerm : FOL.Term signature :=
  .func constantSymbol .nil

def nextTerm
    (term : FOL.Term signature) :
    FOL.Term signature :=
  .func nextSymbol (.cons term .nil)

def pairTerm
    (left right : FOL.Term signature) :
    FOL.Term signature :=
  .func pairSymbol (.cons left (.cons right .nil))

def flagFormula : FOL.Formula signature :=
  .rel flagSymbol .nil

def edgeFormula
    (left right : FOL.Term signature) :
    FOL.Formula signature :=
  .rel edgeSymbol (.cons left (.cons right .nil))

def cubeFormula
    (first second third : FOL.Term signature) :
    FOL.Formula signature :=
  .rel cubeSymbol
    (.cons first (.cons second (.cons third .nil)))

def firstAxiom : FOL.Sentence signature :=
  ⟨.forall_ 0
      (.imp
        (edgeFormula constantTerm (.var 0))
        flagFormula),
    by decide⟩

def secondAxiom : FOL.Sentence signature :=
  ⟨.forall_ 0 (.forall_ 1
      (.imp
        (cubeFormula constantTerm
          (nextTerm (.var 0))
          (pairTerm (.var 0) (.var 1)))
        (edgeFormula constantTerm (.var 1)))),
    by decide⟩

def conjecture : FOL.Sentence signature :=
  ⟨.forall_ 0 (.forall_ 1
      (.imp
        (cubeFormula constantTerm
          (nextTerm (.var 0))
          (pairTerm (.var 0) (.var 1)))
        flagFormula)),
    by decide⟩

def entailment : FOL.SentenceEntailment signature where
  axioms := [firstAxiom, secondAxiom]
  conjecture := conjecture

def exactEnv : Vampire.TPTP.NameEnv Rel Fun :=
  { relNames :=
      [(Rel.edge, "r_edge"), (Rel.flag, "r_flag"),
        (Rel.cube, "r_cube")]
    funNames :=
      [(Fun.constant, "f_constant"),
        (Fun.next, "f_next"), (Fun.pair, "f_pair")] }

run_cmd
  let computed :=
    Vampire.TPTP.NameEnv.ofEntailment entailment
  unless decide (exactEnv.relNames = computed.relNames) &&
      decide (exactEnv.funNames = computed.funNames) do
    throwError "mixed exact NameEnv fixture drifted"

universe u

theorem rawMixedProof
    {ι : Type u}
    [Inhabited ι]
    {«_r_flag» : Prop}
    {«_r_edge» : ι → ι → Prop}
    {«_r_cube» : ι → ι → ι → Prop}
    {«_f_constant» : ι}
    {«_f_next» : ι → ι}
    {«_f_pair» : ι → ι → ι} :
    ((∀ x : ι,
        «_r_edge» «_f_constant» x → «_r_flag») ∧
      (∀ x y : ι,
        «_r_cube» «_f_constant» («_f_next» x)
            («_f_pair» x y) →
          «_r_edge» «_f_constant» y)) →
      ∀ x y : ι,
        «_r_cube» «_f_constant» («_f_next» x)
            («_f_pair» x y) →
          «_r_flag» := by
  intro axioms x y cube
  exact axioms.1 y (axioms.2 x y cube)

theorem rawMixedWithoutInhabited
    {ι : Type u}
    {«_r_flag» : Prop}
    {«_r_edge» : ι → ι → Prop}
    {«_r_cube» : ι → ι → ι → Prop}
    {«_f_constant» : ι}
    {«_f_next» : ι → ι}
    {«_f_pair» : ι → ι → ι} :
    ((∀ x : ι,
        «_r_edge» «_f_constant» x → «_r_flag») ∧
      (∀ x y : ι,
        «_r_cube» «_f_constant» («_f_next» x)
            («_f_pair» x y) →
          «_r_edge» «_f_constant» y)) →
      ∀ x y : ι,
        «_r_cube» «_f_constant» («_f_next» x)
            («_f_pair» x y) →
          «_r_flag» := by
  intro axioms x y cube
  exact axioms.1 y (axioms.2 x y cube)

inductive Carrier
| point
deriving DecidableEq, Inhabited, Repr

instance : Domain Carrier where
  inhabited := inferInstance
  decEq := inferInstance
  repr := inferInstance

theorem mixedEntailmentValid :
    entailment.Valid (D := Carrier) := by
  apply
    FOL.SentenceEntailment.valid_of_implicationShallowValid
  intro ι _ model _assignment
  exact_reconstruction rawMixedProof using
    (Vampire.TPTP.NameEnv.ofEntailment entailment, model)

------------------------------------------------------------
-- Association and Collision Cases
------------------------------------------------------------

def associationAxiom : FOL.Sentence signature :=
  ⟨.and
      (.and flagFormula
        (edgeFormula constantTerm constantTerm))
      (cubeFormula constantTerm constantTerm
        constantTerm),
    by decide⟩

def associationConjecture : FOL.Sentence signature :=
  ⟨.or
      (.or flagFormula
        (edgeFormula constantTerm constantTerm))
      (cubeFormula constantTerm constantTerm
        constantTerm),
    by decide⟩

def associationEntailment :
    FOL.SentenceEntailment signature where
  axioms := [associationAxiom]
  conjecture := associationConjecture

def associationEnv : Vampire.TPTP.NameEnv Rel Fun :=
  { relNames :=
      [(Rel.flag, "r_flag"), (Rel.edge, "r_edge"),
        (Rel.cube, "r_cube")]
    funNames := [(Fun.constant, "f_constant")] }

run_cmd
  let computed :=
    Vampire.TPTP.NameEnv.ofEntailment associationEntailment
  unless decide
      (associationEnv.relNames = computed.relNames) &&
      decide (associationEnv.funNames = computed.funNames) do
    throwError "association exact NameEnv fixture drifted"

theorem rawAssociationProof
    {ι : Type u}
    [Inhabited ι]
    {«_r_flag» : Prop}
    {«_r_edge» : ι → ι → Prop}
    {«_r_cube» : ι → ι → ι → Prop}
    {«_f_constant» : ι} :
    («_r_flag» ∧
        «_r_edge» «_f_constant» «_f_constant» ∧
        «_r_cube» «_f_constant» «_f_constant»
          «_f_constant») →
      «_r_flag» ∨
        «_r_edge» «_f_constant» «_f_constant» ∨
        «_r_cube» «_f_constant» «_f_constant»
          «_f_constant» := by
  intro hypothesis
  exact Or.inl hypothesis.1

theorem associationEntailmentValid :
    associationEntailment.Valid (D := Carrier) := by
  apply
    FOL.SentenceEntailment.valid_of_implicationShallowValid
  intro ι _ model _assignment
  exact_reconstruction rawAssociationProof using
    (associationEnv, model)

inductive CollisionRel
| edgeDash
| edgeUnderscore
deriving DecidableEq

instance : Repr CollisionRel where
  reprPrec
  | .edgeDash, _ => "Edge-X"
  | .edgeUnderscore, _ => "Edge_X"

instance : RelationNames CollisionRel where
  decEq := inferInstance
  repr := inferInstance

/-
  The renderer no longer makes names distinct, so a carrier
  whose display spellings differ only outside the identifier
  alphabet has to spell its solver names apart itself. These
  are the two names the old freshening pass produced.
-/
instance : Vampire.SolverName CollisionRel where
  solverName
  | .edgeDash => "r_Edge_X"
  | .edgeUnderscore => "r_Edge_X_0"

inductive CollisionFun
| widgetDash
| widgetUnderscore
deriving DecidableEq

instance : Repr CollisionFun where
  reprPrec
  | .widgetDash, _ => "Widget-X"
  | .widgetUnderscore, _ => "Widget_X"

instance : FunctionNames CollisionFun where
  decEq := inferInstance
  repr := inferInstance

instance : Vampire.SolverName CollisionFun where
  solverName
  | .widgetDash => "f_Widget_X"
  | .widgetUnderscore => "f_Widget_X_0"

def collisionSignature :
    Signature CollisionRel CollisionFun :=
  sig![
    rels:
      CollisionRel.edgeDash (arity: 0),
      CollisionRel.edgeUnderscore (arity: 0)
    funs:
      CollisionFun.widgetDash (arity: 0),
      CollisionFun.widgetUnderscore (arity: 0)
  ]

def edgeDashSymbol : Signature.Rel collisionSignature :=
  collisionSignature.sym CollisionRel.edgeDash

def edgeUnderscoreSymbol :
    Signature.Rel collisionSignature :=
  collisionSignature.sym CollisionRel.edgeUnderscore

def widgetDashSymbol :
    Signature.Fun collisionSignature :=
  collisionSignature.func CollisionFun.widgetDash

def widgetUnderscoreSymbol :
    Signature.Fun collisionSignature :=
  collisionSignature.func CollisionFun.widgetUnderscore

def collisionPremise : FOL.Formula collisionSignature :=
  .and (.rel edgeDashSymbol .nil)
    (.and (.rel edgeUnderscoreSymbol .nil)
      (.and
        (.eq (.func widgetDashSymbol .nil)
          (.func widgetDashSymbol .nil))
        (.eq (.func widgetUnderscoreSymbol .nil)
          (.func widgetUnderscoreSymbol .nil))))

def collisionConjecture : FOL.Sentence collisionSignature :=
  ⟨.imp collisionPremise collisionPremise, by decide⟩

def collisionEntailment :
    FOL.SentenceEntailment collisionSignature where
  axioms := []
  conjecture := collisionConjecture

def collisionEnv :
    Vampire.TPTP.NameEnv CollisionRel CollisionFun :=
  { relNames :=
      [(CollisionRel.edgeDash, "r_Edge_X"),
        (CollisionRel.edgeUnderscore, "r_Edge_X_0")]
    funNames :=
      [(CollisionFun.widgetDash, "f_Widget_X"),
        (CollisionFun.widgetUnderscore,
          "f_Widget_X_0")] }

run_cmd
  let computed :=
    Vampire.TPTP.NameEnv.ofEntailment collisionEntailment
  unless decide
      (collisionEnv.relNames = computed.relNames) &&
      decide (collisionEnv.funNames = computed.funNames) do
    throwError "collision exact NameEnv fixture drifted"

theorem rawCollisionProof
    {ι : Type u}
    [Inhabited ι]
    {«_r_Edge_X» «_r_Edge_X_0» : Prop}
    {«_f_Widget_X» «_f_Widget_X_0» : ι} :
    True →
      («_r_Edge_X» ∧ «_r_Edge_X_0» ∧
          «_f_Widget_X» = «_f_Widget_X» ∧
          «_f_Widget_X_0» = «_f_Widget_X_0») →
        «_r_Edge_X» ∧ «_r_Edge_X_0» ∧
          «_f_Widget_X» = «_f_Widget_X» ∧
          «_f_Widget_X_0» = «_f_Widget_X_0» := by
  intro _ hypothesis
  exact hypothesis

theorem collisionEntailmentValid :
    collisionEntailment.Valid (D := Carrier) := by
  apply
    FOL.SentenceEntailment.valid_of_implicationShallowValid
  intro ι _ model _assignment
  exact_reconstruction rawCollisionProof using
    (Vampire.TPTP.NameEnv.ofEntailment
      collisionEntailment, model)

------------------------------------------------------------
-- Equality Orientation
------------------------------------------------------------

/-
  The solver normalises the orientation of an equality
  literal, so a reconstructed statement can differ from the
  Lean-owned one by `Eq.symm` alone. Two shapes meet that in
  practice: a selection whose indices descend, and the active
  domain of a constant.
-/

/- Selection body `edge #0 #1 ∧ #1 = #0` (descending). -/
def descendingSelection : FOL.Sentence signature :=
  ⟨.forall_ 0 (.forall_ 1
      (.and (edgeFormula (.var 0) (.var 1))
        (.eq (.var 1) (.var 0)))),
    by decide⟩

/- Its ascending twin `edge #0 #1 ∧ #0 = #1`. -/
def ascendingSelection : FOL.Sentence signature :=
  ⟨.forall_ 0 (.forall_ 1
      (.and (edgeFormula (.var 0) (.var 1))
        (.eq (.var 0) (.var 1)))),
    by decide⟩

def descendingEntailment :
    FOL.SentenceEntailment signature where
  axioms := [descendingSelection]
  conjecture := descendingSelection

def ascendingEntailment :
    FOL.SentenceEntailment signature where
  axioms := [ascendingSelection]
  conjecture := ascendingSelection

/-
  The solver's orientation for a variable equality: the
  lower-numbered variable first, whichever way the source
  wrote it. One raw theorem therefore serves both twins.
-/
theorem rawSelectionOrientation
    {ι : Type u}
    [Inhabited ι]
    {«_r_edge» : ι → ι → Prop} :
    (∀ v0 v1 : ι, «_r_edge» v0 v1 ∧ v0 = v1) →
      ∀ v0 v1 : ι, «_r_edge» v0 v1 ∧ v0 = v1 :=
  fun hypothesis => hypothesis

theorem descendingSelectionValid :
    descendingEntailment.Valid (D := Carrier) := by
  apply
    FOL.SentenceEntailment.valid_of_implicationShallowValid
  intro ι _ model _assignment
  exact_reconstruction rawSelectionOrientation using
    (Vampire.TPTP.NameEnv.ofEntailment descendingEntailment,
      model)

theorem ascendingSelectionValid :
    ascendingEntailment.Valid (D := Carrier) := by
  apply
    FOL.SentenceEntailment.valid_of_implicationShallowValid
  intro ι _ model _assignment
  exact_reconstruction rawSelectionOrientation using
    (Vampire.TPTP.NameEnv.ofEntailment ascendingEntailment,
      model)

/- Active domain of a constant: `edge c #0 → #0 = c`. -/
def constantDomainSentence : FOL.Sentence signature :=
  ⟨.forall_ 0
      (.imp (edgeFormula constantTerm (.var 0))
        (.eq (.var 0) constantTerm)),
    by decide⟩

def constantDomainEntailment :
    FOL.SentenceEntailment signature where
  axioms := [constantDomainSentence]
  conjecture := constantDomainSentence

/- The solver puts the non-variable term first. -/
theorem rawConstantOrientation
    {ι : Type u}
    [Inhabited ι]
    {«_r_edge» : ι → ι → Prop}
    {«_f_constant» : ι} :
    (∀ x : ι,
        «_r_edge» «_f_constant» x → «_f_constant» = x) →
      ∀ x : ι,
        «_r_edge» «_f_constant» x → «_f_constant» = x :=
  fun hypothesis => hypothesis

theorem constantDomainValid :
    constantDomainEntailment.Valid (D := Carrier) := by
  apply
    FOL.SentenceEntailment.valid_of_implicationShallowValid
  intro ι _ model _assignment
  exact_reconstruction rawConstantOrientation using
    (Vampire.TPTP.NameEnv.ofEntailment
        constantDomainEntailment,
      model)

------------------------------------------------------------
-- Symbol-Free and Rejection Checks
------------------------------------------------------------

inductive EmptyRel
deriving DecidableEq, Repr

instance : RelationNames EmptyRel where
  decEq := inferInstance
  repr := inferInstance

instance : Vampire.SolverName EmptyRel where
  solverName := fun r => nomatch r

inductive EmptyFun
deriving DecidableEq, Repr

instance : FunctionNames EmptyFun where
  decEq := inferInstance
  repr := inferInstance

instance : Vampire.SolverName EmptyFun where
  solverName := fun f => nomatch f

def emptySignature : Signature EmptyRel EmptyFun :=
  sig![rels: funs:]

def emptyEntailment :
    FOL.SentenceEntailment emptySignature where
  axioms := []
  conjecture := ⟨.top, by decide⟩

def emptyEnv : Vampire.TPTP.NameEnv EmptyRel EmptyFun :=
  { relNames := []
    funNames := [] }

run_cmd
  let computed :=
    Vampire.TPTP.NameEnv.ofEntailment emptyEntailment
  unless decide (emptyEnv.relNames = computed.relNames) &&
      decide (emptyEnv.funNames = computed.funNames) do
    throwError "symbol-free exact NameEnv fixture drifted"

theorem rawSymbolFreeProof : True → True := by
  intro _
  trivial

theorem rawSymbolFreeWithCarrier
    {ι : Type u}
    [Inhabited ι] : True → True := by
  intro _
  trivial

def carrierOnlyEntailment :
    FOL.SentenceEntailment emptySignature where
  axioms := []
  conjecture :=
    ⟨.forall_ 0 (.eq (.var 0) (.var 0)), by decide⟩

theorem rawCarrierOnlyProof
    {ι : Type u}
    [Inhabited ι] : True → ∀ x : ι, x = x := by
  intro _ x
  rfl

theorem symbolFreeEntailmentValid :
    emptyEntailment.Valid (D := Carrier) := by
  apply
    FOL.SentenceEntailment.valid_of_implicationShallowValid
  intro ι _ model _assignment
  exact_reconstruction rawSymbolFreeProof using
    (emptyEnv, model)

theorem carrierOnlyEntailmentValid :
    carrierOnlyEntailment.Valid (D := Carrier) := by
  apply
    FOL.SentenceEntailment.valid_of_implicationShallowValid
  intro ι _ model _assignment
  exact_reconstruction rawCarrierOnlyProof using
    (emptyEnv, model)

inductive NullaryRel
| flag
deriving DecidableEq

instance : Repr NullaryRel where
  reprPrec
  | .flag, _ => "flag"

instance : RelationNames NullaryRel where
  decEq := inferInstance
  repr := inferInstance

instance : Vampire.SolverName NullaryRel where
  solverName := Vampire.SolverName.ofRepr "r"

inductive NullaryFun
deriving DecidableEq, Repr

instance : FunctionNames NullaryFun where
  decEq := inferInstance
  repr := inferInstance

instance : Vampire.SolverName NullaryFun where
  solverName := fun f => nomatch f

def nullarySignature : Signature NullaryRel NullaryFun :=
  sig![rels: NullaryRel.flag (arity: 0) funs:]

def nullaryFlag : FOL.Formula nullarySignature :=
  .rel (nullarySignature.sym NullaryRel.flag) .nil

def nullaryEntailment :
    FOL.SentenceEntailment nullarySignature where
  axioms := []
  conjecture :=
    ⟨.imp nullaryFlag nullaryFlag, by decide⟩

def nullaryEnv :
    Vampire.TPTP.NameEnv NullaryRel NullaryFun :=
  { relNames := [(NullaryRel.flag, "r_flag")]
    funNames := [] }

theorem rawNullaryProof
    {«_r_flag» : Prop} :
    True → («_r_flag» → «_r_flag») := by
  intro _ hypothesis
  exact hypothesis

theorem nullaryEntailmentValid :
    nullaryEntailment.Valid (D := Carrier) := by
  apply
    FOL.SentenceEntailment.valid_of_implicationShallowValid
  intro ι _ model _assignment
  exact_reconstruction rawNullaryProof using
    (nullaryEnv, model)

def collidingEnv : Vampire.TPTP.NameEnv Rel Fun where
  relNames :=
    [(Rel.flag, "r_same"), (Rel.edge, "r_same")]
  funNames := []

def repeatedSourceEnv : Vampire.TPTP.NameEnv Rel Fun where
  relNames :=
    [(Rel.flag, "r_flag"),
      (Rel.flag, "r_flag_copy")]
  funNames := []

def crossKindCollisionEnv : Vampire.TPTP.NameEnv Rel Fun where
  relNames := [(Rel.flag, "shared")]
  funNames := [(Fun.constant, "shared")]

theorem rawMissingBinder
    {ι : Type u}
    [Inhabited ι]
    {«_r_flag» : Prop}
    {«_r_edge» : ι → ι → Prop} : True := by
  trivial

theorem rawExtraBinder
    {ι : Type u}
    [Inhabited ι]
    {«_r_extra» : Prop} : True := by
  trivial

theorem rawRepeatedSource
    {ι : Type u}
    [Inhabited ι]
    {«_r_flag» «_r_flag_copy» : Prop} : True := by
  trivial

theorem rawWrongArity
    {ι : Type u}
    [Inhabited ι]
    {«_r_flag» : ι → Prop} : True := by
  trivial

theorem rawExtraFunctionBinder
    {ι : Type u}
    [Inhabited ι]
    {«_r_flag» : Prop}
    {«_r_edge» : ι → ι → Prop}
    {«_r_cube» : ι → ι → ι → Prop}
    {«_f_constant» : ι}
    {«_f_next» : ι → ι}
    {«_f_pair» : ι → ι → ι}
    {«_f_extra» : ι} : True := by
  trivial

theorem rawWrongFunctionArity
    {ι : Type u}
    [Inhabited ι]
    {«_r_flag» : Prop}
    {«_r_edge» : ι → ι → Prop}
    {«_r_cube» : ι → ι → ι → Prop}
    {«_f_constant» : ι}
    {«_f_next» : ι → ι → ι}
    {«_f_pair» : ι → ι → ι} : True := by
  trivial

theorem rawWrongTarget
    {ι : Type u}
    [Inhabited ι]
    {«_r_flag» : Prop}
    {«_r_edge» : ι → ι → Prop}
    {«_r_cube» : ι → ι → ι → Prop}
    {«_f_constant» : ι}
    {«_f_next» : ι → ι}
    {«_f_pair» : ι → ι → ι} : True := by
  trivial

theorem rawPermutedProof
    {ι : Type u}
    {«_f_pair» : ι → ι → ι}
    {«_r_cube» : ι → ι → ι → Prop}
    [Inhabited ι]
    {«_f_constant» : ι}
    {«_r_flag» : Prop}
    {«_f_next» : ι → ι}
    {«_r_edge» : ι → ι → Prop} :
    ((∀ x : ι,
        «_r_edge» «_f_constant» x → «_r_flag») ∧
      (∀ x y : ι,
        «_r_cube» «_f_constant» («_f_next» x)
            («_f_pair» x y) →
          «_r_edge» «_f_constant» y)) →
      ∀ x y : ι,
        «_r_cube» «_f_constant» («_f_next» x)
            («_f_pair» x y) →
          «_r_flag» := by
  intro axioms x y cube
  exact axioms.1 y (axioms.2 x y cube)

theorem rawResidualBinder
    {ι : Type u}
    [Inhabited ι]
    {«_r_flag» : Prop}
    {«_r_edge» : ι → ι → Prop}
    {«_r_cube» : ι → ι → ι → Prop}
    {«_f_constant» : ι}
    {«_f_next» : ι → ι}
    {«_f_pair» : ι → ι → ι} :
    True → ∀ {«_r_residual» : Prop}, True := by
  intro _ _
  trivial

theorem rawAnonymousResidualBinder
    {ι : Type u}
    [Inhabited ι]
    {«_r_flag» : Prop}
    {«_r_edge» : ι → ι → Prop}
    {«_r_cube» : ι → ι → ι → Prop}
    {«_f_constant» : ι}
    {«_f_next» : ι → ι}
    {«_f_pair» : ι → ι → ι} :
    True → ∀ {_ : Prop}, True := by
  intro _ _
  trivial

def flagOnlyEnv : Vampire.TPTP.NameEnv Rel Fun where
  relNames := [(Rel.flag, "r_flag")]
  funNames := []

theorem rawNoCarrier
    {«_r_flag» : Prop} : True := by
  trivial

example : entailment.ImplicationShallowValid := by
  intro ι _ model _assignment
  fail_if_success
    exact_reconstruction rawMixedProof using
      (collidingEnv, model)
  fail_if_success
    exact_reconstruction rawMissingBinder using
      (exactEnv, model)
  fail_if_success
    exact_reconstruction rawRepeatedSource using
      (repeatedSourceEnv, model)
  fail_if_success
    exact_reconstruction rawMixedProof using
      (crossKindCollisionEnv, model)
  fail_if_success
    exact_reconstruction rawExtraBinder using
      (exactEnv, model)
  fail_if_success
    exact_reconstruction rawWrongArity using
      (exactEnv, model)
  fail_if_success
    exact_reconstruction rawExtraFunctionBinder using
      (exactEnv, model)
  fail_if_success
    exact_reconstruction rawWrongFunctionArity using
      (exactEnv, model)
  fail_if_success
    exact_reconstruction rawResidualBinder using
      (exactEnv, model)
  fail_if_success
    exact_reconstruction rawAnonymousResidualBinder using
      (exactEnv, model)
  exact_reconstruction rawMixedProof using
    (exactEnv, model)

example : entailment.ImplicationShallowValid := by
  intro ι _ model _assignment
  exact_reconstruction rawPermutedProof using
    (exactEnv, model)

example : entailment.ImplicationShallowValid := by
  intro ι _ model _assignment
  exact_reconstruction rawMixedWithoutInhabited using
    (exactEnv, model)

example : emptyEntailment.ImplicationShallowValid := by
  intro ι _ model _assignment
  exact_reconstruction rawSymbolFreeWithCarrier using
    (emptyEnv, model)

example : emptyEntailment.ImplicationShallowValid := by
  intro ι _ model _assignment
  exact_reconstruction rawSymbolFreeProof using
    (emptyEnv, model)

#print axioms mixedEntailmentValid
#print axioms associationEntailmentValid
#print axioms collisionEntailmentValid
#print axioms descendingSelectionValid
#print axioms ascendingSelectionValid
#print axioms constantDomainValid
#print axioms symbolFreeEntailmentValid
#print axioms carrierOnlyEntailmentValid
#print axioms nullaryEntailmentValid

end ExactReconstruction
end Tests
end Synthesis
end Whiel
