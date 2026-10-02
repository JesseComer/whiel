-- Author: Jesse Comer
import Whiel.AssertExpr.ToRelCalc
import Whiel.Synthesis.Runtime.Task
import Whiel.Vampire.QFEntailment
import Whiel.Vampire.StableEncoding

/-
  The theorem-connected Lean side of reusable solver-body
  preparation.

  A task-specific worker registry supplies source formulas.
  Rust sends stable source and symbol keys; it never sends
  Lean syntax for dynamic elaboration.
-/

------------------------------------------------------------
-- Solver Body Sources
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Exact Lean source accepted by the common body boundary. -/
inductive SolverBodySource
    (D : Type)
    [Domain D]
    (Γ : UnnamedSchema A) where
| qf
    (sourceId : String)
    (formula : QFAssertExpr D Γ)
| assert
    (sourceId : String)
    (formula : AssertExpr D Γ)
    (noBound : formula.NoBoundSymbols)

namespace SolverBodySource

/- Stable source identity supplied by the task registry. -/
def sourceId : SolverBodySource D Γ → String
| .qf sourceId _ => sourceId
| .assert sourceId _ _ => sourceId

/- Wire identity of the trusted Lean source variant. -/
def sourceKind : SolverBodySource D Γ → String
| .qf _ _ => "quantifier_free"
| .assert _ _ _ => "assert"

/- Convert either accepted source form to QF syntax. -/
def toQF : SolverBodySource D Γ → QFAssertExpr D Γ
| .qf _ formula => formula
| .assert _ formula noBound => formula.toQFOfNoBound noBound

/- Convert an accepted source to its RelCalc sentence. -/
def toSentence
    (source : SolverBodySource D Γ) :
    RelCalc.Sentence D Γ :=
  source.toQF.toRelCalcSentence

end SolverBodySource

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Empty-Instance Entailment Checks
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  One source-level counterexample at a nullary assignment.
-/
def IsEmptyCounterexample
    (E : QFEntailment (D := D) Γ)
    (χ : Instance.NullaryAssignment Γ) : Prop :=
  E.constants = ∅ ∧
    (∀ φ ∈ E.axioms,
      φ.eval (Instance.ofNullaryAssignment χ)) ∧
    ¬ E.conjecture.eval
      (Instance.ofNullaryAssignment χ)

instance
    (E : QFEntailment (D := D) Γ)
    (χ : Instance.NullaryAssignment Γ) :
    Decidable (IsEmptyCounterexample E χ) := by
  unfold IsEmptyCounterexample
  infer_instance

/- Set one nullary choice without changing the others. -/
private def setNullaryChoice
    (χ : Instance.NullaryAssignment Γ)
    (X : Instance.NullarySymbol Γ)
    (value : Bool) :
    Instance.NullaryAssignment Γ :=
  fun Y => if Y.1.1 = X.1.1 then value else χ Y

/- Enumerate choices for a list of nullary symbols. -/
private def enumerateNullaryAssignments :
    List (Instance.NullarySymbol Γ) →
      List (Instance.NullaryAssignment Γ)
| [] => [fun _ => Bool.false]
| X :: Xs =>
    (enumerateNullaryAssignments Xs).flatMap fun χ =>
      [ setNullaryChoice χ X Bool.false,
        setNullaryChoice χ X Bool.true ]

/- List all nullary symbols in schema order. -/
private def orderedNullarySymbols
    [LinearOrder A]
    (Γ : UnnamedSchema A) :
    List (Instance.NullarySymbol Γ) :=
  Γ.syms.attach.sort.filterMap fun X =>
    if hAr : Γ.arity X = 0 then
      some ⟨X, hAr⟩
    else
      none

/-
  Return the first exact empty-instance assignment found.
-/
def findEmptyCounterexample?
    [LinearOrder A]
    (E : QFEntailment (D := D) Γ) :
    Option (Instance.NullaryAssignment Γ) :=
  (enumerateNullaryAssignments
    (orderedNullarySymbols Γ)).find?
    (fun χ => decide (IsEmptyCounterexample E χ))

/-
  Return the first adom-empty countermodel found, whatever
  constants the entailment mentions (the assignment the
  constant-blind `QFEntailment.adomEmptyCounterexample?`
  decides on).
-/
def findAdomEmptyCounterexample?
    [LinearOrder A]
    (E : QFEntailment (D := D) Γ) :
    Option (Instance.NullaryAssignment Γ) :=
  (enumerateNullaryAssignments
    (orderedNullarySymbols Γ)).find?
    (fun χ =>
      decide (QFEntailment.AdomEmptyCounterexample E χ))

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Prepared Role-Neutral Bodies
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable [LinearOrder D]
variable [SolverKey A]
variable [SolverKey D]
variable {Γ : UnnamedSchema A}

/- One strict rendering tied to its exact Lean source. -/
structure PreparedBody
    (env : Vampire.TPTP.NameEnv A D)
    (source : SolverBodySource D Γ) where
  body : String
  rendered :
    Vampire.TPTP.sentenceWithEnv? env
        (source.toSentence.toFOLWithConstants
          source.toSentence.constants subset_rfl) =
      some body

namespace PreparedBody

/- Exact source constants as injective transport keys. -/
def exactConstantKeys
    {env : Vampire.TPTP.NameEnv A D}
    {source : SolverBodySource D Γ}
    (_prepared : PreparedBody env source) :
    List String :=
  source.toSentence.constants.sort.map SolverKey.key

end PreparedBody

/- Prepare one body, failing when the explicit environment is incomplete. -/
def prepareBody?
    (env : Vampire.TPTP.NameEnv A D)
    (source : SolverBodySource D Γ) :
    Option (PreparedBody env source) :=
  let sentence := source.toSentence
  match hBody : Vampire.TPTP.sentenceWithEnv? env
      (sentence.toFOLWithConstants sentence.constants subset_rfl) with
  | none => none
  | some body => some ⟨body, hBody⟩

/- Wire-level body data, with proof erased after preparation. -/
structure PreparedBodyData where
  sourceId : String
  sourceKind : String
  exactConstantKeys : List String
  body : String
  referencedRelations : List (String × String)
  referencedConstants : List (String × String)

/- Erase a checked body to its transport data. -/
def PreparedBody.toData
    [Vampire.SolverName A]
    [Vampire.SolverName D]
    {env : Vampire.TPTP.NameEnv A D}
    {source : SolverBodySource D Γ}
    (prepared : PreparedBody env source) :
    PreparedBodyData where
  sourceId := source.sourceId
  sourceKind := source.sourceKind
  exactConstantKeys := prepared.exactConstantKeys
  body := prepared.body
  referencedRelations :=
    let sentence := source.toSentence
    let fol := sentence.toFOLWithConstants
      sentence.constants subset_rfl
    (Vampire.TPTP.eraseDupsPreserve
      (Vampire.TPTP.formulaRelations fol.1)).map
        (fun relation =>
          (SolverKey.key relation, env.rel relation))
  referencedConstants :=
    source.toSentence.constants.sort.map
      (fun constant =>
        (SolverKey.key constant, env.funNameOf constant))

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Support Blocks
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable [LinearOrder A]
variable [LinearOrder D]
variable [SolverKey A]
variable [SolverKey D]

/- Strictly render adom and constant-distinctness support. -/
def supportBodies?
    (env : Vampire.TPTP.NameEnv A D)
    (Γ : UnnamedSchema A)
    (constants : Finset D) :
    Option (String × List String) := do
  let adom ← Vampire.TPTP.sentenceWithEnv? env
    (RelCalc.ToFOL.activeDomainSentence Γ constants)
  let distinct ←
    (RelCalc.ToFOL.constantDistinctSentences
      (Γ := Γ) constants).mapM
        (Vampire.TPTP.sentenceWithEnv? env)
  return (adom, distinct)

/- One complete checked support block. -/
structure PreparedSupportBlock
    (env : Vampire.TPTP.NameEnv A D)
    (Γ : UnnamedSchema A)
    (constants : Finset D) where
  adomBody : String
  distinctBodies : List String
  rendered :
    supportBodies? env Γ constants =
      some (adomBody, distinctBodies)

/- Prepare one complete support block or return none. -/
def prepareSupportBlock?
    (env : Vampire.TPTP.NameEnv A D)
    (Γ : UnnamedSchema A)
    (constants : Finset D) :
    Option (PreparedSupportBlock env Γ constants) :=
  match hBodies : supportBodies? env Γ constants with
  | none => none
  | some (adom, distinct) => some ⟨adom, distinct, hBodies⟩

/- Wire-level support-block data. -/
structure PreparedSupportData where
  constantKeys : List String
  adomBody : String
  distinctBodies : List String
  referencedRelations : List (String × String)
  referencedConstants : List (String × String)

/- Erase a checked support block to its transport data. -/
def PreparedSupportBlock.toData
    [Vampire.SolverName A]
    [Vampire.SolverName D]
    {env : Vampire.TPTP.NameEnv A D}
    {Γ : UnnamedSchema A}
    {constants : Finset D}
    (prepared : PreparedSupportBlock env Γ constants) :
    PreparedSupportData where
  constantKeys := constants.sort.map SolverKey.key
  adomBody := prepared.adomBody
  distinctBodies := prepared.distinctBodies
  referencedRelations :=
    Γ.syms.sort.map
      (fun relation =>
        (SolverKey.key relation, env.rel relation))
  referencedConstants :=
    constants.sort.map
      (fun constant =>
        (SolverKey.key constant, env.funNameOf constant))

end Runtime
end Synthesis
end Whiel
