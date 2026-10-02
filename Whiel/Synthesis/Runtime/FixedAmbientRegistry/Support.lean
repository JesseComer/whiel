-- Author: Jesse Comer
import Whiel.Synthesis.FrameworkII.FixedAmbient.CertificateEmitter
import Whiel.Synthesis.FrameworkII.FixedAmbient.Counterexample
import Whiel.Synthesis.FrameworkII.FixedAmbient.Worker
import Whiel.Synthesis.Runtime.Task

/-
  Shared typed registry support. `Entry.ofInput` derives
  every worker operation from the computed preprocessing
  result. Generated input modules import only this support
  and their own authoritative Input, avoiding cycles.
-/

------------------------------------------------------------
-- Registry Entries
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry

open Concrete

/- One typed row in a prophecy relation table. -/
structure RelationRow (Gamma : UnnamedSchema WhielNames) where
  relation : Gamma.syms

namespace RelationRow

variable {Gamma : UnnamedSchema WhielNames}

/- Opaque constructor-distinguishing relation key. -/
def key (row : RelationRow Gamma) : String :=
  SolverKey.key row.relation.1

/-
  Human-readable relation presentation, in the notation
  spelling, so a relation row reads as the same name the
  task text and the clause displays carry. The opaque
  solver key is `key` and is unaffected.
-/
def display (row : RelationRow Gamma) : String :=
  WhielNames.spell row.relation.1

/- Arity read from the computed prophecy schema. -/
def arity (row : RelationRow Gamma) : Nat :=
  Gamma.arity row.relation

/- Stable wire representation of one relation row. -/
def toJson (row : RelationRow Gamma) : Lean.Json :=
  Lean.Json.mkObj
    [ ("key", Lean.Json.str row.key),
      ("display", Lean.Json.str row.display),
      ("arity", Lean.Json.num row.arity) ]

end RelationRow

/- The complete relation table, in structural order. -/
def relationTableOf
    (Gamma : UnnamedSchema WhielNames) :
    List (RelationRow Gamma) :=
  Gamma.syms.attach.sort.map fun relation =>
    { relation := relation }

/- One prophecy relation table for wire publication. -/
def relationTableJsonOf
    (Gamma : UnnamedSchema WhielNames) : Lean.Json :=
  Lean.Json.arr
    ((relationTableOf Gamma).map RelationRow.toJson).toArray

private def prophecyBindingJson
    {Gamma : UnnamedSchema WhielNames}
    {body : Cmd Data Gamma}
    {task : FrameworkII.FixedAmbient.Task body}
    (binding : FrameworkII.FixedAmbient.Task.Binding task) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("program_key", Lean.Json.str
        (SolverKey.key binding.source.1)),
      ("prophecy_key", Lean.Json.str
        (SolverKey.key binding.prophecy.1)),
      ("arity", Lean.Json.num
        (Gamma.arity binding.source)) ]

/- Body-only prophecy correspondence for wire publication. -/
def prophecyBindingsJsonOf
    {Gamma : UnnamedSchema WhielNames}
    {body : Cmd Data Gamma}
    (task : FrameworkII.FixedAmbient.Task body) :
    Lean.Json :=
  Lean.Json.arr
    ((FrameworkII.FixedAmbient.Task.bindings task).map
      prophecyBindingJson).toArray

/- Complete task-bound identity of one same-schema scope. -/
def scopeIdentityOf
    (identity : TaskIdentity)
    {Gamma : UnnamedSchema WhielNames}
    {body : Cmd Data Gamma}
    (task : FrameworkII.FixedAmbient.Task body) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_framework_ii_fixed_ambient_task"),
      ("version", Lean.Json.num 2),
      ("semantic_version", Lean.Json.num
        identity.semanticVersion),
      ("encoding_version", Lean.Json.num
        identity.encodingVersion),
      ("task_canonical_id", Lean.Json.str
        identity.canonicalId),
      ("task_module", Lean.Json.str
        identity.moduleName),
      ("task_namespace", Lean.Json.str
        identity.namespaceName),
      ("task_source_sha256", Lean.Json.str
        identity.sourceSha256),
      ("ambient_scope",
        FrameworkII.FixedAmbient.Task.identityJson
          task SolverKey.key) ]

/-
  One directly callable registry entry. Every field is
  determined by the compiled input alone; nothing here is
  supplied by the host.
-/
structure Entry where
  prophecySchema : UnnamedSchema WhielNames
  identity : TaskIdentity
  manifest : BoundTaskManifest
  loop : Hoare.LoopTriple Data prophecySchema
  task : FrameworkII.FixedAmbient.Task loop.body
  scopeIdentity : Lean.Json
  rawInput : FrameworkII.FixedAmbient.RawInput
  relationTable : List (RelationRow prophecySchema)
  relationTableJson : Lean.Json
  prophecyBindings :
    List (FrameworkII.FixedAmbient.Task.Binding task)
  prophecyBindingsJson : Lean.Json
  /-
    Admission takes the run's optional host bound on clause
    text explicitly, so every call site states whether it is
    admitting host-bounded agent text or re-parsing Lean's
    own canonical source, which no host limit governs.
  -/
  admitClause : String ->
    FrameworkII.SurfaceParser.Limits ->
    Except FrameworkII.FixedAmbient.ClauseAdmissionFailure
      (FrameworkII.FixedAmbient.Clause prophecySchema)
  admitClauses : List String ->
    FrameworkII.SurfaceParser.Limits ->
    Except FrameworkII.FixedAmbient.ClauseAdmissionFailure
      (List (FrameworkII.FixedAmbient.Clause prophecySchema))
  admitClauseJson : List String ->
    Except FrameworkII.FixedAmbient.ClauseAdmissionFailure
      (List Lean.Json)
  taskComponents :
    List (FrameworkII.FixedAmbient.Component.Metadata
      prophecySchema)
  clauseComponents :
    FrameworkII.FixedAmbient.Clause prophecySchema ->
      List (FrameworkII.FixedAmbient.Component.Metadata
        prophecySchema)
  buildObligation :
    FrameworkII.FixedAmbient.Snapshot prophecySchema ->
      FrameworkII.FixedAmbient.ObligationSelector ->
        Except String
          (FrameworkII.FixedAmbient.BuiltObligation
            prophecySchema)
  buildAllObligations :
    FrameworkII.FixedAmbient.Snapshot prophecySchema ->
      List (FrameworkII.FixedAmbient.BuiltObligation
        prophecySchema)
  collapseCore :
    FrameworkII.FixedAmbient.Snapshot prophecySchema ->
      List (Nat × QFAssertExpr Data prophecySchema) ×
        QFAssertExpr Data prophecySchema
  prepareEntailment? :
    Vampire.TPTP.NameEnv WhielNames Data ->
      FrameworkII.FixedAmbient.BuiltObligation
        prophecySchema ->
        Option (FrameworkII.FixedAmbient.PreparedEntailment
          prophecySchema)
  prepareComponent? :
    Vampire.TPTP.NameEnv WhielNames Data ->
      FrameworkII.FixedAmbient.Component.Metadata
        prophecySchema ->
        Option (FrameworkII.FixedAmbient.PreparedComponent
          prophecySchema)
  checkEmptyCounterexample :
    QFEntailment (D := Data) prophecySchema ->
      Except String
        (FrameworkII.FixedAmbient.EmptyCheckResult
          prophecySchema)
  validateRefutation :
    (entailment : QFEntailment (D := Data) prophecySchema) ->
      Lean.Json ->
        Except String
          (FrameworkII.Refutation.Validation prophecySchema
            entailment.constants)
  preconditionRows :
    List (FrameworkII.FixedAmbient.PreconditionRow
      prophecySchema)
  confirmPreconditionRow :
    (snapshot :
      FrameworkII.FixedAmbient.Snapshot prophecySchema) ->
      FrameworkII.FixedAmbient.ObligationSelector -> Nat ->
        Except String
          (FrameworkII.FixedAmbient.PreconditionRowConfirmation
            loop snapshot)
  certificateBinding :
    FrameworkII.FixedAmbient.CertificateEmitter.InputBinding
  emitCertificate :
    FrameworkII.FixedAmbient.Snapshot prophecySchema ->
      Except String
        FrameworkII.FixedAmbient.CertificateEmitter.Bundle

/-
  Build the one registry entry of one compiled input. Every
  registered task is assembled by exactly this route, from
  its checked identity, its Lean-evaluated manifest, and its
  preprocessing result.
-/
def Entry.ofInput
    {Gamma : UnnamedSchema ProgramNames}
    {inputPre inputPost : AssertExpr Data Gamma}
    {inputCmd : Cmd Data Gamma}
    (identity : TaskIdentity)
    (manifest : BoundTaskManifest)
    (preproc : Hoare.Preproc inputPre inputCmd inputPost) :
    Entry :=
  let inputLoop :=
    FrameworkII.FixedAmbient.Preproc.loop preproc
  let loop := inputLoop.lift
  let task := inputLoop.task
  let scopeIdentity := scopeIdentityOf identity task
  let binding :=
    FrameworkII.FixedAmbient.CertificateEmitter.InputBinding.ofTaskIdentity
      identity
  { prophecySchema := inputLoop.prophecySchema
    identity := identity
    manifest := manifest
    loop := loop
    task := task
    scopeIdentity := scopeIdentity
    rawInput :=
      { schema := Gamma
        pre := inputPre
        cmd := inputCmd
        post := inputPost }
    relationTable := relationTableOf inputLoop.prophecySchema
    relationTableJson :=
      relationTableJsonOf inputLoop.prophecySchema
    prophecyBindings :=
      FrameworkII.FixedAmbient.Task.bindings task
    prophecyBindingsJson := prophecyBindingsJsonOf task
    admitClause := fun source limits =>
      FrameworkII.FixedAmbient.admitClause
        inputLoop.prophecySchema source limits
    admitClauses := fun sources limits =>
      FrameworkII.FixedAmbient.admitClauses
        inputLoop.prophecySchema sources limits
    admitClauseJson :=
      FrameworkII.FixedAmbient.admitClauseJson
        inputLoop.prophecySchema
    taskComponents :=
      FrameworkII.FixedAmbient.Component.taskComponents
        scopeIdentity loop task
    clauseComponents := fun clause =>
      FrameworkII.FixedAmbient.Component.clauseComponents
        scopeIdentity loop task clause
    buildObligation := fun snapshot selector =>
      FrameworkII.FixedAmbient.buildObligation loop task
        snapshot selector
    buildAllObligations := fun snapshot =>
      FrameworkII.FixedAmbient.buildAllObligations loop task
        snapshot
    collapseCore := fun snapshot =>
      FrameworkII.FixedAmbient.collapseCore loop task snapshot
    prepareEntailment? := fun env built =>
      FrameworkII.FixedAmbient.prepareEntailment? env built
    prepareComponent? := fun env metadata =>
      FrameworkII.FixedAmbient.prepareComponent? env metadata
    checkEmptyCounterexample := fun entailment =>
      FrameworkII.FixedAmbient.checkEmptyCounterexample
        entailment
    validateRefutation := fun entailment interpretation =>
      FrameworkII.FixedAmbient.validateRefutation
        entailment interpretation
    preconditionRows :=
      FrameworkII.FixedAmbient.preconditionRows loop
    confirmPreconditionRow := fun snapshot selector ordinal =>
      FrameworkII.FixedAmbient.confirmPreconditionRow
        loop snapshot selector ordinal
    certificateBinding := binding
    emitCertificate := fun snapshot =>
      FrameworkII.FixedAmbient.CertificateEmitter.emit
        preproc binding scopeIdentity snapshot }

namespace Entry

/- Validate one submitted counterexample for this input. -/
def validateCounterexample
    (e : Entry)
    (submitted : Lean.Json) :
    Except FrameworkII.CounterexampleRejection
      (FrameworkII.FixedAmbient.Counterexample.Record
        e.rawInput.schema) :=
  FrameworkII.FixedAmbient.Counterexample.validateRawInput
    e.rawInput submitted

/- Re-admit one frozen counterexample for this input. -/
def admitFrozenCounterexample
    (e : Entry)
    (fuel : Nat)
    (identity : String)
    (submitted : Lean.Json) :
    Except FrameworkII.CounterexampleRejection
      (FrameworkII.FixedAmbient.Counterexample.Record
        e.rawInput.schema) :=
  FrameworkII.FixedAmbient.Counterexample.admitFrozenRawInput
    e.rawInput fuel identity submitted

/- Emit the invalidity certificate of a frozen record. -/
def emitInvalidCertificate
    (e : Entry)
    (record :
      FrameworkII.FixedAmbient.Counterexample.Record
        e.rawInput.schema) :
    Except String
      FrameworkII.FixedAmbient.CertificateEmitter.Bundle :=
  FrameworkII.FixedAmbient.CertificateEmitter.emitInvalid
    e.rawInput.pre e.rawInput.cmd e.rawInput.post
    e.certificateBinding e.scopeIdentity record

end Entry

end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
