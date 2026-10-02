-- Author: Jesse Comer
import Whiel.Eval.Cmd.FuelCount
import Whiel.Eval.CounterExample.Kernel
import Whiel.Synthesis.FrameworkII.CounterexampleInstance

/-
  Lean-owned validation of one agent-proposed counterexample
  against a raw program-name input triple.

  The host never parses the submitted instance. Lean decodes
  it with the counterexample codec, checks the input
  precondition, runs the raw input command with the fuelled
  reference evaluator under an unreachable structural fuel
  value (`replayFuel`: there is no host fuel bound, and the
  call-local wall-clock timeout is the only guard), and
  checks that the run halts in a state violating the input
  postcondition. The fuel actually consumed is measured by
  `CmdFuel.evalCount` and frozen in place of that structural
  value; `Hoare.CounterExample.kernelRefutes_evalConsumed`
  proves that the smaller measured bound certifies whenever
  the larger one does, so no bound is ever substituted for
  the measurement.

  Key declarations include:
    * `Whiel.Synthesis.FrameworkII.FixedAmbient.RawInput`
    * `Whiel.Synthesis.FrameworkII.FixedAmbient.Counterexample.Record`
    * `Whiel.Synthesis.FrameworkII.FixedAmbient.Counterexample.validate`
-/

------------------------------------------------------------
-- Raw Input Bindings
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient

open Concrete
open Runtime

/-
  The raw program-name input triple of one registered task,
  with nothing derived from it. The counterexample path
  consumes exactly this: no snapshot, no catalog, no
  prophecy schema, and no lifted loop.
-/
structure RawInput where
  schema : UnnamedSchema ProgramNames
  pre : AssertExpr Data schema
  cmd : Cmd Data schema
  post : AssertExpr Data schema

end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Validated Counterexample Records
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace Counterexample

open Concrete
open Runtime

/-
  One validated counterexample. The instance is typed by the
  exact input schema, the fuel is the measured consumption
  that certifies it, and the canonical document is the only
  form in which the instance leaves Lean. There is no bound
  to record beside the measurement: the replay has none.
-/
structure Record
    (Gamma : UnnamedSchema ProgramNames) where
  value : Instance Data Gamma
  fuelConsumed : Nat
  canonicalJson : Lean.Json
  keyedRows : ProgramInstance.KeyedRows
  identity : String

/-
  Structural fuel the replay runs under. It is not a host
  bound and not a resource limit: the counterexample path has
  no fuel bound, and the only guard on the replay is the
  host's call-local wall-clock timeout, whose expiry is
  reported as a `timeout` rejection of the call and never as
  a verdict on the instance. `evalCount` needs a `Nat`, so
  the replay passes a value no run can reach before that
  timeout fires (over 4 x 10^18 evaluation steps), which
  keeps it inside Lean's unboxed `Nat` range. `.outOfFuel` is
  therefore unreachable by construction here and survives
  only because `evalCount` is total.
-/
def replayFuel : Nat := 2 ^ 62

/-
  Validate one submitted instance against a raw input
  triple. Every rejection is typed and carries no submitted
  text. The replay runs under `replayFuel`, which is not a
  bound the caller chooses; the record keeps the fuel the run
  actually consumed.
-/
def validate
    {Gamma : UnnamedSchema ProgramNames}
    (pre : AssertExpr Data Gamma)
    (cmd : Cmd Data Gamma)
    (post : AssertExpr Data Gamma)
    (json : Lean.Json) :
    Except CounterexampleRejection (Record Gamma) := do
  if hPre : pre.NoBoundSymbols then
    if hPost : post.NoBoundSymbols then
      let decoded <- decodeProgramInstance Gamma json
      unless decide ((pre.toQF hPre).eval decoded.value) do
        throw .preconditionFails
      match CmdFuel.evalCount replayFuel cmd
          decoded.value with
      | (.outOfFuel, _) =>
          throw .outOfFuel
      | (.halted halted, remaining) =>
          if decide ((post.toQF hPost).eval halted) then
            throw .postconditionHolds
          else
            let consumed := replayFuel - remaining
            /-
              `Hoare.CounterExample.kernelRefutes_evalConsumed`
              proves that the measured consumption refutes
              whenever the larger structural fuel does, so
              this check cannot fail. It is kept as a defensive
              assertion and fails closed on its own code:
              nothing about the submission is at fault when
              it fires.
            -/
            unless Hoare.CounterExample.kernelRefutes consumed
                pre cmd post decoded.value do
              throw (.internalError
                ("the fuel measured for the halting run does " ++
                  "not certify the refutation"))
            return {
              value := decoded.value
              fuelConsumed := consumed
              canonicalJson := decoded.canonicalJson
              keyedRows := decoded.keyedRows
              identity := decoded.identity
            }
    else
      throw (.notQuantifierFree
        "the input postcondition is not quantifier free")
  else
    throw (.notQuantifierFree
      "the input precondition is not quantifier free")

/- Strict wire form of one accepted counterexample. -/
def Record.toJson
    {Gamma : UnnamedSchema ProgramNames}
    (record : Record Gamma) : Lean.Json :=
  Lean.Json.mkObj
    [ ("status", Lean.Json.str "counterexample"),
      ("fuel_consumed", Lean.Json.num record.fuelConsumed),
      ("instance_identity", Lean.Json.str record.identity),
      ("instance", record.canonicalJson) ]

/- Validate one submission against a registered raw input. -/
def validateRawInput
    (raw : RawInput)
    (json : Lean.Json) :
    Except CounterexampleRejection (Record raw.schema) :=
  validate raw.pre raw.cmd raw.post json

/-
  Re-admit one already frozen counterexample. The instance
  is decoded again from its canonical document, its identity
  must be the frozen one, and the frozen fuel must still
  refute the input triple; nothing is recomputed or
  minimized here.
-/
def admitFrozen
    {Gamma : UnnamedSchema ProgramNames}
    (pre : AssertExpr Data Gamma)
    (cmd : Cmd Data Gamma)
    (post : AssertExpr Data Gamma)
    (fuel : Nat)
    (identity : String)
    (json : Lean.Json) :
    Except CounterexampleRejection (Record Gamma) := do
  let decoded <- decodeProgramInstance Gamma json
  unless decoded.identity == identity do
    throw (.malformed
      ("the submitted instance does not have the frozen " ++
        "instance identity"))
  unless Hoare.CounterExample.kernelRefutes fuel pre cmd
      post decoded.value do
    throw (.malformed
      ("the frozen instance and fuel do not refute the " ++
        "input triple"))
  return {
    value := decoded.value
    fuelConsumed := fuel
    canonicalJson := decoded.canonicalJson
    keyedRows := decoded.keyedRows
    identity := decoded.identity
  }

/- Re-admit one frozen record against a registered input. -/
def admitFrozenRawInput
    (raw : RawInput)
    (fuel : Nat)
    (identity : String)
    (json : Lean.Json) :
    Except CounterexampleRejection (Record raw.schema) :=
  admitFrozen raw.pre raw.cmd raw.post fuel identity json

end Counterexample
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel
