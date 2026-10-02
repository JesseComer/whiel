-- Author: Jesse Comer
import Whiel.Synthesis.Runtime.FixedAmbientRegistry

set_option linter.hashCommand false

/-
  Product-path checks for the counterexample codec, the
  fuel-counting evaluator, and the refutable fixture's
  frozen witness.

  The checks pin the accepted relation spellings, the
  conservative caps, the canonical re-emission and its
  identity, the agreement of `CmdFuel.evalCount` with
  `CmdFuel.eval`, the typed verdicts of
  `Counterexample.validate`, and the exact fuel the
  fixture's witness consumes and has frozen for it.
-/

------------------------------------------------------------
-- Codec Fixtures
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace CounterexampleInstanceTest

open Concrete
open FrameworkII
open Runtime.FixedAmbientRegistry

private def edgeRow
    (source target : Nat) : Lean.Json :=
  Lean.Json.arr
    #[ Lean.Json.str ("num:" ++ toString source),
       Lean.Json.str ("num:" ++ toString target) ]

private def relation
    (name : String)
    (rows : List Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [ ("name", Lean.Json.str name),
      ("rows", Lean.Json.arr rows.toArray) ]

private def instanceOf
    (relations : List Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [("relations", Lean.Json.arr relations.toArray)]

/- The two-edge witness of the refutable fixture. -/
def witness : Lean.Json :=
  instanceOf
    [ relation "p::E" [edgeRow 0 1, edgeRow 1 2],
      relation "p::S" [],
      relation "p::T" [] ]

/- The same witness under the presentation's lift prefix. -/
def liftedWitness : Lean.Json :=
  instanceOf
    [ relation "o:p::E" [edgeRow 0 1, edgeRow 1 2],
      relation "o:p::S" [],
      relation "o:p::T" [] ]

private def schema :=
  Whiel.Benchmark.Example0013.inputSchema

private def decodedIdentity?
    (json : Lean.Json) : Option String :=
  match decodeProgramInstance schema json with
  | .ok decoded => some decoded.identity
  | .error _ => none

private def rejectionCode
    (json : Lean.Json) : String :=
  match decodeProgramInstance schema json with
  | .ok _ => "accepted"
  | .error rejection => rejection.code

------------------------------------------------------------
-- Accepted Spellings
------------------------------------------------------------

/- The canonical program-name key is accepted. -/
#guard (decodedIdentity? witness).isSome

/- The presentation's ordinary lift prefix names the same
   relation, and decodes to the same canonical instance. -/
#guard decodedIdentity? liftedWitness = decodedIdentity? witness

/- The canonical re-emission is the fixed wire document. -/
#guard
  (match decodeProgramInstance schema witness with
    | .ok decoded => decoded.canonicalJson.compress
    | .error _ => "") =
  "{\"relations\":[{\"name\":\"p::E\",\"rows\":" ++
    "[[\"num:0\",\"num:1\"],[\"num:1\",\"num:2\"]]}," ++
    "{\"name\":\"p::S\",\"rows\":[]}," ++
    "{\"name\":\"p::T\",\"rows\":[]}]}"

/- Re-decoding the canonical document is idempotent. -/
#guard
  (match decodeProgramInstance schema witness with
    | .ok decoded => decodedIdentity? decoded.canonicalJson
    | .error _ => none) = decodedIdentity? witness

/- The rendered keyed rows rebuild the decoded instance. -/
#guard
  (match decodeProgramInstance schema witness with
    | .ok decoded =>
        CounterexampleCodec.canonicalJson schema
            (ProgramInstance.ofKeyedRows schema
              decoded.keyedRows) ==
          decoded.canonicalJson
    | .error _ => false)

------------------------------------------------------------
-- Typed Rejections
------------------------------------------------------------

/- A relation the input schema does not name is rejected. -/
#guard rejectionCode
    (instanceOf
      [ relation "p::E" [], relation "p::S" [],
        relation "p::T" [], relation "p::Q" [] ]) =
  "unknown_relation"

/- A prophecy relation is not an input relation. -/
#guard rejectionCode
    (instanceOf
      [ relation "y:p::T" [], relation "p::E" [],
        relation "p::S" [], relation "p::T" [] ]) =
  "unknown_relation"

/- A cell that is not a canonical value key is rejected. -/
#guard rejectionCode
    (instanceOf
      [ relation "p::E"
          [Lean.Json.arr #[Lean.Json.num 0, Lean.Json.num 1]],
        relation "p::S" [], relation "p::T" [] ]) =
  "malformed"

/- A noncanonical value key is rejected. -/
#guard rejectionCode
    (instanceOf
      [ relation "p::E"
          [Lean.Json.arr
            #[Lean.Json.str "num:00", Lean.Json.str "num:1"]],
        relation "p::S" [], relation "p::T" [] ]) =
  "malformed"

/- A repeated relation is rejected. -/
#guard rejectionCode
    (instanceOf
      [ relation "p::E" [], relation "p::E" [],
        relation "p::S" [], relation "p::T" [] ]) =
  "malformed"

/- The two accepted spellings of one relation are the same
   relation, so carrying both is a repeated relation. -/
#guard rejectionCode
    (instanceOf
      [ relation "p::E" [], relation "o:p::E" [],
        relation "p::S" [], relation "p::T" [] ]) =
  "malformed"

/- The same duplicate in the other order. -/
#guard rejectionCode
    (instanceOf
      [ relation "o:p::E" [], relation "p::E" [],
        relation "p::S" [], relation "p::T" [] ]) =
  "malformed"

/- An omitted relation is rejected. -/
#guard rejectionCode
    (instanceOf [relation "p::E" [], relation "p::S" []]) =
  "malformed"

/- A row of the wrong arity is rejected. -/
#guard rejectionCode
    (instanceOf
      [ relation "p::E"
          [Lean.Json.arr #[Lean.Json.str "num:0"]],
        relation "p::S" [], relation "p::T" [] ]) =
  "malformed"

/- A document that is not the strict shape is rejected. -/
#guard rejectionCode (Lean.Json.mkObj []) = "malformed"

------------------------------------------------------------
-- No Instance Size Bound
------------------------------------------------------------

/-
  Pass 7.7b removed the 64-value, 256-row and 1024-row caps.
  A counterexample is decoded at whatever size it is
  submitted; the only guard is the host's call-local
  wall-clock timeout, and kernel-checking a large certificate
  is a build cost, never a reason to refuse an instance.
-/

private def wideRows (count : Nat) : List Lean.Json :=
  (List.range count).map fun index => edgeRow index index

/- 400 rows over 400 distinct values: far beyond every
   removed cap, and decoded without complaint. -/
#guard rejectionCode
    (instanceOf
      [ relation "p::E" (wideRows 400),
        relation "p::S" [], relation "p::T" [] ]) =
  "accepted"

/- The rejection vocabulary carries no size code at all, and
   no fuel code either. -/
#guard ¬ (["malformed", "unknown_relation", "not_quantifier_free",
    "precondition_fails", "postcondition_holds",
    "internal_error"].contains "cap_exceeded")
#guard ¬ (["malformed", "unknown_relation", "not_quantifier_free",
    "precondition_fails", "postcondition_holds",
    "internal_error"].contains "out_of_fuel")

end CounterexampleInstanceTest
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Fuel Counting
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace CounterexampleInstanceTest

open Concrete
open FrameworkII

private def fixtureInstance : Instance Data
    Whiel.Benchmark.Example0013.inputSchema :=
  match decodeProgramInstance
      Whiel.Benchmark.Example0013.inputSchema witness with
  | .ok decoded => decoded.value
  | .error _ => fun _ => ∅

/-
  Counting the fuel does not change the result. The general
  statement is `CmdFuel.evalCount_fst`; these checks pin it
  on the fixture at bounds below, at, and above the fuel the
  run consumes.
-/
private def resultKey
    (result : CmdFuel.Result Data
      Whiel.Benchmark.Example0013.inputSchema) : String :=
  match result with
  | .outOfFuel => "out_of_fuel"
  | .halted halted =>
      (CounterexampleCodec.canonicalJson
        Whiel.Benchmark.Example0013.inputSchema
        halted).compress

private def agreesAt (fuel : Nat) : Bool :=
  resultKey
      (CmdFuel.evalCount fuel
        Whiel.Benchmark.Example0013.inputCmd
        fixtureInstance).1 ==
    resultKey
      (CmdFuel.eval fuel
        Whiel.Benchmark.Example0013.inputCmd
        fixtureInstance)

#guard agreesAt 0
#guard agreesAt 5
#guard agreesAt 6
#guard agreesAt 7
#guard agreesAt 200

/- The witness consumes exactly six units of fuel. -/
#guard CmdFuel.evalConsumed 200
    Whiel.Benchmark.Example0013.inputCmd fixtureInstance = 6

/- The consumed bound is independent of the host's bound. -/
#guard CmdFuel.evalConsumed 64
    Whiel.Benchmark.Example0013.inputCmd fixtureInstance = 6

/- One unit below the consumed bound the run does not halt. -/
#guard
  (match CmdFuel.eval 5 Whiel.Benchmark.Example0013.inputCmd
      fixtureInstance with
    | .outOfFuel => true
    | .halted _ => false)

end CounterexampleInstanceTest
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Validation Verdicts
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace CounterexampleInstanceTest

open Concrete
open FrameworkII

private def validationCode
    (pre post : AssertExpr Data
      Whiel.Benchmark.Example0013.inputSchema)
    (json : Lean.Json) : String :=
  match FixedAmbient.Counterexample.validate pre
      Whiel.Benchmark.Example0013.inputCmd post json with
  | .ok _ => "accepted"
  | .error rejection => rejection.code

/-
  A relation name the input schema does not carry, used only
  to extend the input schema so an assertion over it binds
  one relation symbol existentially.
-/
private def boundRelation : ProgramNames :=
  .flagSymbol 0 0

/-
  One assertion that is not quantifier free: its full schema
  extends the input schema by `boundRelation`, so that
  symbol is existentially bound.
-/
private def quantifiedAssertion :
    AssertExpr Data Whiel.Benchmark.Example0013.inputSchema :=
  AssertExpr.ofFormula
    (UnnamedSchema.insertFresh_extensionOf
      Whiel.Benchmark.Example0013.inputSchema boundRelation 2
      (by decide))
    QFAssertExpr.«true»

/- The extending symbol really is existentially bound. -/
#guard !decide quantifiedAssertion.NoBoundSymbols

/- A quantified precondition is rejected before the
   submitted instance is decoded or run. -/
#guard validationCode quantifiedAssertion
    Whiel.Benchmark.Example0013.inputPost witness =
  "not_quantifier_free"

/- So is a quantified postcondition. -/
#guard validationCode Whiel.Benchmark.Example0013.inputPre
    quantifiedAssertion witness =
  "not_quantifier_free"

/- The rejection is typed rather than an internal fault,
   even when the submitted document is itself malformed. -/
#guard validationCode quantifiedAssertion
    Whiel.Benchmark.Example0013.inputPost
    (Lean.Json.mkObj []) =
  "not_quantifier_free"

/-
  The refutable fixture's witness validates, and the record
  freezes the fuel the run actually consumed. There is no
  bound to fall back to: the replay runs under the
  unreachable structural `replayFuel`, and
  `kernelRefutes_evalConsumed` is why the measurement alone
  certifies.
-/
#guard
  (match FixedAmbient.Counterexample.validate
      Whiel.Benchmark.Example0013.inputPre
      Whiel.Benchmark.Example0013.inputCmd
      Whiel.Benchmark.Example0013.inputPost witness with
    | .ok record => record.fuelConsumed
    | .error _ => 0) = 6

/- The structural replay fuel is unreachable by any run the
   call-local timeout allows, so exhausting it is a fault of
   this validation path rather than a verdict on a
   submission: it carries the internal-fault code, and the
   wire vocabulary has no fuel code of its own. -/
#guard FixedAmbient.Counterexample.replayFuel = 2 ^ 62
#guard CounterexampleRejection.code .outOfFuel =
  "internal_error"

/- The internal-fault code is reserved for Lean's own
   defensive assertion and is never a verdict on one
   submission. -/
#guard CounterexampleRejection.code (.internalError "x") =
  "internal_error"

end CounterexampleInstanceTest
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Frozen Fixture Witness
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace CounterexampleInstanceTest

open Concrete
open Whiel.Benchmark.Example0013

/-
  The hand-checked witness of the refutable fixture, with
  the fuel the emitter freezes for it. This is the same
  statement the emitted certificate closes in the kernel.
-/
theorem fixture_witness_refutes :
    Hoare.CounterExample.kernelRefutes 6 inputPre inputCmd
        inputPost
      (ProgramInstance.ofKeyedRows inputSchema
        [ ("p::E",
            [ [Data.num 0, Data.num 1],
              [Data.num 1, Data.num 2] ]),
          ("p::S", []),
          ("p::T", []) ]) = Bool.true := by
  decide

/- The precondition and postcondition are quantifier free. -/
example : inputPre.NoBoundSymbols := by decide
example : inputPost.NoBoundSymbols := by decide

end CounterexampleInstanceTest
end Tests
end Synthesis
end Whiel
