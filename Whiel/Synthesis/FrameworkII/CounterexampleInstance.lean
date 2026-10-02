-- Author: Jesse Comer
import Whiel.Eval.CounterExample.ProgramInstance
import Whiel.Synthesis.FrameworkII.InstanceAdmission
import Whiel.Synthesis.Runtime.CanonicalDigest

/-
  Lean-owned codec for one agent-proposed counterexample
  instance over a program-name input schema.

  This decoder is deliberately separate from the lifted
  schema decoder of `FrameworkII.Refutation`: a
  counterexample is an instance of the raw input schema over
  `ProgramNames` and it carries no carrier declaration. The
  instance has no size bound: the only guard on a
  counterexample submission is the call-local wall-clock
  timeout the host applies to the whole validation, and
  kernel-checking a large certificate is a build cost, never
  a reason to refuse an instance. The submitted document is
  opaque to the host; only Lean reads it.

  The accepted shape is the strict source-instance shape
  `{ "relations": [{ "name": <key>, "rows": [[<cell>, ...]] }] }`,
  where a relation name is the canonical `ProgramNames` key
  the agent sees for the input relation (the ordinary lift
  prefix `o:` of the presentation's relation table is
  accepted as the same name), and a cell is a canonical
  domain value key such as `num:3`.

  Key declarations include:
    * `Whiel.Synthesis.FrameworkII.CounterexampleRejection`
    * `Whiel.Synthesis.FrameworkII.DecodedCounterexample`
    * `Whiel.Synthesis.FrameworkII.decodeProgramInstance`
-/

------------------------------------------------------------
-- Typed Rejections
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII

/-
  One deterministic reason a submitted counterexample is not
  accepted. The first two arise in the codec; the next
  four arise when the decoded instance is run. The last is
  reserved for a defensive assertion inside Lean's own
  validation path: it reports no fault of the submission and
  can only fire if that path is itself inconsistent, so it
  fails the submission closed rather than accepting it.

  `outOfFuel` reports that same class. The replay's fuel is
  unreachable rather than a bound on the submission, so its
  exhaustion is a fault of this path and it carries the
  `internal_error` code; the wire vocabulary therefore has no
  separate fuel code.
-/
inductive CounterexampleRejection where
| malformed (detail : String)
| unknownRelation (detail : String)
| notQuantifierFree (detail : String)
| preconditionFails
| outOfFuel
| postconditionHolds
| internalError (detail : String)
deriving DecidableEq, Repr

namespace CounterexampleRejection

/- Stable machine-readable rejection class. -/
def code : CounterexampleRejection -> String
| .malformed _ => "malformed"
| .unknownRelation _ => "unknown_relation"
| .notQuantifierFree _ => "not_quantifier_free"
| .preconditionFails => "precondition_fails"
| .outOfFuel => "internal_error"
| .postconditionHolds => "postcondition_holds"
| .internalError _ => "internal_error"

/- Bounded explanation that never echoes submitted text. -/
def reason : CounterexampleRejection -> String
| .malformed detail => detail
| .unknownRelation detail => detail
| .notQuantifierFree detail => detail
| .internalError detail => detail
| .preconditionFails =>
    "the submitted instance does not satisfy the input " ++
      "precondition"
| .outOfFuel =>
    "the replay's structural fuel is unreachable, so " ++
      "exhausting it reports a fault of this validation " ++
      "path and never a fault of the submission"
| .postconditionHolds =>
    "the halted run satisfies the input postcondition, so " ++
      "the instance is not a counterexample"

/- Strict wire form of one rejection. -/
def toJson
    (rejection : CounterexampleRejection) : Lean.Json :=
  Lean.Json.mkObj
    [ ("status", Lean.Json.str "rejected"),
      ("code", Lean.Json.str rejection.code),
      ("reason", Lean.Json.str rejection.reason) ]

end CounterexampleRejection

end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Canonical Program-Name Instances
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace CounterexampleCodec

open Concrete
open Runtime

/- Order values of a solver-keyed carrier by their keys. -/
@[reducible] def keyOrder
    {alpha : Type}
    [SolverKey alpha] : LinearOrder alpha :=
  LinearOrder.lift' SolverKey.key SolverKey.key_injective

/- Canonical cell key of one domain value. -/
def cellJson (value : Data) : Lean.Json :=
  Lean.Json.str (SolverKey.key value)

/- Canonical row of one tuple, in coordinate order. -/
def rowJson
    {n : Nat}
    (tuple : Tuple Data n) : Lean.Json :=
  Lean.Json.arr (tuple.toList.map cellJson).toArray

/- Canonical rows of one relation, in tuple-key order. -/
def relationRows
    {Gamma : UnnamedSchema ProgramNames}
    (value : Instance Data Gamma)
    (symbol : Gamma.syms) : List (Tuple Data (Gamma.arity symbol)) :=
  letI : LinearOrder Data := keyOrder
  (value symbol).sort

/- Canonical relation record of one schema relation. -/
def relationJson
    {Gamma : UnnamedSchema ProgramNames}
    (value : Instance Data Gamma)
    (symbol : Gamma.syms) : Lean.Json :=
  Lean.Json.mkObj
    [ ("name", Lean.Json.str (SolverKey.key symbol.1)),
      ("rows", Lean.Json.arr
        ((relationRows value symbol).map rowJson).toArray) ]

/- Every schema relation, in canonical relation-key order. -/
def sortedSymbols
    (Gamma : UnnamedSchema ProgramNames) : List Gamma.syms :=
  letI : LinearOrder ProgramNames := keyOrder
  Gamma.syms.attach.sort

/-
  The canonical re-emission of one decoded instance. It is
  the exact document the emitter re-decodes, and the
  document whose digest is the instance identity.
-/
def canonicalJson
    (Gamma : UnnamedSchema ProgramNames)
    (value : Instance Data Gamma) : Lean.Json :=
  Lean.Json.mkObj
    [ ("relations", Lean.Json.arr
        ((sortedSymbols Gamma).map
          (relationJson value)).toArray) ]

/-
  The same instance as source-level keyed rows, for the
  certificate literal.
-/
def keyedRows
    (Gamma : UnnamedSchema ProgramNames)
    (value : Instance Data Gamma) :
    ProgramInstance.KeyedRows :=
  (sortedSymbols Gamma).map fun symbol =>
    (SolverKey.key symbol.1,
      (relationRows value symbol).map Vector.toList)

/- Digest of the canonical instance document. -/
def identity
    (Gamma : UnnamedSchema ProgramNames)
    (value : Instance Data Gamma) : String :=
  CanonicalDigest.jsonSha256 (canonicalJson Gamma value)

end CounterexampleCodec
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Strict Counterexample Decoding
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII

open Concrete
open Runtime
open CounterexampleCodec

/-
  One decoded counterexample instance with the canonical
  document Lean re-emits for it.
-/
structure DecodedCounterexample
    (Gamma : UnnamedSchema ProgramNames) where
  value : Instance Data Gamma
  canonicalJson : Lean.Json
  keyedRows : ProgramInstance.KeyedRows
  identity : String

namespace CounterexampleCodec

/-
  Resolve one submitted relation name. The canonical
  `ProgramNames` key is the contract spelling; the ordinary
  lift prefix `o:`, which is how the presentation's relation
  table spells the same input relation, resolves to the same
  name. No `ProgramNames` key begins with `o:`, so the two
  spellings cannot collide.
-/
def resolveRelation (name : String) : Option ProgramNames :=
  let stripped :=
    if name.startsWith "o:" then
      String.ofList (name.toList.drop 2)
    else
      name
  ProgramNames.parse? stripped

/- Decode one cell from its canonical domain-value key. -/
def decodeCell (json : Lean.Json) : Except String Data := do
  let key <- match json with
    | .str key => .ok key
    | _ => .error "counterexample cell must be a string"
  let some value := SolverKey.dataOfKey? key
    | throw "counterexample cell is not a domain value key"
  if SolverKey.key value != key then
    throw "counterexample cell key is not canonical"
  return value

/- Map one admission failure onto its wire rejection. -/
def ofAdmissionError
    (error : InstanceAdmissionError) :
    CounterexampleRejection :=
  match error with
  | .unknownRelation _ =>
      .unknownRelation
        (error.message ++ " at " ++ error.path)
  | _ =>
      .malformed (error.message ++ " at " ++ error.path)

end CounterexampleCodec

/-
  Decode one complete counterexample instance over the exact
  input schema.
-/
def decodeProgramInstance
    (Gamma : UnnamedSchema ProgramNames)
    (json : Lean.Json) :
    Except CounterexampleRejection
      (DecodedCounterexample Gamma) := do
  let admitted <- match admitSourceInstance Gamma
      CounterexampleCodec.resolveRelation
      CounterexampleCodec.decodeCell json with
    | .ok admitted => .ok admitted
    | .error error =>
        .error (CounterexampleCodec.ofAdmissionError error)
  let canonical :=
    CounterexampleCodec.canonicalJson Gamma admitted.value
  return {
    value := admitted.value
    canonicalJson := canonical
    keyedRows :=
      CounterexampleCodec.keyedRows Gamma admitted.value
    identity := CanonicalDigest.jsonSha256 canonical
  }

end FrameworkII
end Synthesis
end Whiel
