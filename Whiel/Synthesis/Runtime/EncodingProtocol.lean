-- Author: Jesse Comer
import Lean

/-
  Versioned transport for persistent synthesis encoding
  workers.

  Each message is one UTF-8 JSON object framed by a four-byte
  big-endian payload length. The fixed limit is checked before
  payload allocation.
-/

------------------------------------------------------------
-- Protocol Envelopes
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace EncodingProtocol

/- Current bounded-frame protocol version. -/
def formatVersion : Nat := 13

/- Maximum UTF-8 JSON frame exchanged with the Rust encoding worker: 64 MiB. -/
def maxFrameBytes : Nat := 64 * 1024 * 1024

/- One source-key to TPTP-name assignment. -/
structure NameBinding where
  key : String
  name : String
deriving DecidableEq, Repr

namespace NameBinding

/- Parse one name binding. -/
def fromJson? (json : Lean.Json) : Except String NameBinding := do
  return {
    key := ← json.getObjValAs? String "key"
    name := ← json.getObjValAs? String "name" }

/- Serialize one name binding. -/
def toJson (binding : NameBinding) : Lean.Json :=
  Lean.Json.mkObj
    [ ("key", Lean.Json.str binding.key),
      ("name", Lean.Json.str binding.name) ]

end NameBinding

/- One worker request envelope. -/
structure Request where
  formatVersion : Nat
  semanticVersion : Nat
  encodingVersion : Nat
  taskCanonicalId : String
  taskModule : String
  taskNamespace : String
  taskSourceSha256 : String
  requestId : Nat
  contextId : String
  nameEnvRevision : Nat
  proposalRevision : Nat
  operation : String
  payload : Lean.Json

namespace Request

/- Parse the exact versioned request envelope. -/
def fromJson? (json : Lean.Json) : Except String Request := do
  return {
    formatVersion :=
      ← json.getObjValAs? Nat "format_version"
    semanticVersion :=
      ← json.getObjValAs? Nat "semantic_version"
    encodingVersion :=
      ← json.getObjValAs? Nat "encoding_version"
    taskCanonicalId :=
      ← json.getObjValAs? String "task_canonical_id"
    taskModule :=
      ← json.getObjValAs? String "task_module"
    taskNamespace :=
      ← json.getObjValAs? String "task_namespace"
    taskSourceSha256 :=
      ← json.getObjValAs? String "task_source_sha256"
    requestId :=
      ← json.getObjValAs? Nat "request_id"
    contextId :=
      ← json.getObjValAs? String "context_id"
    nameEnvRevision :=
      ← json.getObjValAs? Nat "name_env_revision"
    proposalRevision :=
      ← json.getObjValAs? Nat "proposal_revision"
    operation :=
      ← json.getObjValAs? String "operation"
    payload := json.getObjValD "payload" }

end Request

/- Worker identity fixed for the process lifetime. -/
structure WorkerIdentity where
  contextId : String
  semanticVersion : Nat
  encodingVersion : Nat
  taskCanonicalId : String
  taskModule : String
  taskNamespace : String
  taskSourceSha256 : String
deriving DecidableEq, Repr

/- Structured protocol or preparation failure. -/
structure ResponseError where
  kind : String
  message : String
deriving DecidableEq, Repr

/- One response envelope. -/
structure Response where
  semanticVersion : Nat
  encodingVersion : Nat
  taskCanonicalId : String
  taskModule : String
  taskNamespace : String
  taskSourceSha256 : String
  requestId : Nat
  contextId : String
  operation : String
  requestNameEnvRevision : Nat
  nameEnvRevision : Nat
  requestProposalRevision : Nat
  proposalRevision : Nat
  status : String
  payload : Lean.Json
  error? : Option ResponseError := none

namespace Response

/- Successful response tied to one request. -/
def ok
    (request : Request)
    (currentNameEnvRevision : Nat)
    (payload : Lean.Json)
    (currentProposalRevision : Nat :=
      request.proposalRevision) : Response where
  semanticVersion := request.semanticVersion
  encodingVersion := request.encodingVersion
  taskCanonicalId := request.taskCanonicalId
  taskModule := request.taskModule
  taskNamespace := request.taskNamespace
  taskSourceSha256 := request.taskSourceSha256
  requestId := request.requestId
  contextId := request.contextId
  operation := request.operation
  requestNameEnvRevision := request.nameEnvRevision
  nameEnvRevision := currentNameEnvRevision
  requestProposalRevision := request.proposalRevision
  proposalRevision := currentProposalRevision
  status := "ok"
  payload := payload

/- Failed response tied to one parsed request. -/
def error
    (request : Request)
    (currentNameEnvRevision : Nat)
    (kind message : String)
    (currentProposalRevision : Nat :=
      request.proposalRevision) : Response where
  semanticVersion := request.semanticVersion
  encodingVersion := request.encodingVersion
  taskCanonicalId := request.taskCanonicalId
  taskModule := request.taskModule
  taskNamespace := request.taskNamespace
  taskSourceSha256 := request.taskSourceSha256
  requestId := request.requestId
  contextId := request.contextId
  operation := request.operation
  requestNameEnvRevision := request.nameEnvRevision
  nameEnvRevision := currentNameEnvRevision
  requestProposalRevision := request.proposalRevision
  proposalRevision := currentProposalRevision
  status := "error"
  payload := Lean.Json.null
  error? := some { kind, message }

/- Response for a request whose envelope could not be parsed. -/
def malformed
    (identity : WorkerIdentity)
    (currentNameEnvRevision : Nat)
    (message : String)
    (currentProposalRevision : Nat := 0) : Response where
  semanticVersion := identity.semanticVersion
  encodingVersion := identity.encodingVersion
  taskCanonicalId := identity.taskCanonicalId
  taskModule := identity.taskModule
  taskNamespace := identity.taskNamespace
  taskSourceSha256 := identity.taskSourceSha256
  requestId := 0
  contextId := identity.contextId
  operation := ""
  requestNameEnvRevision := currentNameEnvRevision
  nameEnvRevision := currentNameEnvRevision
  requestProposalRevision := currentProposalRevision
  proposalRevision := currentProposalRevision
  status := "error"
  payload := Lean.Json.null
  error? := some { kind := "malformed_request", message }

/- Serialize one response envelope. -/
def toJson (response : Response) : Lean.Json :=
  let errorFields := match response.error? with
    | none => []
    | some err =>
        [("error", Lean.Json.mkObj
          [ ("kind", Lean.Json.str err.kind),
            ("message", Lean.Json.str err.message) ])]
  Lean.Json.mkObj
    ([ ("format_version", Lean.Json.num formatVersion),
       ("semantic_version", Lean.Json.num response.semanticVersion),
       ("encoding_version", Lean.Json.num response.encodingVersion),
       ("task_canonical_id", Lean.Json.str response.taskCanonicalId),
       ("task_module", Lean.Json.str response.taskModule),
       ("task_namespace", Lean.Json.str response.taskNamespace),
       ("task_source_sha256", Lean.Json.str response.taskSourceSha256),
       ("request_id", Lean.Json.num response.requestId),
       ("context_id", Lean.Json.str response.contextId),
       ("operation", Lean.Json.str response.operation),
       ("request_name_env_revision",
          Lean.Json.num response.requestNameEnvRevision),
       ("name_env_revision", Lean.Json.num response.nameEnvRevision),
       ("request_proposal_revision",
          Lean.Json.num response.requestProposalRevision),
       ("proposal_revision",
          Lean.Json.num response.proposalRevision),
       ("status", Lean.Json.str response.status),
       ("payload", response.payload) ] ++ errorFields)

end Response

end EncodingProtocol
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Bounded Length Framing
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace EncodingProtocol

/- Encode a payload length as four big-endian bytes. -/
def encodeLength (length : Nat) : ByteArray :=
  ByteArray.mk #[
    ((length / 16777216) % 256).toUInt8,
    ((length / 65536) % 256).toUInt8,
    ((length / 256) % 256).toUInt8,
    (length % 256).toUInt8]

/- Decode a four-byte big-endian payload length. -/
def decodeLength (header : ByteArray) : Option Nat :=
  if header.size = 4 then
    some
      ((header.get! 0).toNat * 16777216 +
       (header.get! 1).toNat * 65536 +
       (header.get! 2).toNat * 256 +
       (header.get! 3).toNat)
  else
    none

/- Read exactly `count` bytes, distinguishing clean EOF. -/
def readExact
    (stream : IO.FS.Stream)
    (count : Nat) :
    IO (Option ByteArray) := do
  let mut acc := ByteArray.empty
  while acc.size < count do
    let remaining := count - acc.size
    let chunk ← stream.read (USize.ofNat remaining)
    if chunk.isEmpty then
      if acc.isEmpty then
        return none
      else
        throw (IO.userError
          "truncated encoding-worker frame")
    acc := acc ++ chunk
  return some acc

/- Read one bounded payload. -/
def readFrame
    (stream : IO.FS.Stream) : IO (Option ByteArray) := do
  let some header ← readExact stream 4
    | return none
  let some length := decodeLength header
    | throw (IO.userError "invalid encoding-worker frame header")
  if length > maxFrameBytes then
    throw (IO.userError
      s!"encoding-worker frame exceeds {maxFrameBytes} bytes")
  readExact stream length

/- Write one bounded payload and flush after the complete frame. -/
def writeFrame
    (stream : IO.FS.Stream)
    (payload : ByteArray) : IO Unit := do
  if payload.size > maxFrameBytes then
    throw (IO.userError
      s!"encoding-worker response exceeds {maxFrameBytes} bytes")
  stream.write (encodeLength payload.size)
  stream.write payload
  stream.flush

/- Read and parse one JSON frame. -/
def readJsonFrame
    (stream : IO.FS.Stream) : IO (Option Lean.Json) := do
  let some payload ← readFrame stream
    | return none
  let some text := String.fromUTF8? payload
    | throw (IO.userError "encoding-worker frame is not UTF-8")
  match Lean.Json.parse text with
  | .ok json => return some json
  | .error message =>
      throw (IO.userError ("invalid encoding-worker JSON: " ++ message))

/- Serialize and write one JSON frame. -/
def writeJsonFrame
    (stream : IO.FS.Stream)
    (json : Lean.Json) : IO Unit :=
  writeFrame stream (Lean.Json.compress json).toUTF8

end EncodingProtocol
end Runtime
end Synthesis
end Whiel
