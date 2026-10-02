-- Author: Jesse Comer
import Databases.RelCalc.EmptyDomain
import Whiel.Synthesis.FrameworkII.FixedAmbient.CertificateJobs
import Whiel.Synthesis.FrameworkII.FixedAmbient.Counterexample
import Whiel.Synthesis.FrameworkII.FixedAmbient.ClauseNotation
import Whiel.Synthesis.FrameworkII.FixedAmbient.Worker
import Whiel.Synthesis.Runtime.CanonicalDigest
import Whiel.Synthesis.Runtime.Task

/-
  Deterministic, in-memory source emission for durable
  fixed-ambient Framework-II certificates.

  This module performs no filesystem writes and launches no
  process. Lean owns every emitted formula, job, and proof
  boundary; a coordinator only stages the returned artifacts,
  runs the pinned leancheck Vampire on the opaque problems,
  packages each raw proof with `packageProof`, and builds the
  result.

  The emitted tree has the shape of
  `Benchmark/Example0001/Certificate`: `Proposal.lean` prints
  each clause through `ClauseNotation`; the side-car
  `ProposalBinding.lean` binds every printed clause to its
  canonical source with `#guard` and sits on no proof import
  chain; `Jobs.lean` declares the level list, the exact
  `2N+1` jobs over it, and each job's `ShallowTarget`; each
  `EmptyCexCheck` leaf replays its own CNF/LRAT resources
  to prove the unchanged empty-domain obligation; every
  `Reconstructions` module closes its target with
  `certify_job`, which evaluates the supports and the symbol
  environment inside the elaborated term instead of the
  source; and `Valid.lean` folds the clause proofs into the
  input triple and prints its axioms. Every emitted module
  opens with one wrapped header comment in the style of the
  library modules.
-/

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace CertificateEmitter

open Concrete
open Runtime

------------------------------------------------------------
-- Input And Artifact Boundaries
------------------------------------------------------------

/- Exact compiled Input module selected for certification. -/
structure InputBinding where
  canonicalId : String
  moduleName : String
  namespaceName : String
  sourceSha256 : String
  semanticVersion : Nat
  encodingVersion : Nat
deriving DecidableEq, Repr

/-
  Declarations every certifiable Input module must provide
  under its namespace: the program-name input schema, the
  raw triple, and its preprocessing result. The
  prophecy schema, lifted loop, and task are computed from
  these; certification consumes the five by name and never
  authors or regenerates the Input.
-/
structure InputNames where
  schema : String := "inputSchema"
  pre : String := "inputPre"
  cmd : String := "inputCmd"
  post : String := "inputPost"
  preproc : String := "inputPreproc"
deriving DecidableEq, Repr

/- The one input naming contract accepted by the emitter. -/
def inputNames : InputNames := {}

/- One deterministic artifact, relative to a private root. -/
structure Artifact where
  relativePath : String
  contents : String
deriving DecidableEq, Repr

/- One job's exact empty-domain evidence and module. -/
structure EmptyCheck where
  cnfRelativePath : String
  cnfSha256 : String
  lratRelativePath : String
  moduleRelativePath : String
  moduleName : String
  theoremName : String
  cnf : String

/-
  Operational handoff for one opaque solver problem. These
  fields bind the coordinator's process work to the exact
  Lean job without serializing Lean semantics.
-/
structure ProofJob where
  id : String
  role : String
  ordinal : Nat
  clauseId : Option Nat
  level : Option Nat
  selectorIdentity : Lean.Json
  jobIdentity : Lean.Json
  jobDigest : String
  problemRelativePath : String
  problemSha256 : String
  leancheckOutputRelativePath : String
  proofModuleRelativePath : String
  proofModule : String
  proofNamespace : String
  proofTheorem : String
  reconstructionModule : String
  emptyCheck : EmptyCheck
  tptp : String

/- Atomic in-memory result accepted by the coordinator. -/
structure Bundle where
  inputIdentity : Lean.Json
  scopeIdentity : Lean.Json
  snapshotIdentity : Lean.Json
  inputSourceSha256 : String
  coreSize : Nat
  certificateModule : String
  certificateTheorem : String
  artifacts : List Artifact
  jobs : List ProofJob

private def optionNatJson : Option Nat -> Lean.Json
| none => Lean.Json.null
| some value => Lean.Json.num value

namespace Artifact

/- Strict wire form of one staged artifact. -/
def toJson (artifact : Artifact) : Lean.Json :=
  Lean.Json.mkObj
    [ ("relative_path", Lean.Json.str artifact.relativePath),
      ("contents_sha256", Lean.Json.str
        (CanonicalDigest.sha256 artifact.contents)),
      ("contents", Lean.Json.str artifact.contents) ]

end Artifact

namespace EmptyCheck

/- CNF bytes are staged separately, never in this token. -/
def toJson (check : EmptyCheck) : Lean.Json :=
  Lean.Json.mkObj
    [ ("encoding_version", Lean.Json.num 1),
      ("cnf_relative_path",
        Lean.Json.str check.cnfRelativePath),
      ("cnf_sha256", Lean.Json.str check.cnfSha256),
      ("lrat_relative_path",
        Lean.Json.str check.lratRelativePath),
      ("module_relative_path",
        Lean.Json.str check.moduleRelativePath),
      ("module", Lean.Json.str check.moduleName),
      ("theorem", Lean.Json.str check.theoremName) ]

end EmptyCheck

namespace ProofJob

/- Strict operational wire form; semantics stay in Lean. -/
def toJson (job : ProofJob) : Lean.Json :=
  Lean.Json.mkObj
    [ ("id", Lean.Json.str job.id),
      ("role", Lean.Json.str job.role),
      ("ordinal", Lean.Json.num job.ordinal),
      ("clause_id", optionNatJson job.clauseId),
      ("level", optionNatJson job.level),
      ("selector_identity", job.selectorIdentity),
      ("job_identity", job.jobIdentity),
      ("job_digest", Lean.Json.str job.jobDigest),
      ("problem_relative_path",
        Lean.Json.str job.problemRelativePath),
      ("problem_sha256", Lean.Json.str job.problemSha256),
      ("leancheck_output_relative_path",
        Lean.Json.str job.leancheckOutputRelativePath),
      ("proof_module_relative_path",
        Lean.Json.str job.proofModuleRelativePath),
      ("proof_module", Lean.Json.str job.proofModule),
      ("proof_namespace", Lean.Json.str job.proofNamespace),
      ("proof_theorem", Lean.Json.str job.proofTheorem),
      ("reconstruction_module",
        Lean.Json.str job.reconstructionModule),
      ("empty_check", job.emptyCheck.toJson) ]

end ProofJob

namespace Bundle

/- Complete deterministic handoff to the coordinator. -/
def toJson (bundle : Bundle) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_fixed_ambient_certificate_bundle"),
      ("version", Lean.Json.num 2),
      ("input_identity", bundle.inputIdentity),
      ("scope_identity", bundle.scopeIdentity),
      ("snapshot_identity", bundle.snapshotIdentity),
      ("input_source_sha256",
        Lean.Json.str bundle.inputSourceSha256),
      ("core_size", Lean.Json.num bundle.coreSize),
      ("certificate_module",
        Lean.Json.str bundle.certificateModule),
      ("certificate_theorem",
        Lean.Json.str bundle.certificateTheorem),
      ("artifacts", Lean.Json.arr
        (bundle.artifacts.map Artifact.toJson).toArray),
      ("jobs", Lean.Json.arr
        (bundle.jobs.map ProofJob.toJson).toArray) ]

end Bundle

private def isAsciiLetter (char : Char) : Bool :=
  ('a' <= char && char <= 'z') ||
    ('A' <= char && char <= 'Z')

private def isAsciiDigit (char : Char) : Bool :=
  '0' <= char && char <= '9'

private def validIdentifierSegment (segment : String) : Bool :=
  match segment.toList with
  | [] => false
  | head :: tail =>
      (isAsciiLetter head || head == '_') &&
        tail.all fun char =>
          isAsciiLetter char || isAsciiDigit char ||
            char == '_'

private def validDottedIdentifier (value : String) : Bool :=
  let segments := value.splitOn "."
  !segments.isEmpty && segments.all validIdentifierSegment

private def isLowerHexChar (char : Char) : Bool :=
  ('0' <= char && char <= '9') ||
    ('a' <= char && char <= 'f')

/- Validate the closed benchmark Input naming contract. -/
def InputBinding.validate
    (binding : InputBinding) : Except String Unit := do
  unless validIdentifierSegment binding.canonicalId do
    throw "certificate canonical_id is not a safe Lean identifier"
  unless validDottedIdentifier binding.moduleName do
    throw "certificate input module is not a safe Lean module name"
  unless validDottedIdentifier binding.namespaceName do
    throw "certificate input namespace is not a safe Lean namespace"
  unless binding.moduleName ==
      "Benchmark." ++ binding.canonicalId ++ ".Input" do
    throw "certificate input module disagrees with canonical_id"
  unless binding.namespaceName ==
      "Whiel.Benchmark." ++ binding.canonicalId do
    throw "certificate input namespace disagrees with canonical_id"
  unless binding.sourceSha256.length == 64 &&
      binding.sourceSha256.toList.all isLowerHexChar do
    throw "certificate Input hash is not a lowercase SHA-256 digest"
  unless binding.semanticVersion > 0 do
    throw "certificate semantic version must be positive"
  unless binding.encodingVersion > 0 do
    throw "certificate encoding version must be positive"

/- Module prefix of the emitted certificate tree. -/
def InputBinding.certificateModule
    (binding : InputBinding) : String :=
  "Benchmark." ++ binding.canonicalId ++ ".Certificate"

/- Namespace of the emitted certificate tree. -/
def InputBinding.certificateNamespace
    (binding : InputBinding) : String :=
  binding.namespaceName ++ ".Certificate"

/- Complete operational identity of the immutable Input. -/
def InputBinding.identityJson
    (binding : InputBinding) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_fixed_ambient_certificate_input"),
      ("version", Lean.Json.num 1),
      ("canonical_id", Lean.Json.str binding.canonicalId),
      ("module", Lean.Json.str binding.moduleName),
      ("namespace", Lean.Json.str binding.namespaceName),
      ("source_sha256", Lean.Json.str binding.sourceSha256),
      ("semantic_version",
        Lean.Json.num binding.semanticVersion),
      ("encoding_version",
        Lean.Json.num binding.encodingVersion) ]

/- Build the certificate binding from a compiled identity. -/
def InputBinding.ofTaskIdentity
    (identity : TaskIdentity) : InputBinding :=
  { canonicalId := identity.canonicalId
    moduleName := identity.moduleName
    namespaceName := identity.namespaceName
    sourceSha256 := identity.sourceSha256
    semanticVersion := identity.semanticVersion
    encodingVersion := identity.encodingVersion }

end CertificateEmitter
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Source Rendering
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace CertificateEmitter

open Concrete
open Runtime

private def generatedHeader : String :=
  "-- Generated by the Lean-owned fixed-ambient " ++
    "certificate-emitter-v2.\n-- Do not edit by hand.\n"

private def frameworkOpens : List String :=
  ["Whiel", "Whiel.Concrete",
    "Whiel.Synthesis.FrameworkII.FixedAmbient"]

private def proposalOpens : List String :=
  ["Whiel", "Whiel.Concrete",
    "Whiel.Synthesis.FrameworkII.FixedAmbient"]

/-
  Emitter-owned names of the computed objects every
  certificate module shares: the preprocessed input loop
  over the input schema and its computed prophecy schema.
-/
private def certifiedLoopName : String :=
  "certifiedLoop"

private def prophecySchemaName : String :=
  "prophecySchema"

/- Content width of one wrapped header line. -/
private def commentWidth : Nat := 58

/- Greedy word wrap of one comment within the bar width. -/
private def wrapComment (text : String) : List String :=
  let words := (text.splitOn " ").filter fun word =>
    !word.isEmpty
  let step := fun (acc : List String × String) (word : String) =>
    if acc.2.isEmpty then (acc.1, word)
    else if acc.2.length + 1 + word.length <= commentWidth then
      (acc.1, acc.2 ++ " " ++ word)
    else (acc.1 ++ [acc.2], word)
  let (lines, last) := words.foldl step ([], "")
  if last.isEmpty then lines else lines ++ [last]

/- The one `/- ... -/` header block of an emitted module. -/
private def headerLines (text : String) : List String :=
  "/-" :: (wrapComment text).map (fun line => "  " ++ line) ++
    ["-/"]

private def renderHeader (text : String) : String :=
  String.intercalate "\n" (headerLines text) ++ "\n"

/-
  The `#guard_msgs` expectation of one certificate theorem's
  axiom print, wrapped to the same width as every other
  emitted comment. The guard runs with
  `whitespace := lax`, which collapses the wrapping, so the
  message it accepts is unchanged. A fully qualified theorem
  name is one unbreakable word and may still overrun the
  width on its own line.
-/
private def axiomGuardComment
    (namespaceName : String)
    (theoremName : String) : String :=
  let text :=
    "info: '" ++ namespaceName ++ "." ++ theoremName ++
      "' depends on axioms: [propext, Classical.choice, " ++
      "Quot.sound]"
  String.intercalate "\n"
    ("/--" :: (wrapComment text).map
      (fun line => "  " ++ line) ++ ["-/"]) ++ "\n"

private def sourcePreamble
    (imports : List String)
    (header : String)
    (namespaceName : String)
    (opens : List String := frameworkOpens)
    (options : List String := []) : String :=
  generatedHeader ++
    String.intercalate "\n"
      (imports.map fun name => "import " ++ name) ++
    "\n\nset_option linter.style.setOption false\n" ++
    "set_option linter.style.longLine false\n" ++
    String.join
      (options.map fun option =>
        "set_option " ++ option ++ "\n") ++
    "set_option maxHeartbeats 400000000\n" ++
    "set_option maxRecDepth 1048576\n\n" ++
    renderHeader header ++
    "\nnamespace " ++ namespaceName ++ "\n\n" ++
    String.intercalate "\n"
      (opens.map fun name => "open " ++ name) ++ "\n\n"

private def sourcePostamble
    (namespaceName : String) : String :=
  "\nend " ++ namespaceName ++ "\n"

private def clauseName (ordinal : Nat) : String :=
  "candidateClause" ++ toString ordinal

private def renderList
    (indent : String)
    (items : List String) : String :=
  match items with
  | [] => "[]"
  | _ =>
      "[\n" ++ indent ++
        String.intercalate (",\n" ++ indent) items ++
        "\n  ]"

/- One printed clause declaration. -/
private def renderCandidateClause
    {Gamma : UnnamedSchema WhielNames}
    (ordinal : Nat)
    (row : CatalogRow Gamma) : Except String String := do
  match
      ClauseNotation.renderProposalDeclaration
        (clauseName ordinal) prophecySchemaName
        row.clause.formula with
  | .ok declaration => pure declaration
  | .error message =>
      throw ("clause " ++ toString row.clauseId ++
        " has no notation spelling: " ++ message)

/-
  The build-time guard binding one printed clause back to the
  catalog's canonical source, so a printer defect fails the
  benchmark build instead of certifying another Core.
-/
private def renderClauseBinding
    {Gamma : UnnamedSchema WhielNames}
    (ordinal : Nat)
    (row : CatalogRow Gamma) : String :=
  "#guard SurfaceSyntax.source " ++ clauseName ordinal ++
    " ==\n  " ++ reprStr row.clause.canonicalSource

/-
  The computed loop and prophecy schema, declared once in
  the proposal so every clause is typed by the same schema
  the jobs use. The loop lives over the preprocessor's own
  output schema --- the input schema extended by the flags
  the transformation drew --- and not over the input schema
  itself.
-/
private def renderComputedSchema : String :=
  let names := inputNames
  "abbrev " ++ certifiedLoopName ++ " :\n" ++
    "    Hoare.LoopTriple Data " ++ names.preproc ++
      ".outSchema :=\n" ++
    "  Preproc.loop " ++ names.preproc ++ "\n\n" ++
    "abbrev " ++ prophecySchemaName ++ " :\n" ++
    "    UnnamedSchema WhielNames :=\n" ++
    "  " ++ certifiedLoopName ++ ".prophecySchema"

private def proposalSource
    {Gamma : UnnamedSchema WhielNames}
    (binding : InputBinding)
    (snapshot : Snapshot Gamma) : Except String String := do
  let namespaceName := binding.certificateNamespace
  let rendered <- snapshot.rows.zipIdx.mapM fun pair =>
    renderCandidateClause pair.2 pair.1
  let declarations := String.intercalate "\n\n" rendered
  let clauseNames := snapshot.rows.zipIdx.map fun pair =>
    clauseName pair.2
  pure (sourcePreamble
      [binding.moduleName,
        "Whiel.Concrete.Notation",
        "Whiel.Synthesis.FrameworkII.FixedAmbient." ++
          "CertificateJobs"]
      ("The candidate clauses over the computed prophecy " ++
        "schema.")
      namespaceName proposalOpens ++
    renderComputedSchema ++ "\n\n" ++
    declarations ++
    (if declarations.isEmpty then "" else "\n\n") ++
    "def candidateClauses :\n" ++
    "    List (QFAssertExpr Data " ++ prophecySchemaName ++
      ") :=\n  " ++ renderList "    " clauseNames ++ "\n" ++
    sourcePostamble namespaceName)

/-
  The retained printer-binding side-car. It imports only the
  proposal and is imported by nothing on the certificate's
  proof chain; the benchmark aggregate elaborates it.
-/
private def proposalBindingSource
    {Gamma : UnnamedSchema WhielNames}
    (binding : InputBinding)
    (snapshot : Snapshot Gamma) : String :=
  let namespaceName := binding.certificateNamespace
  let bindings := snapshot.rows.zipIdx.map fun pair =>
    renderClauseBinding pair.2 pair.1
  sourcePreamble
      [binding.certificateModule ++ ".Proposal",
        "Whiel.Synthesis.FrameworkII.FixedAmbient." ++
          "SurfaceSyntax"]
      ("A build-time sanity check that the clause notation " ++
        "parses to the proposed clauses. It does not feed " ++
        "into the final certificate proof.")
      namespaceName proposalOpens
      ["linter.hashCommand false"] ++
    String.intercalate "\n\n" bindings ++
    (if bindings.isEmpty then "" else "\n") ++
    sourcePostamble namespaceName

------------------------------------------------------------
-- Exact Job Rendering
------------------------------------------------------------

private inductive RenderRole
| initialization (rowOrdinal : Nat)
| maintenance (rowOrdinal : Nat)
| termination

private structure RenderSpec where
  id : String
  role : RenderRole
  selector : ObligationSelector
  ordinal : Nat
  clauseId : Option Nat
  level : Option Nat
  jobName : String
  statementName : String
  emptyName : String
  shallowName : String
  validName : String
  moduleStem : String

private def RenderRole.name : RenderRole -> String
| .initialization _ => "initialization"
| .maintenance _ => "maintenance"
| .termination => "termination"

private def initSpec
    {Gamma : UnnamedSchema WhielNames}
    (row : CatalogRow Gamma)
    (ordinal : Nat) : RenderSpec :=
  { id := LeveledFamily.initializationJobId ordinal
    role := .initialization ordinal
    selector := .initialization row.clauseId
    ordinal
    clauseId := some row.clauseId
    level := some row.level
    jobName := "initJob" ++ toString ordinal
    statementName :=
      "candidate_init_clause_" ++ toString ordinal ++ "_stmt"
    emptyName := "initNoEmpty" ++ toString ordinal
    shallowName := "initShallow" ++ toString ordinal
    validName := "initValid" ++ toString ordinal
    moduleStem := "InitClause" ++ toString ordinal }

private def maintenanceSpec
    {Gamma : UnnamedSchema WhielNames}
    (coreSize : Nat)
    (row : CatalogRow Gamma)
    (rowOrdinal : Nat) : RenderSpec :=
  { id := LeveledFamily.maintenanceJobId rowOrdinal
    role := .maintenance rowOrdinal
    selector := .maintenance row.clauseId
    ordinal := coreSize + rowOrdinal
    clauseId := some row.clauseId
    level := some row.level
    jobName := "maintJob" ++ toString rowOrdinal
    statementName :=
      "candidate_maint_clause_" ++ toString rowOrdinal ++
        "_stmt"
    emptyName := "maintNoEmpty" ++ toString rowOrdinal
    shallowName := "maintShallow" ++ toString rowOrdinal
    validName := "maintValid" ++ toString rowOrdinal
    moduleStem := "MaintClause" ++ toString rowOrdinal }

private def terminationSpec (coreSize : Nat) : RenderSpec :=
  { id := LeveledFamily.terminationJobId
    role := .termination
    selector := .termination
    ordinal := 2 * coreSize
    clauseId := none
    level := none
    jobName := "termJob"
    statementName := "candidate_term_stmt"
    emptyName := "termNoEmpty"
    shallowName := "termShallow"
    validName := "termValid"
    moduleStem := "TermCheck" }

private def renderSpecs
    {Gamma : UnnamedSchema WhielNames}
    (snapshot : Snapshot Gamma) : List RenderSpec :=
  let coreSize := snapshot.rows.length
  snapshot.rows.zipIdx.map (fun row => initSpec row.1 row.2) ++
    snapshot.rows.zipIdx.map (fun row =>
      maintenanceSpec coreSize row.1 row.2) ++
    [terminationSpec coreSize]

private def selectorJson : ObligationSelector -> Lean.Json
| .initialization clauseId =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "initialization"),
        ("clause_id", Lean.Json.num clauseId) ]
| .maintenance clauseId =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "maintenance"),
        ("clause_id", Lean.Json.num clauseId) ]
| .termination =>
    Lean.Json.mkObj [("kind", Lean.Json.str "termination")]

/-
  Row ordinals grouped by level: entry `k` lists, in row
  order, the clause names of every row at level `k`.
-/
private def levelGroups
    {Gamma : UnnamedSchema WhielNames}
    (rows : List (CatalogRow Gamma)) : List (List Nat) :=
  let top := rows.foldl (fun acc row => max acc row.level) 0
  if rows.isEmpty then [] else
    (List.range (top + 1)).map fun level =>
      (rows.zipIdx.filter fun pair => pair.1.level == level).map
        fun pair => pair.2

/- Emitter-owned name of the certificate's level list. -/
private def levelsName : String :=
  "candidateLevels"

private def renderLevelsDeclaration
    {Gamma : UnnamedSchema WhielNames}
    (snapshot : Snapshot Gamma) : String :=
  let groups := (levelGroups snapshot.rows).map fun ordinals =>
    "[" ++ String.intercalate ", " (ordinals.map clauseName) ++
      "]"
  "def " ++ levelsName ++ " :\n" ++
    "    List (List (QFAssertExpr Data " ++ prophecySchemaName ++
      ")) :=\n  " ++ renderList "    " groups

private def renderJobDeclaration
    (spec : RenderSpec) : String :=
  let jobExpression := match spec.role with
    | .initialization ordinal =>
        "LeveledFamily.initJob " ++ certifiedLoopName ++ " " ++
          levelsName ++ " " ++ toString ordinal
    | .maintenance ordinal =>
        "LeveledFamily.maintJob " ++ certifiedLoopName ++ " " ++
          levelsName ++ " " ++ toString ordinal
    | .termination =>
        "LeveledFamily.termJob " ++ certifiedLoopName ++ " " ++
          levelsName
  "abbrev " ++ spec.jobName ++ " := " ++ jobExpression

private def renderStatement (spec : RenderSpec) : String :=
  "abbrev " ++ spec.statementName ++ " : Prop :=\n" ++
    "  " ++ spec.jobName ++ ".ShallowTarget"

private def jobsSource
    {Gamma : UnnamedSchema WhielNames}
    (binding : InputBinding)
    (snapshot : Snapshot Gamma)
    (specs : List RenderSpec) : String :=
  let namespaceName := binding.certificateNamespace
  sourcePreamble
      [binding.certificateModule ++ ".Proposal",
        "Whiel.Synthesis.FrameworkII.FixedAmbient." ++
          "CertificateJobs"]
      ("The exact FO-expressible entailments (verification " ++
        "conditions) required to show that the proposal is a " ++
        "sufficient inductive invariant for the preprocessed " ++
        "Hoare triple.")
      namespaceName ++
    renderLevelsDeclaration snapshot ++ "\n\n" ++
    String.intercalate "\n" (specs.map renderJobDeclaration) ++
    "\n\n" ++
    String.intercalate "\n\n" (specs.map renderStatement) ++
    "\n" ++
    sourcePostamble namespaceName

private def emptyCheckModule
    (binding : InputBinding)
    (spec : RenderSpec) : String :=
  binding.certificateModule ++ ".EmptyCexCheck." ++
    spec.moduleStem

private def emptyCheckSource
    (binding : InputBinding)
    (spec : RenderSpec) : String :=
  let namespaceName := binding.certificateNamespace
  sourcePreamble
      [binding.certificateModule ++ ".Jobs",
        "Whiel.Vampire.EmptyDomainLRAT"]
      ("The verification condition `" ++ spec.id ++
        "` is not falsified by an empty instance.")
      namespaceName ++
    "theorem " ++ spec.emptyName ++ " :\n" ++
    "    " ++ spec.jobName ++
      ".entailment.emptyCounterexample? = " ++
      "Bool.false := by\n" ++
    "  apply Whiel.Vampire.EmptyDomainLRAT." ++
      "emptyCounterexample_eq_false\n" ++
    "  kernel_cnf_lrat\n" ++
    "    (include_str \"Resources/" ++ spec.id ++
      ".cnf\")\n" ++
    "    (include_str \"Resources/" ++ spec.id ++
      ".lrat\")\n" ++
    sourcePostamble namespaceName

private def proofModule
    (binding : InputBinding)
    (spec : RenderSpec) : String :=
  binding.certificateModule ++ ".VampireProofJobs." ++
    spec.moduleStem

private def proofNamespace
    (binding : InputBinding)
    (spec : RenderSpec) : String :=
  binding.certificateNamespace ++ ".VampireProofs." ++
    spec.moduleStem

private def reconstructionModule
    (binding : InputBinding)
    (spec : RenderSpec) : String :=
  binding.certificateModule ++ ".Reconstructions." ++
    spec.moduleStem

private def reconstructionSource
    (binding : InputBinding)
    (spec : RenderSpec) : String :=
  let namespaceName := binding.certificateNamespace
  let rawTheorem := proofNamespace binding spec ++ ".fullProof"
  sourcePreamble
      [emptyCheckModule binding spec,
        proofModule binding spec,
        "Whiel.Synthesis.FrameworkII.FixedAmbient." ++
          "CertifyJob"]
      ("Uses the `certify_job` tactic to convert the " ++
        "leancheck proof of `" ++ spec.id ++ "` into a proof " ++
        "of `" ++ spec.validName ++ "`.")
      namespaceName ++
    "theorem " ++ spec.shallowName ++ " :\n" ++
    "    " ++ spec.statementName ++ " := by\n" ++
    "  certify_job " ++ spec.jobName ++ "\n" ++
    "    " ++ rawTheorem ++ "\n\n" ++
    "theorem " ++ spec.validName ++ " :\n" ++
    "    " ++ spec.jobName ++ ".entailment.Valid :=\n" ++
    "  " ++ spec.jobName ++ ".valid_of_fullProof\n" ++
    "    " ++ spec.emptyName ++ " " ++ spec.shallowName ++
      "\n" ++
    sourcePostamble namespaceName

/-
  The inline clause-proof spine, one `.cons` per family row
  in family order, closed by `.nil`, as indented argument
  lines of the entry-point application.
-/
private def clauseProofSpineSource
    (specs : List RenderSpec) : String :=
  let initSpecs := specs.filter fun spec =>
    match spec.role with
    | .initialization _ => true
    | _ => false
  let maintSpecs := specs.filter fun spec =>
    match spec.role with
    | .maintenance _ => true
    | _ => false
  let conses := (initSpecs.zip maintSpecs).map fun pair =>
    ".cons ⟨" ++ pair.1.validName ++ ", " ++
      pair.2.validName ++ "⟩ <|"
  let items := conses ++ [".nil)"]
  "    (" ++ String.intercalate "\n      " items

/- Name of the final theorem every certificate proves. -/
def certificateTheoremName : String :=
  "input_hoare_triple_valid"

/- Module stem of the final certificate module. -/
def validModuleStem : String :=
  "Valid"

private def validSource
    (binding : InputBinding)
    (specs : List RenderSpec) : String :=
  let names := inputNames
  let namespaceName := binding.certificateNamespace
  sourcePreamble (specs.map (reconstructionModule binding))
      ("Proves the input Hoare triple from the clause proofs " ++
        "and prints its axioms.")
      namespaceName frameworkOpens
      ["linter.hashCommand false"] ++
    "theorem " ++ certificateTheoremName ++ " :\n" ++
    "    HoareValid " ++ names.pre ++ " " ++ names.cmd ++
      " " ++ names.post ++ " :=\n" ++
    "  Preproc.certifyProgramInput_of_clauseProofs\n" ++
    "    " ++ names.preproc ++ " " ++ levelsName ++ "\n" ++
    clauseProofSpineSource specs ++ "\n" ++
    "    termValid\n\n" ++
    axiomGuardComment namespaceName
      certificateTheoremName ++
    "#guard_msgs (whitespace := lax) in\n" ++
    "#print axioms " ++ certificateTheoremName ++ "\n" ++
    sourcePostamble namespaceName

------------------------------------------------------------
-- Invalidity Source Rendering
------------------------------------------------------------

/- Repository-relative path of one emitted artifact. -/
private def sourcePath
    (binding : InputBinding)
    (suffix : String) : String :=
  "Benchmark/" ++ binding.canonicalId ++ "/Certificate/" ++
    suffix


/- Name of the theorem every invalidity certificate proves. -/
def invalidTheoremName : String :=
  "input_hoare_triple_invalid"

/- Module stem of the emitted invalidity certificate. -/
def invalidModuleStem : String :=
  "Invalid"

/- Emitter-owned name of the frozen counterexample. -/
private def counterExampleName : String :=
  "counterExampleInput"

/- Emitter-owned name of the frozen certifying fuel. -/
private def counterExampleFuelName : String :=
  "counterExampleFuel"

/- One domain constant in the instance notation. -/
private def renderNotationData : Data -> String
| .num value => toString value
| .str value => String.quote value
| .bool true => "true"
| .bool false => "false"

private def renderNotationRow
    (cells : List Data) : String :=
  "[" ++
    String.intercalate ", " (cells.map renderNotationData) ++
    "]"

/-
  One relation of the record as a notation update. The
  relation is named by the spelling the notation reads back
  to the same program name, so each emitted update
  preserves the record's canonical relation key.
-/
private def renderNotationUpdate
    (relation : String × ProgramInstance.Rows) :
    Except String String := do
  let some name := ProgramNames.parse? relation.1
    | throw ("the counterexample names a relation whose " ++
        "canonical key does not parse: " ++ relation.1)
  unless ProgramNames.encode name == relation.1 do
    throw ("the counterexample names a relation whose " ++
      "key is not canonical: " ++ relation.1)
  pure (ProgramNames.spell name ++ " := [" ++
    String.intercalate ", "
      (relation.2.map renderNotationRow) ++ "]")

/-
  The frozen instance in the program-name instance
  notation, one update per relation the record carries.
-/
private def renderCounterExampleNotation
    (schema : String)
    (rows : ProgramInstance.KeyedRows) :
    Except String String := do
  match rows with
  | [] =>
      pure ("programInst![" ++ schema ++ "]")
  | _ =>
      let updates ← rows.mapM renderNotationUpdate
      pure ("programInst![" ++ schema ++ " |\n    " ++
        String.intercalate ";\n    " updates ++ " ]")

/-
  The complete invalidity certificate. It names the frozen
  instance, the frozen fuel, and nothing else: the theorem
  is closed by the kernel checker on those two values alone.
  The instance is written once, in the program-name
  notation that the kernel checker consumes directly.
-/
private def invalidSource
    (binding : InputBinding)
    (rows : ProgramInstance.KeyedRows)
    (fuel : Nat) : Except String String := do
  let names := inputNames
  let namespaceName := binding.certificateNamespace
  let instanceText ←
    renderCounterExampleNotation names.schema rows
  pure <|
  sourcePreamble
      [binding.moduleName,
        "Whiel.Eval.CounterExample.InstanceNotation",
        "Whiel.Eval.CounterExample.Kernel"]
      ("Refutes the input Hoare triple from the frozen " ++
        "counterexample instance and the frozen fuel, and " ++
        "prints its axioms.")
      namespaceName ["Whiel", "Whiel.Concrete"]
      ["linter.hashCommand false"] ++
    "def " ++ counterExampleName ++ " : Instance Data " ++
      names.schema ++ " :=\n" ++
    "  " ++ instanceText ++ "\n\n" ++
    "def " ++ counterExampleFuelName ++ " : Nat := " ++
      toString fuel ++ "\n\n" ++
    "theorem " ++ invalidTheoremName ++ " :\n" ++
    "    ¬ Whiel.HoareValid " ++ names.pre ++ " " ++
      names.cmd ++ " " ++ names.post ++ " :=\n" ++
    "  Whiel.Hoare.CounterExample.certifyKernel\n" ++
    "    " ++ counterExampleFuelName ++ " " ++
      counterExampleName ++ "\n\n" ++
    axiomGuardComment namespaceName invalidTheoremName ++
    "#guard_msgs (whitespace := lax) in\n" ++
    "#print axioms " ++ invalidTheoremName ++ "\n" ++
    sourcePostamble namespaceName

------------------------------------------------------------
-- Invalidity Emission
------------------------------------------------------------

/- Complete frozen identity of one accepted counterexample. -/
def counterExampleIdentityJson
    {Gamma : UnnamedSchema ProgramNames}
    (record : Counterexample.Record Gamma) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_fixed_ambient_counterexample"),
      ("version", Lean.Json.num 1),
      ("instance_identity", Lean.Json.str record.identity),
      ("fuel", Lean.Json.num record.fuelConsumed),
      ("instance", record.canonicalJson) ]

/-
  Emit the complete invalidity certificate for one validated
  counterexample. The rendered literal is rebuilt and
  re-checked here, so the emitted source is refused unless it
  denotes the frozen instance and that instance refutes the
  raw input triple under the frozen fuel.
-/
def emitInvalid
    {Gamma : UnnamedSchema ProgramNames}
    (pre : AssertExpr Data Gamma)
    (cmd : Cmd Data Gamma)
    (post : AssertExpr Data Gamma)
    (binding : InputBinding)
    (scopeIdentity : Lean.Json)
    (record : Counterexample.Record Gamma) :
    Except String Bundle := do
  binding.validate
  let rebuilt :=
    ProgramInstance.ofKeyedRows Gamma record.keyedRows
  unless CounterexampleCodec.canonicalJson Gamma rebuilt ==
      record.canonicalJson do
    throw ("the rendered counterexample literal is not the " ++
      "frozen instance")
  unless Hoare.CounterExample.kernelRefutes
      record.fuelConsumed pre cmd post rebuilt do
    throw ("the rendered counterexample literal does not " ++
      "refute the input triple under the frozen fuel")
  let identity := counterExampleIdentityJson record
  let contents ←
    invalidSource binding record.keyedRows
      record.fuelConsumed
  pure
    { inputIdentity := binding.identityJson
      scopeIdentity
      snapshotIdentity := identity
      inputSourceSha256 := binding.sourceSha256
      coreSize := 0
      certificateModule :=
        binding.certificateModule ++ "." ++
          invalidModuleStem
      certificateTheorem :=
        binding.certificateNamespace ++ "." ++
          invalidTheoremName
      artifacts :=
        [ { relativePath := sourcePath binding
              (invalidModuleStem ++ ".lean")
            contents } ]
      jobs := [] }

------------------------------------------------------------
-- Raw Proof Packaging
------------------------------------------------------------

private def rawImportLine : String :=
  "import VampLean"

private def rawTheoremPrefix : String :=
  "theorem fullProof "

private def rawSectionEnd : String :=
  "end vamproof"

/-
  The Lean modules a packaged proof may import besides the
  pinned VampLean runtime. Vampire never emits one of these:
  they are requested by the caller for text an untrusted
  proof transformation rewrote to call a Whiel-owned or
  Mathlib tactic. The list is pinned here rather than taken
  on trust from the request, so a caller can only choose
  among imports this emitter already admits. One entry per
  transformation, so independently developed transformations
  do not collide here.
-/
private def permittedExtraImports : List String :=
  -- targeted clause projection (transformation 4)
  [ "Whiel.Vampire.ClauseProjection",
    -- kernel-checked LRAT for AVATAR refutations (transformation 2)
    "Mathlib.Tactic.Sat.FromLRAT" ]

private def withoutDuplicates
    (names : List String) : List String :=
  names.foldl
    (fun accumulated name =>
      if accumulated.contains name then accumulated
      else accumulated ++ [name])
    []

/-
  Deterministic module packaging of one raw leancheck output.
  Exactly one `import VampLean` line is followed by the
  requested extra imports, the module's header comment,
  opening the pinned runtime namespace, and the job's proof
  namespace; the namespace is closed after the raw text. No
  other byte of the raw proof changes, and an empty
  `extraImports` reproduces the earlier packaging byte for
  byte. The raw text itself must carry no import line but
  the pinned runtime's: every extra import is supplied by
  the request, never smuggled in by a rewrite.
-/
def packageProof
    (jobId proofNamespace : String)
    (raw : String)
    (extraImports : List String := []) : Except String String := do
  match extraImports.find?
      (fun name => !permittedExtraImports.contains name) with
    | some name =>
        throw ("proof packaging refuses the extra import " ++ name)
    | none => pure ()
  unless (withoutDuplicates extraImports).length ==
      extraImports.length do
    throw "proof packaging received a repeated extra import"
  let lines := raw.splitOn "\n"
  let importCount :=
    (lines.filter fun line => line == rawImportLine).length
  unless importCount == 1 do
    throw "raw leancheck output must import VampLean exactly once"
  if lines.any fun line =>
      line.startsWith "import " && line != rawImportLine then
    throw "raw leancheck output has a foreign import"
  unless lines.any fun line =>
      line.startsWith rawTheoremPrefix do
    throw "raw leancheck output declares no fullProof"
  unless lines.any fun line => line == rawSectionEnd do
    throw "raw leancheck output does not close its section"
  if lines.any fun line =>
      line.startsWith "namespace " || line.startsWith "end " &&
        line != rawSectionEnd then
    throw "raw leancheck output already carries a namespace"
  let header := headerLines
    ("The leancheck proof of `" ++ jobId ++ "` as emitted by " ++
      "the pinned Vampire, with only the namespace and " ++
      "`open` added.")
  let packaged := lines.flatMap fun line =>
    if line == rawImportLine then
      [line] ++ (extraImports.map fun name => "import " ++ name) ++
        [""] ++ header ++
        ["", "open VampLean", "namespace " ++ proofNamespace]
    else
      [line]
  return String.intercalate "\n" packaged ++
    "\nend " ++ proofNamespace ++ "\n"

------------------------------------------------------------
-- Emission
------------------------------------------------------------

private def snapshotRowIdentity
    {Gamma : UnnamedSchema WhielNames}
    (row : CatalogRow Gamma) : Lean.Json :=
  Lean.Json.mkObj
    [ ("clause_id", Lean.Json.num row.clauseId),
      ("level", Lean.Json.num row.level),
      ("identity", row.clause.identityJson),
      ("canonical_source",
        Lean.Json.str row.clause.canonicalSource) ]

/- Complete identity of the frozen Core being certified. -/
def snapshotIdentity
    {Gamma : UnnamedSchema WhielNames}
    (snapshot : Snapshot Gamma) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_fixed_ambient_snapshot"),
      ("version", Lean.Json.num 1),
      ("rows", Lean.Json.arr
        (snapshot.rows.map snapshotRowIdentity).toArray) ]

private def certificateJobIdentity
    (binding : InputBinding)
    (scopeIdentity snapshotIdentity : Lean.Json)
    (spec : RenderSpec)
    (problemSha256 : String) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_fixed_ambient_certificate_job"),
      ("version", Lean.Json.num 1),
      ("input_identity", binding.identityJson),
      ("scope_identity", scopeIdentity),
      ("snapshot_identity", snapshotIdentity),
      ("selector", selectorJson spec.selector),
      ("job_id", Lean.Json.str spec.id),
      ("role", Lean.Json.str spec.role.name),
      ("ordinal", Lean.Json.num spec.ordinal),
      ("problem_sha256", Lean.Json.str problemSha256),
      ("proof_module", Lean.Json.str
        (proofModule binding spec)),
      ("proof_namespace", Lean.Json.str
        (proofNamespace binding spec)),
      ("proof_theorem", Lean.Json.str "fullProof"),
      ("reconstruction_module", Lean.Json.str
        (reconstructionModule binding spec)) ]

private def proofJob
    {Gamma : UnnamedSchema WhielNames}
    (binding : InputBinding)
    (scopeIdentity snapshotIdentity : Lean.Json)
    (spec : RenderSpec)
    (job : CertificateJob Data Gamma) : ProofJob :=
  let tptp := job.tptp
  let cnf :=
    job.entailment.toRelCalcEntailment.emptyCNF.dimacs
  let problemSha256 := CanonicalDigest.sha256 tptp
  let identity := certificateJobIdentity binding
    scopeIdentity snapshotIdentity spec problemSha256
  { id := spec.id
    role := spec.role.name
    ordinal := spec.ordinal
    clauseId := spec.clauseId
    level := spec.level
    selectorIdentity := selectorJson spec.selector
    jobIdentity := identity
    jobDigest := CanonicalDigest.jsonSha256 identity
    problemRelativePath := sourcePath binding <|
      "VampireArtifacts/jobs/" ++ spec.id ++ "/problem.p"
    problemSha256
    leancheckOutputRelativePath := sourcePath binding <|
      "VampireArtifacts/jobs/" ++ spec.id ++ "/leancheck.lean"
    proofModuleRelativePath := sourcePath binding <|
      "VampireProofJobs/" ++ spec.moduleStem ++ ".lean"
    proofModule := proofModule binding spec
    proofNamespace := proofNamespace binding spec
    proofTheorem := "fullProof"
    reconstructionModule := reconstructionModule binding spec
    emptyCheck :=
      { cnfRelativePath := sourcePath binding <|
          "EmptyCexCheck/Resources/" ++ spec.id ++ ".cnf"
        cnfSha256 := CanonicalDigest.sha256 cnf
        lratRelativePath := sourcePath binding <|
          "EmptyCexCheck/Resources/" ++ spec.id ++ ".lrat"
        moduleRelativePath := sourcePath binding <|
          "EmptyCexCheck/" ++ spec.moduleStem ++ ".lean"
        moduleName := emptyCheckModule binding spec
        theoremName :=
          binding.certificateNamespace ++ "." ++
            spec.emptyName
        cnf }
    tptp }

private def sourceArtifacts
    {Gamma : UnnamedSchema WhielNames}
    (binding : InputBinding)
    (snapshot : Snapshot Gamma)
    (specs : List RenderSpec) :
    Except String (List Artifact) := do
  let proposal <- proposalSource binding snapshot
  pure <|
    [ { relativePath := sourcePath binding "Proposal.lean"
        contents := proposal },
      { relativePath := sourcePath binding "ProposalBinding.lean"
        contents := proposalBindingSource binding snapshot },
      { relativePath := sourcePath binding "Jobs.lean"
        contents := jobsSource binding snapshot specs } ] ++
    specs.map (fun spec =>
      { relativePath := sourcePath binding <|
          "EmptyCexCheck/" ++ spec.moduleStem ++ ".lean"
        contents := emptyCheckSource binding spec }) ++
    specs.map (fun spec =>
      { relativePath := sourcePath binding <|
          "Reconstructions/" ++ spec.moduleStem ++ ".lean"
        contents := reconstructionSource binding spec }) ++
    [ { relativePath := sourcePath binding
          (validModuleStem ++ ".lean")
        contents := validSource binding specs } ]

/-
  Re-admit one retained row from its canonical source and
  require complete catalog identity agreement.
-/
private def readmitRow
    {Gamma : UnnamedSchema WhielNames}
    (row : CatalogRow Gamma) : Except String Unit := do
  let readmitted <- match
      admitClause Gamma row.clause.canonicalSource with
    | .ok clause => pure clause
    | .error (.correctable diagnostic) =>
        throw ("retained clause source is no longer admissible: " ++
          diagnostic.message)
    | .error (.infrastructure message) => throw message
  unless readmitted.identity = row.clause.identity do
    throw "retained clause source disagrees with its structural identity"
  unless readmitted.identityJson == row.clause.identityJson do
    throw "retained clause source disagrees with its identity token"
  unless readmitted.formula.toRaw = row.clause.formula.toRaw do
    throw "retained clause source disagrees with its typed formula"
  unless readmitted.display == row.clause.display do
    throw "retained clause display is not canonical"
  unless readmitted.orderKey == row.clause.orderKey do
    throw "retained clause order key is not canonical"
  unless readmitted.relationKeys == row.clause.relationKeys do
    throw "retained clause relation keys are not canonical"
  unless row.level >= readmitted.minimumLevel do
    throw "retained row violates its Lean-owned minimum level"

private def noDuplicateRowIds
    {Gamma : UnnamedSchema WhielNames}
    (rows : List (CatalogRow Gamma)) : Bool :=
  (rows.map CatalogRow.clauseId).Nodup

private def noDuplicateRowIdentities
    {Gamma : UnnamedSchema WhielNames}
    (rows : List (CatalogRow Gamma)) : Bool :=
  (rows.map fun row => row.clause.identity).Nodup

/- Row levels never decrease along the catalog order. -/
private def levelsOrdered
    {Gamma : UnnamedSchema WhielNames}
    (rows : List (CatalogRow Gamma)) : Bool :=
  decide ((rows.map CatalogRow.level).Pairwise (· ≤ ·))

/-
  The level-list family the certificate declares: the rows
  grouped by level, in row order within each level.
-/
private def levelFamily
    {Gamma : UnnamedSchema WhielNames}
    (snapshot : Snapshot Gamma) : LeveledFamily Data Gamma :=
  LeveledFamily.ofLevels <|
    (levelGroups snapshot.rows).map fun ordinals =>
      ordinals.filterMap fun ordinal =>
        (snapshot.rows[ordinal]?).map fun row =>
          row.clause.formula

private def rawRows
    {Gamma : UnnamedSchema WhielNames}
    (family : LeveledFamily Data Gamma) :
    List (RawGuard WhielNames Data × Nat) :=
  family.clauses.map fun clause =>
    (clause.formula.toRaw, clause.level)

/-
  Emit the complete pure certificate plan for one frozen
  Core over a program-name input. The jobs are the exact
  `2N+1` entailments of the lifted loop over the computed
  prophecy schema. Every row is re-admitted before any
  artifact is returned. Each empty-domain CNF is emitted
  for later SAT solving and kernel replay.
-/
def emit
    {Gamma : UnnamedSchema ProgramNames}
    {inputPre inputPost : AssertExpr Data Gamma}
    {inputCmd : Cmd Data Gamma}
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (binding : InputBinding)
    (scopeIdentity : Lean.Json)
    (snapshot : Snapshot (Preproc.loop P).prophecySchema) :
    Except String Bundle := do
  binding.validate
  for row in snapshot.rows do
    readmitRow row
  unless noDuplicateRowIds snapshot.rows do
    throw "snapshot repeats a clause_id"
  unless noDuplicateRowIdentities snapshot.rows do
    throw "snapshot repeats a formula identity"
  unless levelsOrdered snapshot.rows do
    throw "snapshot rows are not ordered by level"
  let loop := Preproc.loop P
  let family := levelFamily snapshot
  unless rawRows family = rawRows snapshot.family do
    throw "certificate level list disagrees with the snapshot family"
  let jobs := family.certificateJobs loop.task
    loop.lift.guard loop.lift.body_loopFree
    loop.lift.pre loop.lift.post
  let specs := renderSpecs snapshot
  unless specs.length == jobs.length do
    throw "certificate job rendering lost the exact 2N+1 order"
  for pair in specs.zip jobs do
    unless pair.1.id == pair.2.id do
      throw "certificate job identifier disagrees with the exact Lean job"
  let identity := snapshotIdentity snapshot
  let proofJobs := (specs.zip jobs).map fun pair =>
    proofJob binding scopeIdentity identity pair.1 pair.2
  let problemArtifacts := proofJobs.map fun job =>
    { relativePath := job.problemRelativePath
      contents := job.tptp }
  let emptyArtifacts := proofJobs.map fun job =>
    { relativePath := job.emptyCheck.cnfRelativePath
      contents := job.emptyCheck.cnf }
  let sources <- sourceArtifacts binding snapshot specs
  pure
    { inputIdentity := binding.identityJson
      scopeIdentity
      snapshotIdentity := identity
      inputSourceSha256 := binding.sourceSha256
      coreSize := snapshot.rows.length
      certificateModule :=
        binding.certificateModule ++ "." ++ validModuleStem
      certificateTheorem :=
        binding.certificateNamespace ++ "." ++
          certificateTheoremName
      artifacts :=
        sources ++ problemArtifacts ++ emptyArtifacts
      jobs := proofJobs }

end CertificateEmitter
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel
