-- Author: Jesse Comer
import Benchmark.Example0001.Input
import Whiel.Synthesis.Tests.FixedAmbientFlaggedFixture
import Whiel.Synthesis.FrameworkII.FixedAmbient.CertificateEmitter

set_option linter.hashCommand false

/-
  Executable checks for the Lean-owned fixed-ambient
  certificate emitter: deterministic emission, exact job
  order and identifiers, the emitted module shape, catalog
  re-admission, exact empty-domain CNFs, level-order
  rejection, input-binding validation, and raw-proof
  packaging.

  The test binds the immutable `Example0001` input
  directly, independently of any runtime registry.
-/

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIFixedAmbientCertificate

open Concrete
open FrameworkII.FixedAmbient
open FrameworkII.FixedAmbient.CertificateEmitter
open Benchmark.Example0001

/- The preprocessed input loop and its prophecy schema. -/
private abbrev certifiedLoop :
    Hoare.LoopTriple Data inputPreproc.outSchema :=
  Preproc.loop inputPreproc

private abbrev prophecySchema : UnnamedSchema WhielNames :=
  certifiedLoop.prophecySchema

private abbrev FixtureClause :=
  FrameworkII.FixedAmbient.Clause prophecySchema

private abbrev FixtureSnapshot :=
  FrameworkII.FixedAmbient.Snapshot prophecySchema

/- Admit one canonical clause over the prophecy schema. -/
private def admitted (source : String) : FixtureClause :=
  match admitClause prophecySchema source with
  | .ok clause => clause
  | .error _ => FrameworkII.FixedAmbient.Clause.ofFormula .true

#guard (admitted "(op_zT = ∅[2])").canonicalSource ==
  "(op_zT = ∅[2])"

#guard (admitted "(op_zS = ∅[2])").canonicalSource ==
  "(op_zS = ∅[2])"

#guard (admitted "(yp_zT = ∅[2])").canonicalSource ==
  "(yp_zT = ∅[2])"

#guard (admitted "(¬((op_zT = ∅[2])))").canonicalSource ==
  "(¬((op_zT = ∅[2])))"

private def ordinaryClause : FixtureClause :=
  admitted "(op_zT = ∅[2])"

private def auxiliaryClause : FixtureClause :=
  admitted "(op_zS = ∅[2])"

/- The fixture's input binding, independent of the registry. -/
private def binding : InputBinding :=
  { canonicalId := "Example0001"
    moduleName := "Benchmark.Example0001.Input"
    namespaceName := "Whiel.Benchmark.Example0001"
    sourceSha256 :=
      "209e99c85d5c4ddb0509c4f48968a847" ++
        "e87743a52bf6e5e1fb941572f8b0a82d"
    semanticVersion := 1
    encodingVersion := 1 }

private def scopeIdentity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str "whiel_test_scope"),
      ("canonical_id", Lean.Json.str binding.canonicalId) ]

private def emitCertificate
    (snapshot : FixtureSnapshot) : Except String Bundle :=
  emit inputPreproc binding scopeIdentity snapshot

/- The mixed-arity, levels-0/1 two-row Core. -/
private def snapshot : FixtureSnapshot where
  rows :=
    [ { clauseId := 11, level := 0, clause := ordinaryClause },
      { clauseId := 12, level := 1, clause := auxiliaryClause } ]

private def bundle? : Option Bundle :=
  match emitCertificate snapshot with
  | .ok bundle => some bundle
  | .error _ => none

private def bundleError? : Option String :=
  match emitCertificate snapshot with
  | .ok _ => none
  | .error message => some message

#guard bundleError? == none

private def jobIds : List String :=
  (bundle?.map fun bundle => bundle.jobs.map ProofJob.id).getD []

/- Exact `2N+1` order and identifiers. -/
#guard jobIds ==
  ["init_clause_0", "init_clause_1", "maint_clause_0",
    "maint_clause_1", "term_check"]

#guard (bundle?.map fun bundle => bundle.coreSize) == some 2

#guard
  (bundle?.map fun bundle =>
    bundle.toJson.getObjValD "version") ==
    some (Lean.Json.num 2)

/- Existing semantic identity versions stay unchanged. -/
#guard
  (bundle?.map fun bundle =>
    bundle.inputIdentity.getObjValD "version" ==
      Lean.Json.num 1 &&
    bundle.snapshotIdentity.getObjValD "version" ==
      Lean.Json.num 1 &&
    bundle.jobs.all fun job =>
      job.jobIdentity.getObjValD "version" ==
        Lean.Json.num 1 &&
      job.jobDigest ==
        Runtime.CanonicalDigest.jsonSha256
          job.jobIdentity) ==
    some true

#guard
  (bundle?.map fun bundle =>
    bundle.jobs.map ProofJob.ordinal) == some [0, 1, 2, 3, 4]

#guard
  (bundle?.map fun bundle =>
    bundle.jobs.map ProofJob.role) ==
    some ["initialization", "initialization", "maintenance",
      "maintenance", "termination"]

#guard
  (bundle?.map fun bundle =>
    bundle.jobs.map ProofJob.clauseId) ==
    some [some 11, some 12, some 11, some 12, none]

#guard
  (bundle?.map fun bundle => bundle.certificateModule) ==
    some "Benchmark.Example0001.Certificate.Valid"

#guard
  (bundle?.map fun bundle => bundle.certificateTheorem) ==
    some ("Whiel.Benchmark.Example0001.Certificate." ++
      "input_hoare_triple_valid")

/- Deterministic emission: two emissions agree byte for byte. -/
#guard
  (match emitCertificate snapshot, emitCertificate snapshot with
    | .ok left, .ok right =>
        left.artifacts == right.artifacts &&
          left.jobs.map ProofJob.jobDigest ==
            right.jobs.map ProofJob.jobDigest
    | _, _ => false)

------------------------------------------------------------
-- Emitted Tree
------------------------------------------------------------

private def certificateRoot : String :=
  "Benchmark/Example0001/Certificate/"

private def artifactPaths : List String :=
  (bundle?.map fun bundle =>
    bundle.artifacts.map Artifact.relativePath).getD []

/- The exact source file list, in emission order. -/
private def moduleStems : List String :=
  ["InitClause0", "InitClause1", "MaintClause0",
    "MaintClause1", "TermCheck"]

#guard artifactPaths.take 14 ==
  (["Proposal.lean", "ProposalBinding.lean", "Jobs.lean"] ++
    moduleStems.map ("EmptyCexCheck/" ++ · ++ ".lean") ++
    moduleStems.map ("Reconstructions/" ++ · ++ ".lean") ++
    ["Valid.lean"]).map (certificateRoot ++ ·)

#guard (artifactPaths.drop 14).take 5 ==
  jobIds.map fun id =>
    certificateRoot ++ "VampireArtifacts/jobs/" ++ id ++
      "/problem.p"

#guard artifactPaths.drop 19 ==
  jobIds.map fun id =>
    certificateRoot ++ "EmptyCexCheck/Resources/" ++
      id ++ ".cnf"

/- LRAT is solver output; emission writes no placeholder. -/
#guard !(artifactPaths.any (·.endsWith ".lrat"))

#guard !(artifactPaths.contains
  (certificateRoot ++ "EmptyCexCheck.lean"))

#guard !(artifactPaths.contains
  (certificateRoot ++ "Reconstruction.lean"))

#guard !(artifactPaths.contains
  (certificateRoot ++ "Certificate.lean"))

#guard !(artifactPaths.contains
  (certificateRoot ++ "VCAssembly.lean"))

#guard
  (bundle?.map fun bundle =>
    bundle.jobs.map ProofJob.reconstructionModule) ==
    some
      ["Benchmark.Example0001.Certificate.Reconstructions.InitClause0",
        "Benchmark.Example0001.Certificate.Reconstructions.InitClause1",
        "Benchmark.Example0001.Certificate.Reconstructions.MaintClause0",
        "Benchmark.Example0001.Certificate.Reconstructions.MaintClause1",
        "Benchmark.Example0001.Certificate.Reconstructions.TermCheck"]

/- The emitted problems are the exact Lean job renderings. -/
#guard
  (match emitCertificate snapshot with
    | .ok bundle =>
        let jobs := snapshot.family.certificateJobs
          certifiedLoop.task certifiedLoop.lift.guard
          certifiedLoop.lift.body_loopFree
          certifiedLoop.lift.pre certifiedLoop.lift.post
        bundle.jobs.map ProofJob.tptp ==
          jobs.map CertificateJob.tptp
    | .error _ => false)

private def artifactSource (suffix : String) : String :=
  (bundle?.bind fun bundle =>
    (bundle.artifacts.find? fun artifact =>
      artifact.relativePath == certificateRoot ++ suffix)
      |>.map Artifact.contents).getD ""

/- Occurrences of `needle` in `haystack`. -/
private def count (haystack needle : String) : Nat :=
  (haystack.splitOn needle).length - 1

------------------------------------------------------------
-- Certificate Solver Names
------------------------------------------------------------

private def certificateJobList :
    List (CertificateJob Data prophecySchema) :=
  snapshot.family.certificateJobs
    certifiedLoop.task certifiedLoop.lift.guard
    certifiedLoop.lift.body_loopFree
    certifiedLoop.lift.pre certifiedLoop.lift.post

/-
  A certificate job names a relation by its clause source, so
  every rendered relation name parses back to the relation it
  names, and every constant name decodes to its value.
-/
#guard certificateJobList.all fun job =>
  job.nameEnv.relNames.all fun entry =>
    WhielNames.SurfaceSyntax.parse entry.2 == .ok entry.1

#guard certificateJobList.all fun job =>
  job.nameEnv.funNames.all fun entry =>
    Vampire.dataOfSolverName? entry.2 == some entry.1

/- The environment passes the check the renderer relies on. -/
#guard certificateJobList.all fun job => job.nameEnv.wellFormed

/- No problem text carries a printed Lean term any more. -/
#guard certificateJobList.all fun job =>
  count job.tptp "r_Whiel" == 0

/- The emitted Lean sources, without the opaque problems. -/
private def sourceArtifacts : List Artifact :=
  (bundle?.map fun bundle =>
    bundle.artifacts.filter fun artifact =>
      artifact.relativePath.endsWith ".lean").getD []

#guard sourceArtifacts.length == 14

/-
  Every emitted module carries the two banner lines, then
  imports, options, exactly one header block before its
  namespace, and no retired family, job-list, or assembly
  name.
-/
#guard sourceArtifacts.all fun artifact =>
  artifact.contents.startsWith
    ("-- Generated by the Lean-owned fixed-ambient " ++
      "certificate-emitter-v2.\n" ++
      "-- Do not edit by hand.\nimport ")

#guard sourceArtifacts.all fun artifact =>
  count artifact.contents "/-\n" == 1 &&
    count artifact.contents "\n-/\n\nnamespace " == 1 &&
    count artifact.contents "set_option maxRecDepth 1048576\n\n/-\n" == 1

/-
  Every emitted line fits the width once the axiom guard is
  wrapped; no comment is exempted any more.
-/
#guard sourceArtifacts.all fun artifact =>
  (artifact.contents.splitOn "\n").all fun line =>
    line.length <= 80

/-
  "Framework II" is retired from user-facing certificate
  text: no emitted artifact names it, in a banner, a header,
  or a rendered declaration.
-/
#guard
  (bundle?.map fun bundle =>
    bundle.artifacts.all fun artifact =>
      count artifact.contents "Framework II" == 0) ==
    some true

#guard sourceArtifacts.all fun artifact =>
  count artifact.contents "candidateFamily" == 0 &&
    count artifact.contents "def jobs" == 0 &&
    count artifact.contents "VCAssembly" == 0 &&
    count artifact.contents "ofLevels" == 0 &&
    count artifact.contents "candidateClauseProofs" == 0

/-
  Proposal.lean declares the computed loop and schema, then
  each clause in `qfAssert!` notation and the clause list;
  no guard, option, row, or constructor term appears.
-/
private def proposalSource : String :=
  artifactSource "Proposal.lean"

#guard count proposalSource
  ("/-\n  The candidate clauses over the computed prophecy " ++
    "schema.\n-/\n") == 1

#guard count proposalSource "QFAssertExpr Data prophecySchema :=" == 2

#guard count proposalSource "Preproc.loop inputPreproc" == 1

#guard count proposalSource "certifiedLoop.prophecySchema" == 1

#guard count proposalSource "qfAssert![" == 2

#guard count proposalSource "(T = ∅[2])" == 1

#guard count proposalSource "(S = ∅[2])" == 1

#guard count proposalSource "def candidateClauses :" == 1

#guard count proposalSource "#guard" == 0

#guard count proposalSource "hashCommand" == 0

#guard count proposalSource "SurfaceSyntax" == 0

#guard count proposalSource "candidateRow" == 0

#guard count proposalSource "ambientSchema" == 0

#guard count proposalSource "inputFrameworkIITask" == 0

#guard count proposalSource "display" == 0

#guard count proposalSource "RawRAExpr" == 0

#guard count proposalSource "Guard." == 0

#guard count proposalSource "by decide" == 0

#guard count proposalSource "⟨" == 0

/-
  ProposalBinding.lean carries exactly the per-clause printer
  guards, imports only the proposal and the surface syntax,
  and is not imported by any other emitted module.
-/
private def proposalBindingSource : String :=
  artifactSource "ProposalBinding.lean"

#guard count proposalBindingSource
  "import Benchmark.Example0001.Certificate.Proposal\n" == 1

#guard count proposalBindingSource
  "import Whiel.Synthesis.FrameworkII.FixedAmbient.SurfaceSyntax\n" == 1

#guard count proposalBindingSource "\nimport " == 2

#guard count proposalBindingSource "linter.hashCommand false" == 1

#guard count proposalBindingSource
  ("/-\n  A build-time sanity check that the clause notation " ++
    "parses\n  to the proposed clauses. It does not feed into " ++
    "the final\n  certificate proof.\n-/\n") == 1

#guard count proposalBindingSource
  "#guard SurfaceSyntax.source candidateClause0 ==\n  \"(op_zT = ∅[2])\"" == 1

#guard count proposalBindingSource
  "#guard SurfaceSyntax.source candidateClause1 ==\n  \"(op_zS = ∅[2])\"" == 1

#guard count proposalBindingSource "#guard" == 2

#guard count proposalBindingSource "def " == 0

#guard
  (bundle?.map fun bundle =>
    bundle.artifacts.all fun artifact =>
      artifact.relativePath ==
          certificateRoot ++ "ProposalBinding.lean" ||
        count artifact.contents "ProposalBinding" == 0) == some true

/-
  Jobs.lean carries only the level list, the five positional
  jobs over it, and the five `ShallowTarget` statements; no
  family or job list is declared.
-/
private def jobsSource : String :=
  artifactSource "Jobs.lean"

#guard count jobsSource
  ("/-\n  The exact FO-expressible entailments (verification\n" ++
    "  conditions) required to show that the proposal is a\n" ++
    "  sufficient inductive invariant for the preprocessed " ++
    "Hoare\n  triple.\n-/\n") == 1

#guard count jobsSource
  ("def candidateLevels :\n" ++
    "    List (List (QFAssertExpr Data prophecySchema)) :=\n" ++
    "  [\n    [candidateClause0],\n    [candidateClause1]\n  ]\n\n" ++
    "abbrev initJob0 :=") == 1

#guard count jobsSource
  ("abbrev initJob0 := " ++
    "LeveledFamily.initJob certifiedLoop candidateLevels 0\n") == 1

#guard count jobsSource
  ("abbrev initJob1 := " ++
    "LeveledFamily.initJob certifiedLoop candidateLevels 1\n") == 1

#guard count jobsSource
  ("abbrev maintJob0 := " ++
    "LeveledFamily.maintJob certifiedLoop candidateLevels 0\n") == 1

#guard count jobsSource
  ("abbrev maintJob1 := " ++
    "LeveledFamily.maintJob certifiedLoop candidateLevels 1\n") == 1

#guard count jobsSource
  ("abbrev termJob := " ++
    "LeveledFamily.termJob certifiedLoop candidateLevels\n") == 1

#guard count jobsSource
  ("abbrev candidate_init_clause_0_stmt : Prop :=\n" ++
    "  initJob0.ShallowTarget\n") == 1

#guard count jobsSource
  ("abbrev candidate_maint_clause_1_stmt : Prop :=\n" ++
    "  maintJob1.ShallowTarget\n") == 1

#guard count jobsSource
  "abbrev candidate_term_stmt : Prop :=\n  termJob.ShallowTarget\n" == 1

#guard count jobsSource ".ShallowTarget\n" == 5

#guard count jobsSource "\ndef " == 1

#guard count jobsSource "\nabbrev " == 10

#guard count jobsSource "candidateFamily" == 0

#guard count jobsSource "def jobs" == 0

#guard count jobsSource "LeveledFamily.ofLevels" == 0

#guard count jobsSource "certificateJobs" == 0

#guard count jobsSource "\ntheorem " == 0

#guard count jobsSource "#guard" == 0

#guard count jobsSource "candidateRow" == 0

#guard count jobsSource "initQF" == 0

#guard count jobsSource "maintQF" == 0

#guard count jobsSource "termQF" == 0

#guard count jobsSource "jobs_eq" == 0

#guard count jobsSource "rfl" == 0

#guard count jobsSource "Sorted" == 0

#guard count jobsSource "by decide" == 0

#guard count jobsSource "⟨" == 0

#guard count jobsSource "where" == 0

#guard count jobsSource "ofEntailment" == 0

#guard count jobsSource "ambientRelations" == 0

#guard count jobsSource "Env" == 0

#guard count jobsSource "ShallowTargetOfLists" == 0

#guard count jobsSource "WhielNames." == 0

/- Every reconstruction module certifies with `certify_job`. -/
private def reconstructionSource : String :=
  artifactSource "Reconstructions/MaintClause1.lean"

#guard count reconstructionSource
  ("/-\n  Uses the `certify_job` tactic to convert the " ++
    "leancheck\n  proof of `maint_clause_1` into a proof of " ++
    "`maintValid1`.\n-/\n") == 1

#guard count reconstructionSource
  ("theorem maintShallow1 :\n    candidate_maint_clause_1_stmt := by\n" ++
    "  certify_job maintJob1\n    Whiel.Benchmark." ++
    "Example0001.Certificate.VampireProofs." ++
    "MaintClause1.fullProof\n") == 1

#guard count reconstructionSource
  ("theorem maintValid1 :\n    maintJob1.entailment.Valid :=\n" ++
    "  maintJob1.valid_of_fullProof\n    maintNoEmpty1 maintShallow1\n") == 1

#guard count reconstructionSource
  ("import Benchmark.Example0001.Certificate." ++
    "EmptyCexCheck.MaintClause1\n") == 1

#guard count reconstructionSource
  ("import Benchmark.Example0001.Certificate." ++
    "VampireProofJobs.MaintClause1\n") == 1

#guard count reconstructionSource
  "import Whiel.Synthesis.FrameworkII.FixedAmbient.CertifyJob\n" == 1

#guard count reconstructionSource "exact_reconstruction" == 0

#guard count reconstructionSource "valid_of_fullProof_lists" == 0

#guard count reconstructionSource "maintQF" == 0

/- Each leaf proves just its own exact empty check. -/
private def emptyCheckSource : String :=
  artifactSource "EmptyCexCheck/MaintClause1.lean"

#guard count emptyCheckSource
  "import Benchmark.Example0001.Certificate.Jobs\n" == 1

#guard count emptyCheckSource
  "import Whiel.Vampire.EmptyDomainLRAT\n" == 1

#guard count emptyCheckSource "\nimport " == 2

#guard count emptyCheckSource
  ("theorem maintNoEmpty1 :\n" ++
    "    maintJob1.entailment.emptyCounterexample? = " ++
    "Bool.false := by\n") == 1

#guard count emptyCheckSource
  ("  apply Whiel.Vampire.EmptyDomainLRAT." ++
    "emptyCounterexample_eq_false\n" ++
    "  kernel_cnf_lrat\n" ++
    "    (include_str \"Resources/" ++
    "maint_clause_1.cnf\")\n" ++
    "    (include_str \"Resources/" ++
    "maint_clause_1.lrat\")\n") == 1

#guard count emptyCheckSource "\ntheorem " == 1
#guard count emptyCheckSource "decide" == 0

#guard moduleStems.all fun stem =>
  let source := artifactSource
    ("Reconstructions/" ++ stem ++ ".lean")
  count source
    ("import Benchmark.Example0001.Certificate." ++
      "EmptyCexCheck." ++ stem ++ "\n") == 1 &&
    count source "EmptyCexCheck." == 1

/- Operational metadata stays outside job identity. -/
#guard
  (bundle?.map fun bundle =>
    (bundle.jobs.zip moduleStems).all fun (job, stem) =>
      let check := job.emptyCheck
      check.toJson == Lean.Json.mkObj
        [ ("encoding_version", Lean.Json.num 1),
          ("cnf_relative_path", Lean.Json.str
            (certificateRoot ++
              "EmptyCexCheck/Resources/" ++
              job.id ++ ".cnf")),
          ("cnf_sha256", Lean.Json.str
            (Runtime.CanonicalDigest.sha256 check.cnf)),
          ("lrat_relative_path", Lean.Json.str
            (certificateRoot ++
              "EmptyCexCheck/Resources/" ++
              job.id ++ ".lrat")),
          ("module_relative_path", Lean.Json.str
            (certificateRoot ++ "EmptyCexCheck/" ++
              stem ++ ".lean")),
          ("module", Lean.Json.str
            ("Benchmark.Example0001.Certificate." ++
              "EmptyCexCheck." ++ stem)),
          ("theorem", Lean.Json.str check.theoremName) ] &&
      job.toJson.getObjValD "empty_check" == check.toJson &&
      artifactSource
        ("EmptyCexCheck/Resources/" ++ job.id ++ ".cnf") ==
          check.cnf) == some true

#guard
  (bundle?.map fun bundle =>
    bundle.jobs.map (·.emptyCheck.theoremName)) ==
    some (["initNoEmpty0", "initNoEmpty1", "maintNoEmpty0",
      "maintNoEmpty1", "termNoEmpty"].map fun name =>
        "Whiel.Benchmark.Example0001.Certificate." ++ name)

/- Recompute the CNF from the unchanged exact job list. -/
#guard
  (bundle?.map fun bundle =>
    bundle.jobs.map (·.emptyCheck.cnf)) ==
    some (certificateJobList.map fun job =>
      job.entailment.toRelCalcEntailment.emptyCNF.dimacs)

/-
  Valid.lean imports the five reconstruction modules
  directly, applies the program-input entry point to the
  level list and the inline clause-proof spine, and prints
  the axioms of the certificate theorem.
-/
private def validSource : String :=
  artifactSource "Valid.lean"

#guard count validSource
  ("import Benchmark.Example0001.Certificate." ++
    "Reconstructions.InitClause0\n" ++
    "import Benchmark.Example0001.Certificate." ++
    "Reconstructions.InitClause1\n" ++
    "import Benchmark.Example0001.Certificate." ++
    "Reconstructions.MaintClause0\n" ++
    "import Benchmark.Example0001.Certificate." ++
    "Reconstructions.MaintClause1\n" ++
    "import Benchmark.Example0001.Certificate." ++
    "Reconstructions.TermCheck\n") == 1

#guard count validSource "\nimport " == 5

#guard count validSource "Certificate.Reconstruction\n" == 0

#guard count validSource
  ("/-\n  Proves the input Hoare triple from the clause proofs " ++
    "and\n  prints its axioms.\n-/\n") == 1

#guard count validSource
  ("theorem input_hoare_triple_valid :\n" ++
    "    HoareValid inputPre inputCmd inputPost :=\n" ++
    "  Preproc.certifyProgramInput_of_clauseProofs\n" ++
    "    inputPreproc candidateLevels\n" ++
    "    (.cons ⟨initValid0, maintValid0⟩ <|\n" ++
    "      .cons ⟨initValid1, maintValid1⟩ <|\n" ++
    "      .nil)\n" ++
    "    termValid\n") == 1

#guard count validSource "\ntheorem " == 1

#guard count validSource "linter.hashCommand false" == 1

/-
  The axiom guard is wrapped to the emitter's comment width;
  `whitespace := lax` collapses the wrapping, so the message
  the guard accepts is unchanged.
-/
#guard validSource.endsWith
  ("/--\n  info:\n" ++
    "  'Whiel.Benchmark.Example0001.Certificate." ++
    "input_hoare_triple_valid'\n" ++
    "  depends on axioms: " ++
    "[propext, Classical.choice, Quot.sound]\n-/\n" ++
    "#guard_msgs (whitespace := lax) in\n" ++
    "#print axioms input_hoare_triple_valid\n\n" ++
    "end Whiel.Benchmark.Example0001.Certificate\n")

#guard count validSource "baseNameOnly" == 0

#guard count validSource "Option.some_get" == 0

------------------------------------------------------------
-- Rejections
------------------------------------------------------------

/- SAT obligations emit; only kernel replay can certify. -/
private def contradictoryClause : FixtureClause :=
  admitted "(¬((op_zT = ∅[2])))"

private def contradictorySnapshot : FixtureSnapshot where
  rows :=
    [ { clauseId := 21, level := 0,
        clause := contradictoryClause } ]

#guard
  (match emitCertificate contradictorySnapshot with
    | .ok bundle =>
        bundle.jobs.map ProofJob.id ==
          ["init_clause_0", "maint_clause_0",
            "term_check"] &&
        bundle.jobs.all fun job =>
          job.emptyCheck.cnf.startsWith "p cnf "
    | .error _ => false)

/- Repeated clause identifiers and identities reject. -/
private def repeatedIdSnapshot : FixtureSnapshot where
  rows :=
    [ { clauseId := 11, level := 0, clause := ordinaryClause },
      { clauseId := 11, level := 1, clause := auxiliaryClause } ]

#guard
  (match emitCertificate repeatedIdSnapshot with
    | .ok _ => false
    | .error message => (message.splitOn "clause_id").length > 1)

private def repeatedIdentitySnapshot : FixtureSnapshot where
  rows :=
    [ { clauseId := 11, level := 0, clause := ordinaryClause },
      { clauseId := 12, level := 0, clause := ordinaryClause } ]

#guard
  (match emitCertificate repeatedIdentitySnapshot with
    | .ok _ => false
    | .error message => (message.splitOn "identity").length > 1)

/- A prophecy-mentioning clause cannot sit below level one. -/
private def prophecyClause : FixtureClause :=
  admitted "(yp_zT = ∅[2])"

private def underLevelSnapshot : FixtureSnapshot where
  rows :=
    [ { clauseId := 31, level := 0, clause := prophecyClause } ]

#guard
  (match emitCertificate underLevelSnapshot with
    | .ok _ => false
    | .error message =>
        (message.splitOn "minimum level").length > 1)

/-
  Rows out of level order reject: the level-list family
  would reorder the jobs against the catalog.
-/
private def unorderedSnapshot : FixtureSnapshot where
  rows :=
    [ { clauseId := 12, level := 1, clause := auxiliaryClause },
      { clauseId := 11, level := 0, clause := ordinaryClause } ]

#guard
  (match emitCertificate unorderedSnapshot with
    | .ok _ => false
    | .error message =>
        (message.splitOn "ordered by level").length > 1)

/- A skipped level emits an empty level entry. -/
private def skippedLevelSnapshot : FixtureSnapshot where
  rows :=
    [ { clauseId := 11, level := 0, clause := ordinaryClause },
      { clauseId := 12, level := 2, clause := auxiliaryClause } ]

#guard
  (match emitCertificate skippedLevelSnapshot with
    | .ok bundle =>
        (bundle.artifacts.any fun artifact =>
          artifact.relativePath == certificateRoot ++ "Jobs.lean" &&
            count artifact.contents
              ("  [\n    [candidateClause0],\n    [],\n" ++
                "    [candidateClause1]\n  ]\n") == 1)
    | .error _ => false)

/- Input binding contract. -/
private def validates (binding : InputBinding) : Bool :=
  match binding.validate with
  | .ok () => true
  | .error _ => false

#guard validates binding

#guard !validates { binding with moduleName := "Benchmark.Other.Input" }

#guard !validates { binding with namespaceName := "Whiel.Benchmark.Other" }

#guard !validates { binding with sourceSha256 := "abc" }

#guard !validates { binding with canonicalId := "Fixed Ambient" }

------------------------------------------------------------
-- Raw Proof Packaging
------------------------------------------------------------

private def rawProof : String :=
  "-- Lean proof output generated by Vampire\n" ++
    "import VampLean\nsection vamproof\nuniverse u\n" ++
    "theorem fullProof : True := trivial\n" ++
    "end vamproof\n-- Version: test\n"

private def packages (raw : String) : Bool :=
  match packageProof "test_job" "Whiel.Test.Job" raw with
  | .ok _ => true
  | .error _ => false

/-
  The header block follows the one import and precedes the
  added `open` and namespace; the raw bytes are otherwise
  unchanged.
-/
#guard
  (match packageProof "test_job" "Whiel.Test.Job" rawProof with
    | .ok packaged =>
        (packaged.splitOn ("import VampLean\n\n/-\n" ++
          "  The leancheck proof of `test_job` as emitted by " ++
          "the pinned\n  Vampire, with only the namespace and " ++
          "`open` added.\n-/\n\nopen VampLean\n" ++
          "namespace Whiel.Test.Job\n")).length == 2 &&
        packaged.startsWith
          "-- Lean proof output generated by Vampire\n" &&
        packaged.endsWith
          ("end vamproof\n-- Version: test\n" ++
            "\nend Whiel.Test.Job\n") &&
        (packaged.splitOn "theorem fullProof").length == 2 &&
        (packaged.splitOn "/-\n").length == 2
    | .error _ => false)

#guard !packages (rawProof.replace "import VampLean\n" "")

#guard !packages (rawProof.replace "import VampLean\n"
  "import VampLean\nimport Mathlib\n")

#guard !packages (rawProof.replace "theorem fullProof" "theorem other")

#guard !packages (rawProof.replace "end vamproof\n" "")

#guard !packages ("namespace Foo\n" ++ rawProof)

/-
  A proof transformation that rewrote the text to call a
  Whiel-owned tactic asks for that tactic's module by name.
  The extra import follows the pinned VampLean import and
  precedes the header; only the emitter's own pinned list is
  admitted, and a repeated request is refused.
-/
#guard
  (match packageProof "test_job" "Whiel.Test.Job" rawProof
      ["Whiel.Vampire.ClauseProjection"] with
    | .ok packaged =>
        (packaged.splitOn ("import VampLean\n" ++
          "import Whiel.Vampire.ClauseProjection\n\n/-\n")).length
            == 2 &&
        (packaged.splitOn "import ").length == 3
    | .error _ => false)

#guard
  (match packageProof "test_job" "Whiel.Test.Job" rawProof [] with
    | .ok packaged =>
        (match packageProof "test_job" "Whiel.Test.Job" rawProof with
          | .ok default => packaged == default
          | .error _ => false)
    | .error _ => false)

/-
  The second admitted module: the kernel-checked LRAT
  rewrite of an AVATAR refutation calls Mathlib's
  `lrat_proof`, so `Mathlib.Tactic.Sat.FromLRAT` is on the
  pinned list too.
-/
#guard
  (match packageProof "test_job" "Whiel.Test.Job" rawProof
      ["Mathlib.Tactic.Sat.FromLRAT"] with
    | .ok packaged =>
        (packaged.splitOn ("import VampLean\n" ++
          "import Mathlib.Tactic.Sat.FromLRAT\n\n/-\n")).length
            == 2 &&
        (packaged.splitOn "import ").length == 3
    | .error _ => false)

/-
  Both admitted modules together, in the order the request
  gives them, one line each after the pinned runtime.
-/
#guard
  (match packageProof "test_job" "Whiel.Test.Job" rawProof
      ["Whiel.Vampire.ClauseProjection",
        "Mathlib.Tactic.Sat.FromLRAT"] with
    | .ok packaged =>
        (packaged.splitOn ("import VampLean\n" ++
          "import Whiel.Vampire.ClauseProjection\n" ++
          "import Mathlib.Tactic.Sat.FromLRAT\n\n/-\n")).length
            == 2 &&
        (packaged.splitOn "import ").length == 4
    | .error _ => false)

/-
  Nothing outside the pinned list, however plausible: the
  parent of an admitted module is not admitted, and neither
  is another Whiel module.
-/
#guard
  (match packageProof "test_job" "Whiel.Test.Job" rawProof
      ["Mathlib"] with
    | .ok _ => false
    | .error _ => true)

#guard
  (match packageProof "test_job" "Whiel.Test.Job" rawProof
      ["Mathlib.Tactic.Sat"] with
    | .ok _ => false
    | .error _ => true)

#guard
  (match packageProof "test_job" "Whiel.Test.Job" rawProof
      ["Whiel.Vampire"] with
    | .ok _ => false
    | .error _ => true)

#guard
  (match packageProof "test_job" "Whiel.Test.Job" rawProof
      ["Whiel.Vampire.ClauseProjection", "Mathlib"] with
    | .ok _ => false
    | .error _ => true)

#guard
  (match packageProof "test_job" "Whiel.Test.Job" rawProof
      ["Whiel.Vampire.ClauseProjection",
        "Whiel.Vampire.ClauseProjection"] with
    | .ok _ => false
    | .error _ => true)

/-
  An extra import is a *request*, never something the raw
  text may carry: a transformation that wrote its own import
  line into the proof is refused even when the module it
  names is on the pinned list, and refused again when the
  same module is also requested. The one import line the raw
  text may hold is the pinned runtime's.
-/
#guard !packages (rawProof.replace "import VampLean\n"
  "import VampLean\nimport Whiel.Vampire.ClauseProjection\n")

#guard !packages (rawProof.replace "import VampLean\n"
  "import VampLean\nimport Mathlib.Tactic.Sat.FromLRAT\n")

#guard
  (match packageProof "test_job" "Whiel.Test.Job"
      (rawProof.replace "import VampLean\n"
        "import VampLean\nimport Mathlib.Tactic.Sat.FromLRAT\n")
      ["Mathlib.Tactic.Sat.FromLRAT"] with
    | .ok _ => false
    | .error _ => true)

end FrameworkIIFixedAmbientCertificate
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Dependent Program Emission
------------------------------------------------------------

namespace Whiel.Synthesis.Tests.FixedAmbientFlaggedEmission

open FrameworkII.FixedAmbient.CertificateEmitter
open FixedAmbientFlaggedFixture

/-
  Structural emission checks use a test binding. The scratch
  driver supplies the actual adapter digest at kernel checks.
-/
private def binding : InputBinding where
  canonicalId := "FlaggedEmissions"
  moduleName := "Benchmark.FlaggedEmissions.Input"
  namespaceName := "Whiel.Benchmark.FlaggedEmissions"
  sourceSha256 := String.ofList (List.replicate 64 '0')
  semanticVersion := 1
  encodingVersion := 1

private def bundle : Option Bundle :=
  (emit inputPreproc binding Lean.Json.null
    snapshot).toOption

#guard bundle.isSome
#guard (bundle.map fun b => b.jobs.map ProofJob.id) ==
  some ["init_clause_0", "maint_clause_0", "term_check"]

private def proposal : String :=
  (((bundle.map fun b => b.artifacts).getD []).findSome?
    (fun a => if a.relativePath.endsWith "/Proposal.lean"
      then some a.contents else none)).getD ""

#guard (proposal.splitOn
  "Hoare.LoopTriple Data inputPreproc.outSchema").length
    == 2
#guard (proposal.splitOn
  "Hoare.LoopTriple Data inputSchema").length == 1
#guard
  (proposal.splitOn "Preproc.loop inputPreproc").length == 2

end Whiel.Synthesis.Tests.FixedAmbientFlaggedEmission
