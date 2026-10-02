# Auditing a Whiel certificate

This guide is for a reader who wants to know what a Whiel Lean certificate
establishes, and which definitions to read to judge whether its statement
means the intended database problem. It follows two representative
certificates from the source. Start with the exact theorem, then read the
definitions that give it meaning. Section 3 explains how the proofs are
assembled; section 5 gives commands for checking them. This map is not a complete transitive
dependency listing or a substitute for running those checks.

## 1. What a certificate claims

A certificate ends in one theorem about the benchmark input's own three
definitions, `inputPre`, `inputCmd` and `inputPost`, in namespace
`Whiel.Benchmark.<ID>` (file `Benchmark/<ID>/Input.lean`).

**Validity** — [Benchmark/Example0001/Certificate/Valid.lean](Benchmark/Example0001/Certificate/Valid.lean):

```lean
theorem input_hoare_triple_valid :
    HoareValid inputPre inputCmd inputPost :=
  Preproc.certifyProgramInput_of_clauseProofs
    inputPreproc candidateLevels
    (.cons ⟨initValid0, maintValid0⟩ <|
      .cons ⟨initValid1, maintValid1⟩ <|
      .nil)
    termValid
```

Its full name is
`Whiel.Benchmark.Example0001.Certificate.input_hoare_triple_valid`. Under
`open Whiel` inside that namespace, `HoareValid`, `inputPre`, `inputCmd` and
`inputPost` resolve to `Whiel.HoareValid` and
`Whiel.Benchmark.Example0001.{inputPre,inputCmd,inputPost}`, the
definitions in [Benchmark/Example0001/Input.lean](Benchmark/Example0001/Input.lean).
Section 5 shows how to check this correspondence against a statement
written with fully qualified names.

**Invalidity** — [Benchmark/Example0013/Certificate/Invalid.lean](Benchmark/Example0013/Certificate/Invalid.lean):

```lean
def counterExampleInput : Instance Data inputSchema :=
  programInst![inputSchema |
    E := [[0, 1], [1, 2]];
    S := [];
    T := [] ]

def counterExampleFuel : Nat := 6

theorem input_hoare_triple_invalid :
    ¬ Whiel.HoareValid inputPre inputCmd inputPost :=
  Whiel.Hoare.CounterExample.certifyKernel
    counterExampleFuel counterExampleInput
```

Its full name is
`Whiel.Benchmark.Example0013.Certificate.input_hoare_triple_invalid`.
The theorem concerns `Whiel.Benchmark.Example0013.{inputPre,inputCmd,inputPost}`
from [Benchmark/Example0013/Input.lean](Benchmark/Example0013/Input.lean).
Example0013 has the same schema, precondition and command as Example0001,
with the postcondition changed to `T ⊆ E`, so the pair isolates what the
two kinds of certificate say.

**Expected axioms.** Both endpoint files contain a `#guard_msgs` check of
`#print axioms`, expecting exactly
`[propext, Classical.choice, Quot.sound]`. These are propositional
extensionality, classical choice and quotient soundness. A certificate
with an additional axiom, including `sorryAx` or a native-evaluation trust
axiom, does not meet this audit criterion. The printed axiom set is
transitive: it includes assumptions used by the endpoint's proof dependencies.

**Partial correctness.** `Whiel.HoareValid pre C post` (in
[Whiel/Hoare/Abstract.lean](Whiel/Hoare/Abstract.lean)) is

```lean
∀ I J : Instance D Γ, toAssertion pre I → Cmd.BigStep C I J → toAssertion post J
```

- A validity certificate says that every *terminating* run from a database
  satisfying the precondition ends in a database satisfying the
  postcondition. It says nothing about runs that do not terminate, and it
  does not prove termination.
- An invalidity certificate proves the negation. Its proof
  (`invalid_of_kernelRefutes`) exhibits one concrete initial instance that
  satisfies the precondition and one terminating run of `inputCmd` from it
  (found by fuelled evaluation) whose final instance violates the
  postcondition.

**The claim is about the original triple.** Neither endpoint states
anything about a preprocessed loop, a prophecy-extended schema or a solver
problem; those appear only inside the proof. The validity proof takes
`inputPreproc` (defined in `Input.lean` as
`Hoare.preprocess inputPre inputCmd inputPost`) as an argument. That value
is a structure `Whiel.Hoare.Preproc` whose field
`valid_of_loop : HoareValid loopPre (.while loopGuard loopBody) loopPost →
HoareValid inputPre inputCmd inputPost` is a proved implication, supplied
by `Whiel.Preprocess.preprocess_transfer`. So the reader need not trust
preprocessing to read the theorem: whatever it does, the kernel checks the
step back to the original triple. The invalidity proof does not use
preprocessing at all.

## 2. Reading guide to the statement's meaning

Read these entry points in order to interpret the endpoint. Follow the
small data definitions in items 5–7 whenever they occur in items 2–4.
The proof-construction machinery in section 3 is separate: none of
Whiel's synthesis internals is needed to interpret the final statement.

1. **The input.** [Benchmark/Example0001/Input.lean](Benchmark/Example0001/Input.lean):
   `inputSchema`, `inputPre`, `inputCmd`, `inputPost`. Its comments describe
   the intended problem but are not part of the formal object. The file
   ends with `#eval inputPreproc.display`, which prints the triple as
   parsed. That output is a pretty-printer's rendering, useful for a quick
   reading but not a substitute for the definitions below.
2. **Hoare validity.** `Whiel.HoareValid` in
   [Whiel/Hoare/Abstract.lean](Whiel/Hoare/Abstract.lean), and the
   instance `Whiel.AssertExpr.instToAssertion` in
   [Whiel/Hoare/Concrete.lean](Whiel/Hoare/Concrete.lean), which interprets
   a syntactic assertion as `fun I => φ.eval I`. In Abstract.lean,
   `Whiel.Assertion` is a predicate on instances; `Whiel.ToAssertion` and
   `Whiel.toAssertion` supply the interpretation used by `HoareValid`.
   (Do not confuse it with
   `Whiel.Program.HoareValid` in `Whiel/Preprocess/Transfer.lean`, a
   different notion used inside preprocessing proofs.)
3. **Commands.** `Whiel.Cmd` in [Whiel/Cmd/Syntax.lean](Whiel/Cmd/Syntax.lean)
   (skip, assignment of an RA expression to a schema relation, sequence,
   if-then-else, while) and `Whiel.Cmd.BigStep` in
   [Whiel/Cmd/Semantics.lean](Whiel/Cmd/Semantics.lean): a relational
   big-step semantics. Assignment replaces one relation by the value of its
   RA expression (`Instance.update` in
   [Databases/UnnamedModel/Instance.lean](Databases/UnnamedModel/Instance.lean)).
   Termination of a run is the existence of a `BigStep` derivation.
4. **Assertions and guards.** `Whiel.Guard` in
   [Whiel/Guard/Syntax.lean](Whiel/Guard/Syntax.lean) and `Whiel.Guard.eval`
   in [Whiel/Guard/Semantics.lean](Whiel/Guard/Semantics.lean): true, false,
   equality and containment of two same-arity RA expressions, and the
   Boolean connectives. A loop condition such as `S ≠ T` is the negation of
   an equality guard. `Whiel.AssertExpr` in
   [Whiel/AssertExpr/Syntax.lean](Whiel/AssertExpr/Syntax.lean) and
   `Whiel.AssertExpr.eval` in
   [Whiel/AssertExpr/Semantics.lean](Whiel/AssertExpr/Semantics.lean): an
   assertion is a guard over a possibly larger schema, read with the extra
   relations *existentially quantified* (existential second-order, over
   finite relations). `Whiel.QFAssertExpr` is an alias for `Whiel.Guard`;
   `AssertExpr.fullSchema` and `extendsFree` specify the extra symbols.
   `UnnamedSchema.extensionOf` and `Instance.Extends` (in the schema and
   instance files below) ensure the extension agrees on the original
   relations. The benchmark preprocessing entry point `Whiel.Hoare.preprocess`
   in [Whiel/Hoare/ProphecySchema.lean](Whiel/Hoare/ProphecySchema.lean)
   requires `Whiel.AssertExpr.NoBoundSymbols` of both input assertions: no
   existentially bound relation symbols in the precondition or postcondition.
5. **Databases.** `UnnamedSchema` in
   [Databases/Core/UnnamedSchema.lean](Databases/Core/UnnamedSchema.lean) (a finite
   set of relation names with arities), `Instance` in
   [Databases/UnnamedModel/Instance.lean](Databases/UnnamedModel/Instance.lean)
   (each name maps to a `FinRelation`), and `FinRelation`/`Tuple` in
   [Databases/Core/FinRelation.lean](Databases/Core/FinRelation.lean): a relation
   is a `Finset` of fixed-length vectors.
6. **Relational algebra.** `RawRAExpr` and the well-typed `RAExpr` in
   [Databases/UnnamedRA/Syntax.lean](Databases/UnnamedRA/Syntax.lean);
   `RawRAExpr.eval?`, `RAExpr.eval` and the operators `FinRelation.select`,
   `proj`, `prod`, `union`, `diff`, together with `Sel.Holds`, in
   [Databases/UnnamedRA/Semantics.lean](Databases/UnnamedRA/Semantics.lean). The
   membership lemmas `mem_select_iff`, `mem_proj_iff`, `mem_prod_iff`,
   `mem_union_iff` and `mem_diff_iff` state the operators' meaning directly.
7. **Values and names.** `Whiel.Concrete.Data` and its `Domain` instance in
   [Whiel/Concrete/Data.lean](Whiel/Concrete/Data.lean); the `Domain` class
   in [Databases/Core/Basic.lean](Databases/Core/Basic.lean);
   `Whiel.Concrete.ProgramNames` in
   [Whiel/Concrete/WhielNames.lean](Whiel/Concrete/WhielNames.lean).
8. **Surface notation** (read as needed). `programSch!`, `programAssert!`
   and `programCmd!` are macros in
   [Whiel/Concrete/Notation.lean](Whiel/Concrete/Notation.lean). A reader
   should also consult [Databases/Core/Notation.lean](Databases/Core/Notation.lean)
   for relation and schema literals. That file intentionally retains the
   declaration namespace `DBLib.Notation`; the library files are under
   `Databases/`. Inspect the elaborated terms, for example with
   `#print Whiel.Benchmark.Example0001.inputCmd`, to check what the notation
   produced rather than relying on the macros or pretty-printer.

**Interpretation assumptions these definitions fix:**

- **Finite databases, infinite domain.** Every relation of every instance,
  including the existentially quantified relations of an assertion, is a
  finite set of tuples. Values range over `Data`: natural numbers, strings
  and Booleans, an infinite type.
- **Set semantics.** Relations are `Finset`s: no duplicates and no bag
  multiplicities. Equality and containment are equality and inclusion of
  sets.
- **Positional, 0-based columns.** There are no attribute names. `#i` and
  projection indices are positions starting at 0, and a product concatenates
  tuples, so on two binary relations `π[0, 3] (σ[#1 = #2] (E × T))` is
  relational composition. `RawRAExpr.arity?` checks column bounds and
  operator arities; a typed `RAExpr` carries a proof of well-formedness.
- **The whole schema is the state.** `HoareValid` quantifies over every
  initial instance of the *full* input schema, working relations included.
  With precondition `true`, the initial contents of `T` and `S` in
  Example0001 are arbitrary. The command resets them, and a reader should
  check that every input does likewise wherever the intended problem
  assumes it.
- **Datalog is out of scope.** The formal object is the RA command, not a
  Datalog program. The correspondence to a stated Datalog program is
  described in comments and in `Metadata.json`; these are not proofs of
  correspondence. An external-language encoding requires its own fidelity
  argument or theorem. A file named `Fidelity` establishes only the
  particular correspondence stated by its theorems.

## 3. How the proof reaches the statement (optional)

### Validity (Example0001)

Read [Input.lean](Benchmark/Example0001/Input.lean) first. The schema has
three binary relations, `E`, `T` and `S`, and the precondition is `true`.
The command resets `T` to the empty relation and `S` to
`E ∪ (E ∘ T)`, then repeats `T := S; S := E ∪ (E ∘ T)` until `S = T`.
Here `∘` abbreviates the selection-and-projection expression in the input.
The postcondition is `T ∘ T ⊆ T`: the final `T` is transitive. The endpoint
proves this for every terminating run and every initial database. Its
statement does not claim termination or characterize `T` as the least
transitive closure.

Follow the proof from the proposed clauses to that endpoint:

- **Proposed invariant.**
  [Benchmark/Example0001/Certificate/Proposal.lean](Benchmark/Example0001/Certificate/Proposal.lean)
  defines `candidateClause0`, `candidateClause1` over the prophecy schema
  of `Preproc.loop inputPreproc`. It is data, not an assumption: a wrong
  proposal would make an obligation unprovable.
- **Obligations.**
  [Benchmark/Example0001/Certificate/Jobs.lean](Benchmark/Example0001/Certificate/Jobs.lean)
  defines `candidateLevels` and the jobs `initJob0`, `initJob1`,
  `maintJob0`, `maintJob1` and `termJob` (initiation, maintenance and the
  loop-exit postcondition check).
- **Checked obligation proofs.** Each
  `Benchmark/Example0001/Certificate/Reconstructions/*.lean` proves one
  job's entailment, for example `initValid0 : initJob0.entailment.Valid`:
  - It uses `CertificateJob.valid_of_fullProof` from
    [Whiel/Synthesis/FrameworkII/FixedAmbient/CertificateJobs.lean](Whiel/Synthesis/FrameworkII/FixedAmbient/CertificateJobs.lean).
  - Its inputs are a `decide`d empty-instance check (`initNoEmpty0` in
    [EmptyCexCheck.lean](Benchmark/Example0001/Certificate/EmptyCexCheck.lean))
    and a proof of the job's first-order
    `ShallowTarget` (`initShallow0`).
  - That proof is built by the `certify_job` tactic
    ([Whiel/Synthesis/FrameworkII/FixedAmbient/CertifyJob.lean](Whiel/Synthesis/FrameworkII/FixedAmbient/CertifyJob.lean))
    from the Vampire-emitted Lean proof in
    [VampireProofJobs/InitClause0.lean](Benchmark/Example0001/Certificate/VampireProofJobs/InitClause0.lean)
    (`Whiel.Benchmark.Example0001.Certificate.VampireProofs.InitClause0.fullProof`).
  - That file consists of ordinary Lean theorem steps. Its SAT steps are
    Mathlib's `lrat_proof`, which checks the LRAT certificate in the Lean
    kernel.
- **Soundness of the invariant method.**
  `Whiel.Synthesis.FrameworkII.FixedAmbient.Preproc.certifyProgramInput_of_clauseProofs`
  (CertificateJobs.lean) calls `Preproc.certifyProgramInput` in
  [Whiel/Synthesis/FrameworkII/FixedAmbient/Assembly.lean](Whiel/Synthesis/FrameworkII/FixedAmbient/Assembly.lean).
  That theorem combines `LoopTriple.valid_of_valid_vcs` (valid verification
  conditions give a valid preprocessed loop, including the prophecy-schema
  lift) with `Whiel.Hoare.LoopTriple.valid_input_of_ofPreproc`
  ([Whiel/Hoare/ProphecySchema.lean](Whiel/Hoare/ProphecySchema.lean)).
- **Transfer to the original triple.** `valid_input_of_ofPreproc` uses
  `Hoare.Preproc.valid_input` ([Whiel/Hoare/Preproc.lean](Whiel/Hoare/Preproc.lean)),
  which applies the `valid_of_loop` field. For `Hoare.preprocess`
  (which calls `Whiel.Hoare.ofPreprocessed`), that field is
  `Whiel.Preprocess.preprocess_transfer`
  ([Whiel/Preprocess/Transfer.lean](Whiel/Preprocess/Transfer.lean)). This
  is where preprocessing correctness enters, as a checked lemma rather than
  an assumption.

### Invalidity (Example0013)

Read [Input.lean](Benchmark/Example0013/Input.lean) alongside the valid
example. Only the postcondition differs: it asks for `T ⊆ E`. The
certificate chooses `E = {(0,1), (1,2)}` and empty `S` and `T`. The command
adds the composed edge `(0,2)` to `T` and halts with `S = T`; `(0,2)` is
absent from `E`. Thus the precondition holds but the postcondition fails.
The recorded fuel bound is 6.

- **Evidence.** `counterExampleInput`, a concrete instance built with
  `programInst!` ([Whiel/Eval/CounterExample/InstanceNotation.lean](Whiel/Eval/CounterExample/InstanceNotation.lean)),
  and `counterExampleFuel`. The final instance is not written down; the
  kernel computes it.
- **Checking.** `Whiel.Hoare.CounterExample.certifyKernel`, with
  `kernelRefutes` and `invalid_of_kernelRefutes`, all in
  [Whiel/Eval/CounterExample/Kernel.lean](Whiel/Eval/CounterExample/Kernel.lean):
  - `kernelRefutes` is a Boolean function. It requires both assertions to
    be quantifier-free, evaluates the precondition, runs the command using
    `Whiel.CmdFuel.eval` with the recorded fuel bound, and checks that the
    postcondition is false on the halting state. Fuel bounds recursive
    evaluation depth, not the number of execution steps; it is absent from
    the final `HoareValid` statement. Exhausting fuel does not prove invalidity.
  - `certifyKernel` discharges `kernelRefutes … = true` with
    `decide +kernel`, which is kernel reduction, not compiled code.
- **Conclusion.** `invalid_of_kernelRefutes` turns that into
  `¬ HoareValid`, using `CmdFuel.eval_sound`
  ([Whiel/Eval/Cmd/Fuel.lean](Whiel/Eval/Cmd/Fuel.lean)): a halted fuelled
  run is a `Cmd.BigStep` run. It also uses `AssertExpr.toQF_eval_iff` for
  the assertions.
- **The JSON record is not evidence.**
  [Benchmark/Example0013/Counterexample.json](Benchmark/Example0013/Counterexample.json)
  is the record the certificate was generated from. The certificate
  restates the instance in Lean, and only the Lean term is checked.

## 4. What must be trusted

**Logical checking.** Use the Lean kernel from the toolchain named by
`lean-toolchain` (`leanprover/lean4:v4.30.0-rc1`), with the dependencies
pinned by `lake-manifest.json`. The conclusion relies on the kernel's
checking of the exact endpoint and the accepted axioms `propext`,
`Classical.choice` and `Quot.sound`, in a correctly functioning checking
environment. Imported compiled declarations must correspond to the
sources being audited. Start from a clean checkout and build the pinned
dependencies when that correspondence is in doubt. A toolchain pin
identifies the implementation; it is not a proof of that implementation's
correctness.

**Semantic fidelity.** The kernel checks a formal statement, so the reader
must also judge:

- whether the command, assertion, database and Hoare-validity definitions
  in section 2 express the intended semantics;
- whether each benchmark's `inputSchema`, `inputPre`, `inputCmd` and
  `inputPost` encode the intended problem, including its assumptions.

Macros, comments, metadata and displayed triples can help with reading,
but checking their intended meaning requires inspecting the elaborated
definitions. A proof of the wrong formalization is still a proof of the
wrong formalization.

**What need not be trusted for the mathematical conclusion.** Once the
exact endpoint is kernel-checked with the permitted axioms, no correctness
assumption about the following is needed:

- the search procedure or its reported result;
- the Rust controller;
- the LLM proposer or its proposed invariant or counterexample;
- Vampire or its proof output;
- VampLean's proof reconstruction tactics;
- the proof transformations, preprocessing implementation or certificate
  generator.

These components produce candidates or proof terms. Their errors cannot
justify a false endpoint under the accepted axioms: the kernel must still
check a proof of that endpoint. In particular, VampLean and the Whiel
soundness libraries supply definitions and checked lemmas, not an
additional oracle. The axiom check covers their contribution to the final
proof. The transfer from a preprocessed obligation to the original triple
is itself proved, as shown in section 3. Statement checking is essential:
a proof of a different triple does not certify the intended input.

**Operational records are not proofs.** Search acceptance, a JSON receipt,
a placement entry or a report row does not replace the endpoint check.
[Benchmark/CertificatePlacement.json](Benchmark/CertificatePlacement.json)
records placement results and a digest of each case's `Certificate/`
files. It does not hash `Input.lean` or the entire dependency closure.
`scripts/place_certificates.py --check` checks the ledger against the
certificate files; it does not run Lean. The explicit aggregate builds in
section 5 check the proof modules selected by that ledger. The benchmark
report ([Benchmark/report/build_report.py](Benchmark/report/build_report.py))
derives certification status from recognized certificate sources, so its
status labels should be read alongside those kernel checks.

Certification establishes neither search completeness nor termination,
performance measurements, or fidelity of a SQL, Datalog or other external
encoding without a separate argument for that encoding.

## 5. Checking a certificate yourself

Run the following from the repository root after the pinned-environment
setup in [README.md](README.md). These commands check shipped proof files;
they do not run LLM search or ask Vampire for a new proof.

Use the repository's memory watchdogs and avoid overlapping Lean jobs.
[scripts/lake_build_watched.sh](scripts/lake_build_watched.sh) samples the
RSS of every `lean` process on the machine separately;
[scripts/watchdog.sh](scripts/watchdog.sh) samples the combined RSS of its
command and descendants. Both sample every two seconds, so they are
sampled guards, not instantaneous operating-system limits. Limits below
are in KiB: `4194304` is 4 GiB and `12582912` is 12 GiB.

### Build the prerequisites and two example certificates

```sh
LEAN_NUM_THREADS=1 scripts/lake_build_watched.sh
LEAN_NUM_THREADS=1 scripts/lake_build_watched.sh \
  VampLean Mathlib.Tactic.Linter.UnusedTactic Mathlib.Tactic.Sat.FromLRAT \
  Whiel.Vampire.ClauseProjection Whiel.Vampire.EmptyDomainLRAT \
  Whiel.Synthesis.FrameworkII.FixedAmbient.CertifyJob
LEAN_NUM_THREADS=1 scripts/lake_build_watched.sh \
  Benchmark.Example0001.Certificate.Valid \
  Benchmark.Example0013.Certificate.Invalid
```

The default build covers `Databases` and `Whiel`, not every benchmark
certificate. Lake builds are incremental and may reuse compiled modules;
a successful cached build is not a fresh elaboration of every proof source.

### Check each endpoint from source

```sh
LEAN_NUM_THREADS=1 scripts/watchdog.sh 4194304 lake env lean \
  Benchmark/Example0001/Certificate/Valid.lean
LEAN_NUM_THREADS=1 scripts/watchdog.sh 4194304 lake env lean \
  Benchmark/Example0013/Certificate/Invalid.lean
```

These commands elaborate the named files from source, using the compiled
imports prepared above. Each endpoint file embeds a `#guard_msgs` check of
its `#print axioms` output. For these files, a silent run with exit status 0
means the source and its axiom guard passed. This does not re-elaborate all
imported dependencies.

### Check the exact statement and inspect its axioms

Create a scratch file named `AuditCertificate.lean` at the repository root:

```lean
import Benchmark.Example0001.Certificate.Valid
import Benchmark.Example0013.Certificate.Invalid

example : Whiel.HoareValid
    Whiel.Benchmark.Example0001.inputPre
    Whiel.Benchmark.Example0001.inputCmd
    Whiel.Benchmark.Example0001.inputPost :=
  Whiel.Benchmark.Example0001.Certificate.input_hoare_triple_valid

example : ¬ Whiel.HoareValid
    Whiel.Benchmark.Example0013.inputPre
    Whiel.Benchmark.Example0013.inputCmd
    Whiel.Benchmark.Example0013.inputPost :=
  Whiel.Benchmark.Example0013.Certificate.input_hoare_triple_invalid

#print axioms Whiel.Benchmark.Example0001.Certificate.input_hoare_triple_valid
#print axioms Whiel.Benchmark.Example0013.Certificate.input_hoare_triple_invalid
```

Then run:

```sh
LEAN_NUM_THREADS=1 scripts/watchdog.sh 4194304 lake env lean AuditCertificate.lean
```

The two `example` declarations require the exact original triples. Expect
each `#print axioms` result to list only
`[propext, Classical.choice, Quot.sound]`. Unlike the endpoint files'
embedded guards, bare `#print axioms` displays information without rejecting
an unexpected axiom: inspect the output. To examine the parsed input, add
`#print Whiel.Benchmark.Example0001.inputSchema`, `inputPre`, `inputCmd` or
`inputPost`, using the same fully qualified prefix for each declaration.
Remove the scratch file when finished.

### Check the shipped certificate collection

```sh
python3 scripts/place_certificates.py --check
python3 scripts/generate_fixed_ambient_registry.py --check
LIMIT_KB=4194304 LEAN_NUM_THREADS=1 \
  scripts/lake_build_watched.sh Benchmark.Certificates
LIMIT_KB=12582912 LEAN_NUM_THREADS=1 \
  scripts/lake_build_watched.sh Benchmark.OutsideLibrary
```

The first two commands check that the placement ledger and generated
registry are current; they do not replace Lean checking. The targets
[Benchmark/Certificates.lean](Benchmark/Certificates.lean) and
[Benchmark/OutsideLibrary.lean](Benchmark/OutsideLibrary.lean) import the
certificates selected for the normal and larger-memory builds. For a case
listed with `"fits": false` in the placement ledger, use the 12 GiB setting
for its target. To check such an endpoint from source, use
`LEAN_NUM_THREADS=1 scripts/watchdog.sh 12582912 lake env lean` followed by
its certificate file. As with the two worked examples, aggregate builds
can reuse compiled dependencies and certificates.

## 6. Limits of a source audit

The paths, declarations and command interfaces in this guide can be
checked against the repository source. Source inspection alone does not
establish that the commands have completed successfully in a particular
checkout, that compiled imports match their sources, or that each input
faithfully models the intended external problem. Establish the first two
by checking in the pinned environment with appropriately rebuilt imports;
review the definitions and encoding for the third. A certificate cannot
remove these checks of its statement and checking environment.
