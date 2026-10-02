# Whiel benchmark corpus

This folder is self-contained. Everything that describes a case lives in its
directory, and the reading view of the corpus, `Benchmark/report/`, is rebuilt
from this folder alone.

## Layout

- `ExampleNNNN/Input.lean`: the case. A Hoare triple over one program-name
  schema, written with `programSch!` / `programAssert!` / `programCmd!` in the
  namespace `Whiel.Benchmark.ExampleNNNN`. It holds exactly five
  declarations, `inputSchema`, `inputPre`, `inputCmd`, `inputPost` and
  `inputPreproc := Hoare.preprocess …`, and ends with
  `#eval inputPreproc.display`, which prints the stated triple and the
  loop-only triple preprocessing produces. The header comment describes the
  problem: the Datalog programs in rule notation, what they stand for, the
  pre- and postcondition in words, and the expected verdict.
- `ExampleNNNN/Metadata.json`: title, the description fields the report
  prints (`family`, `kind`, `claim`, `sides`, `sources`, `expectedVerdict`
  and so on), and `datalog`, the source Datalog programs as text. Three optional
  keys, placed directly after `title`, are a plain-English reading of the case:
  `explanation` (what the Datalog program(s) compute, what real concept that is,
  and what the triple as a whole claims), `preInWords` and `postInWords` (one or
  two sentences each on what the precondition/postcondition say). The report
  prints them when present and nothing when absent; the RA assertion in
  `Input.lean` remains the authority, never these keys. The only key the tooling
  requires is `canonicalId`, equal to the directory name.
- `ExampleNNNN/Counterexample.json` and `Certificate/Invalid.lean`: a frozen
  counterexample record and the invalidity certificate the emitter wrote from
  it. `ExampleNNNN/Core.json` and `Certificate/Valid.lean` with its proof
  jobs: the frozen Core, written by every valid certification beside the tree,
  and the validity certificate built from it. Each record alone regenerates
  its certificate with `whiel-symbolic certificate build`. Certificates are
  emitter output only; a hand-written certificate is never checked in.
- `ExampleNNNN/Fidelity/ExampleNNNN.lean`, where present: a kernel-checked
  proof that the compiled parts of `inputCmd` are exactly the output of the
  repository's naive Datalog compiler on the stated programs. A hand-written
  side of a case is restated, not proved. `Fidelity/Support.lean` holds the
  shared helpers.
- `report/`: the report generator, its curation files (`tags.json`,
  `curated.json`), the two curation review records, and the generated report.
  `report/ra_to_fol.py` translates each case's `inputPre`/`inputPost` to a
  first-order-logic reading, printed under the label "First-order reading of
  PRE/POST, translated mechanically from the relational-algebra assertion in
  Input.lean"; the relational-algebra text is still the authority, and a
  construct the translator cannot handle fails the build rather than being
  skipped.
- `Inputs.lean` (every input), `Certificates.lean` (every certificate that
  fits the watched build), `OutsideLibrary.lean` (the certificates that do
  not), `Fidelity.lean` (every fidelity proof) and
  `CertificatePlacement.json` are generated; `Benchmark.lean` is the library
  root and imports the inputs only, so inputs and certificates build
  separately.
- An input has a fixed shape, which the generator enforces: the contributor
  header, imports, the three
  namespace lines, `open Concrete`, the five declarations, elaboration options
  and the display line. Nothing else may appear at the top level, so nothing
  outside the five declarations can change what they mean.

A relation's `Core.json` clause source (`op_zE`, `oa_zS`, `yp_zT`, `of_z3`) is
also the name the solver sees: one total, injective naming scheme covers both
live search and every certificate, so a certificate carries no symbol name of
its own to go stale. `docs/lean-runtime-api.md` ("The name-binding contract")
states the convention and its proofs; this is the only place that does.

## Status of a case

A case is *certified valid* when it has an emitter-written
`Certificate/Valid.lean` and *certified invalid* when it has an emitter-written
`Certificate/Invalid.lean`. A case that carries a record but not yet the
certificate built from it is *solved valid, not yet certified* when it has a
`Core.json` and no `Certificate/Valid.lean`, and *solved invalid, not yet
certified* when it has a `Counterexample.json` and no
`Certificate/Invalid.lean`. A case with neither a record nor a certificate is
*open*.

All five states are read off the tree and off nothing else. A solved state says
that the answer is known and its record is frozen, never that anything has been
kernel-checked: only a certificate says that, and only the emitter writes one.
An expected verdict in the metadata is an expectation, never a status.

## Adding, editing or removing a case

1. Create or edit `ExampleNNNN/Input.lean` and `ExampleNNNN/Metadata.json`.
2. Regenerate the registry, the library roots, the per-case axiom audit and
   the per-case notation round trip, then rebuild the worker so the verifier
   serves the case:

   ```bash
   python3 scripts/generate_fixed_ambient_registry.py
   python3 scripts/generate_fixed_ambient_registry.py --check
   LEAN_NUM_THREADS=2 scripts/lake_build_watched.sh Benchmark fixed_ambient_encoding_worker \
     Whiel.Synthesis.Tests.BenchmarkNotationRoundTripCases
   ```

3. Rebuild the report:

   ```bash
   python3 Benchmark/report/build_report.py
   ```

A new case appears in the report with its automatic tags and no other edit.
Curated tags, a category and source links are added in `report/curated.json`
when wanted.

The identity of a task is a digest of its five declarations. Comments, the
contributor header, imports and whitespace are outside it, so prose can be edited
freely; changing a declaration gives the case a new identity, and records
frozen for the old one (`Core.json`, `Counterexample.json`) must be rebuilt
with `whiel-symbolic certificate build`.

An invalid case is contributed as a counterexample instance. The command
`whiel-symbolic certificate build --input ExampleNNNN --destination
Benchmark/ExampleNNNN/Certificate --witness WITNESS.json` validates the
instance in Lean, freezes `Counterexample.json` and writes the certificate.

Certificates are placed automatically. `python3 scripts/place_certificates.py`
elaborates each new or re-emitted certificate from source, measures the peak
memory of its `lean` process and records the result in
`CertificatePlacement.json`. A certificate whose peak exceeds the watched
build's 4 GB limit is listed in `OutsideLibrary.lean` instead of
`Certificates.lean`, and the report marks the case with its peak; once a
re-emitted certificate fits, the next run moves it back without any manual
edit. A certificate that fails to check is an error, never a placement. The
registry generator refuses a ledger that is not current, so placement comes
first.

```bash
python3 scripts/place_certificates.py
python3 scripts/generate_fixed_ambient_registry.py
LEAN_NUM_THREADS=2 scripts/lake_build_watched.sh Benchmark.Certificates
LIMIT_KB=12582912 LEAN_NUM_THREADS=1 scripts/lake_build_watched.sh Benchmark.OutsideLibrary
```

The 12 GB matches the placement script's own hard cap (`--hard-limit-kb`), so a
certificate that passes placement cannot fail this gate.

The fidelity proofs build as their own target:

```bash
LEAN_NUM_THREADS=2 scripts/lake_build_watched.sh Benchmark.Fidelity
```

A proposer reads a printed program, so the printer and the parser must agree
on every case. The generator writes two round-trip modules per input. The
source triple (schema, precondition, command, postcondition) is part of the
test root. The preprocessed loop over the prophecy schema, which is what
invariants are written against, costs up to a few minutes per input and builds
as its own target; run it after adding or changing a declaration:

```bash
LEAN_NUM_THREADS=2 scripts/lake_build_watched.sh Whiel.Synthesis.Tests.BenchmarkPreprocRoundTripCases
```

A failure of either is a printer or parser defect to report, never something
to work around in the test.

## Contributors

The first line of every input is its contributor header:

```
-- Benchmark contributors: Fangzhu Shen, Leo Zhang
```

A case credits whoever originated it and whoever wrote its current encoding.
Names appear in a fixed order: students first, alphabetically by last name
(Jesse Comer, Fangzhu Shen, Leo Zhang), then advisors, alphabetically by last
name (Mayur Naik, Sudeepa Roy, Val Tannen). The header carries names only: no
dates, labels or remarks. The registry generator refuses an input whose header
is missing, names someone outside this list, or is out of order; a new
contributor is added to the list in the generator and here.

Whose idea a problem was (a system, a paper, a benchmark suite, a task
document) is a different matter from who contributed the case: it is recorded
in the case's `sources` and printed in the report. The verification tasks come
from Val Tannen's `reports/VerificationTasks.pdf`, section 10.1. Lean files
that are not inputs (the fidelity proofs and their support module) carry the
repository's usual `-- Author:` line. The `Input.lean` format and the
certificate format are due to Jesse Comer.
