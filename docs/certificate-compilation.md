# Certificate compilation diagnostics

The certifier can compile its generated modules through Lake's ordinary
dependency scheduler. This is post-search work; search behavior and pinned
solver contracts remain unchanged.

`WHIEL_CERTIFICATE_COMPILER=lake` selects Lake; `sequential` (the default)
selects the existing serial compiler. `LEAN_NUM_THREADS` controls Lake's
parallelism. Lake builds a private package containing only the certificate;
dependencies are the existing compiled libraries, with old copies of the
certificate namespace hidden. Its artifact caches are disabled. Every staged
certificate module is built, including modules not imported by the final one.

Proof transformations run before compilation. The LocalPrenex version 2
recognizer declines the known unsupported ancestor-XOR lineage before
compilation. Lake compilation is followed by the final exact-theorem/std3
check. Missing candidate proofs can enter targeted serial
repair using the existing fallback candidates. Repairs compile in a separate
private overlay. Lake then rebuilds their selected sources and dependents with
`--rehash`; only that complete successful Lake build can establish acceptance.
Unrelated successful modules can be reused within the attempt. The final
theorem check cannot trigger repair: a forbidden axiom rejects the complete
attempt, including when reached transitively through an imported helper.
There are no per-proof axiom-audit processes. Repair is reported on stderr and remains
inside the diagnostic's original deadline.
Candidate zero is retried during repair: missing output alone cannot establish
that Lake attempted those exact source/dependency bytes. Its current error
result has no reliable structured per-module failure evidence.
Invalidity publication retains its existing second fresh revalidation build.

Lake receipts leave per-module compilation durations empty; they do not
mislabel aggregate time as a module duration. Existing serial receipts retain
their module timers. Use the externally measured whole-command time below.
Structured stderr events record emission, Vampire, transformation, SAT,
packaging, compilation, candidate attempts and final checks, including failed
or cancelled phases. The harness records a phase without a finish as
`incomplete`, with no invented duration. `lake_launches` counts managed Lake
launch attempts, including failure to spawn or cancellation at invocation
entry; `lake_completions` counts successful exits. The historical `lake_builds`
field counted successful completions only and old results are unchanged.
Nested phases overlap (SAT is inside transformation, and serial compilation
inside candidate selection), so their durations must not be summed as total
time. Bootstrap and final cleanup
remain included in the externally measured whole-command duration.

## Solver and compiler concurrency

`WHIEL_CERTIFICATE_SOLVER_JOBS` sets a positive number of inner certificate
jobs. When absent, the caller's existing bound applies (one for builds from
saved records). One permit covers a job's sequential solver, transformation,
empty-domain SAT solving and packaging work. Results retain the emitted job
order. This setting does not change search concurrency or the Lean worker pool.
Saved-record bootstrap still uses one preparation/package worker and one CPU
admission slot.

`campaign certify --jobs` controls outer input concurrency. Outer jobs greater
than one together with inner jobs greater than one are rejected before worker
launch. `LEAN_NUM_THREADS` separately controls Lake/Lean concurrency. Solving
and packaging finish before compilation begins; there is no streaming overlap.

Successful trees retain `certificate-build-settings.json`, recording resolved
solver jobs (zero for invalidity), the existing CPU admission bound, compiler,
and inherited Lean thread setting. This sidecar and the settings log are
diagnostic provenance, never proof evidence. The existing CLI receipt schema
is unchanged. The harness copies and checks these settings in `result.json`.

CaDiCaL runs asynchronously within each job's permit. Each invocation owns a
fresh directory, CNF and trace; its pinned arguments and environment filtering
match the existing solver contract. Cancellation and the per-job solver limit
kill and join the child, descendants and output readers before returning. The
AVATAR transformation consumes a prepared trace only for the exact step and CNF
that were submitted. UNSAT exit status alone is never certificate evidence:
the existing LRAT validation and final Lean checks remain required.

## Empty-domain proof resources

Certificate bundle version 2 adds a strict `empty_check` record for each
validity job. Lean computes that exact job's DIMACS once, with encoding
version 1. Rust treats the CNF as opaque bytes and runs pinned CaDiCaL inside
the same bounded job permit. Each `EmptyCexCheck/<job-module>.lean` imports
only its own resources and proves the unchanged Boolean empty-counterexample
statement through the checked semantic bridge and kernel LRAT replay. The
emitter no longer enumerates empty-domain assignments or rejects them natively.
A satisfiable CNF fails certification without publishing a tree.

The published tree retains `EmptyCexCheck/Resources/<job-id>.cnf`, its `.lrat`,
and `manifest.json`. These are proof resources, separate from optional
`VampireArtifacts` debugging evidence. The strict manifest binds each job's
module, theorem, encoding version and both byte digests. Revalidation copies
and hashes these resources with the Lean sources, rejects missing, modified,
undeclared or symlinked resources, and rebuilds after moving the tree. Hashes
protect transport consistency; the Lean kernel binds the replayed formula to
the exact obligation. Rewriting a hash cannot authorize another formula.
Legacy certificates containing an aggregate `EmptyCexCheck.lean` remain
revalidatable. Invalidity bundles use version 2 and retain zero proof jobs.
Input, scope, snapshot and job identity versions are unchanged.

## Local runs

Build shared dependencies and the release runner before measuring, using the
repository's watched Lean build commands. No other Lean work should run during
the diagnostic. The runner and worker paths must name this checkout's builds.

```sh
LEAN_NUM_THREADS=2 scripts/lake_build_watched.sh fixed_ambient_encoding_worker \
  VampLean Mathlib.Tactic.Linter.UnusedTactic Mathlib.Tactic.Sat.FromLRAT \
  Whiel.Synthesis.FrameworkII.FixedAmbient.CertifyJob Whiel.Vampire.EmptyDomainLRAT
cargo build --release --manifest-path whiel_runner/Cargo.toml --bin whiel-symbolic
python3 scripts/compare_certificate_builds.py \
  --output artifacts/certifier-comparison/pilot \
  --backends lake --shape valid --limit 180
  # Add --cases Example0001 for a one-case pilot.
```

Omit `--cases` for all answers selected by `--shape` (69 validity answers
with the command above). `--backends lake` skips fresh sequential measurements.
Omitting `--backends` runs sequential then Lake, independently regenerating
from each saved answer into fresh destinations. The output directory must not exist. Cached dependencies are
allowed; cached certificate modules are not. The harness checks a successful
receipt, final source and exact standard axiom set before recording success.

Defaults are `--limit 600` seconds for the entire command, `--memory-kb
12582912` (12 GiB aggregate process-tree RSS), `--solver-jobs 1` and
`--threads 2`. Add `--process-memory-kb 4194304` to enforce the pilot's 4 GiB
limit on each owned process, separately from the aggregate limit. This optional
limit is unbounded when omitted. The harness monitors memory, kills owned
descendants at a limit, and refuses to continue
if cleanup fails. These controls also cover bootstrap, solver work, audits,
candidate repair and invalidity revalidation. Limit outcomes are unsuccessful
attempts, never evidence that a theorem is false. The old 60-second candidate
compilation deadline is disabled for both modes by
`WHIEL_CERTIFICATE_CANDIDATE_TIMEOUT_SECONDS=0`. Outside the harness, that
variable can set a positive serial candidate/repair deadline; if absent, the serial backend
retains 60 seconds and the Lake backend has no per-candidate deadline.

Solver deadlines are distinct: both modes use the same historical profile
and per-job limit (normally direct/60s; portfolio/60s for 5018, 5023 and 5030;
portfolio/120s for 5034 and 5036). These are diagnostic settings, not a change
to experimental records or production search.

`comparison.csv` records per-case outcomes, whole times, speedups for joint
successes when both backends are selected, serial candidate repair and proof
equality. Unselected backends are marked `not_run`, with no claimed speedup. Per-attempt `result.json`,
`receipt.json` when available, and `build.log` preserve the evidence. `run.json`
records binary hashes, revision/diff, toolchain, host and settings. Times
include harness supervision/cleanup overhead. Fixed ordering, independent
solver variation and warm shared dependencies limit causal interpretation;
these runs are optimization diagnostics, not the paper's final experiment.

The current local diagnostics establish complete certification for Examples
0001, 5001 and 0013, plus the binding, resource and revalidation regressions.
They do not establish a speedup across the corpus. Full Example5018 stopped
at the 4 GiB per-process limit during reconstruction, after solver and SAT
production completed; it did not reach the final theorem audit. Its separate
37 empty-domain proofs passed.
