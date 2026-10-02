# Analyst's guide to a campaign run

For a collaborator reading a finished campaign and writing the numbers up. It
assumes no knowledge of the code. Every file named here is JSON unless it says
otherwise, and every path is relative to the run directory it sits in.

A campaign is an **untrusted search** followed by an optional **certification**.
The search consults a proposer (a model, or the token-free replay proposer) and
ends when the verifier accepts a verdict. Certification is deterministic,
consults nothing, and builds a Lean proof from the accepted record. The two are
separate steps and are timed separately.

## 1. The four measures

### Success

One input's verdict is the `status` of `verifier/<ID>/result.json`. Nothing
else — not a certificate file's presence, not a submission the proposer made,
not a log line — is that input's result.

**Counted as solved:**

| `status` | Meaning |
| --- | --- |
| `valid` | The triple holds; the search accepted an inductive Core and a Lean certificate was published and re-checked. |
| `invalid` | The triple fails; the search accepted a counterexample and a Lean certificate was published and re-checked. |
| `valid_uncertified` | The search accepted an inductive Core. Certification has not been run yet (`--certify never` or `deferred`). |
| `invalid_uncertified` | The search accepted a counterexample. Certification has not been run yet. |

The `_uncertified` pair is the normal outcome of a collaborator's campaign,
which stops at acceptance. They count as solved by the search. They are **not**
proofs: only a published, re-checked `Certificate/` tree is.

**Counted as failures:**

| `status` | Meaning |
| --- | --- |
| `search_timeout` | The search reached its `--search-limit` without a verdict. |
| `incomplete` | The search ended without a verdict for some other reason; `failure_kind` says which. |
| `interrupted` | The run was stopped from outside (signal). |
| `resource_exhausted` | A campaign-wide guard (workspace or API traffic) refused further work. |
| `failed` | The input never reached the search loop at all; `detail` says why. |
| `certification_failed` | The search accepted, but the certificate could not be built or did not check. |
| `certification_timeout` | Certification ran out of its own separate allowance. |
| `certification_unchecked` | A certificate tree stands but cannot be revalidated, so it is never read as certified. |
| `input_changed` | The input's declarations changed after the search accepted, so the record no longer applies. |

A `certification_*` or `input_changed` status means the search succeeded and the
deterministic tail did not; say so rather than counting it as a search failure.

**`failure_kind`** is present on every result whose search started and did not
reach a verdict. Its values:

| `failure_kind` | Meaning |
| --- | --- |
| `OverallTimeout` | The whole-input search allowance expired. |
| `Interrupted` | External cancellation. |
| `ConsultationTimeout` | One consultation exceeded its own optional allowance. |
| `IterationLimitExhausted` | The optional `--iteration-limit` on consultations was reached. |
| `SourceExhausted` | The proposer reported it had nothing further to offer. |
| `CorrectionExhausted` | The proposer's proposals kept being correctable and the correction rounds ran out. |
| `NoResponse` | A consultation finished with no submission. |
| `TransportFailure` | The exchange with the proposer failed in transit. |
| `UnsupportedCheck` | A check the verifier cannot express was requested. |
| `FuelExhausted` | Counterexample replay ran out of its fuel allowance. |
| `CheckTimeout`, `SolverUnknown`, `MalformedResult`, `ProcessFailure` | A solver invocation timed out, returned unknown, returned something unreadable, or failed as a process. |
| `ValidationInfrastructureFailure`, `InfrastructureFailure`, `ConcurrentWorkerFailures` | The machinery around the check failed, not the mathematics. |
| `CertificateConstructionFailure`, `CertificateRejected`, `CertificateTypecheckFailure` | Certification built nothing, built something refused, or built something Lean did not accept. |
| `ManifestFailure`, `PublicationFailure`, `HistoryLogFailure` | The run could not record or publish what it had. |
| `StateInvariantViolation` | The verifier detected an inconsistency in its own state and stopped. |

A single **clause check** inside a search can also come back inconclusive.
These appear in the per-clause ledger, not in `status`, and they are the usual
reason a clause stays pending rather than being committed or refuted:

| `reason` | Meaning |
| --- | --- |
| `timed_out` | The solver exceeded this attempt's allowance. |
| `solver_unknown` | The solver returned without deciding. |
| `peer_failed` | The other racing lane failed, so this attempt was stopped. |
| `unvalidated_refutation` | A candidate countermodel was found but did not validate, so it is not a refutation. |
| `cancelled` | The attempt was cancelled (deadline or interruption). |
| `suspended` | The clause was already suspended for the epoch, so no solver ran. |

Only `timed_out`, `solver_unknown` and `unvalidated_refutation` say anything
about the obligation; the other three say only that the attempt did not finish.

**A proof from inconsistent premises reads differently on a retry.** A check
whose premises contradict each other entails its conjecture along with
everything else, and the solver has always accepted that as a proof. While the
premises are written as axioms — which is every first launch — it says so, with
the status `ContradictoryAxioms`, and the launch record keeps that exact word.
A retry writes the same premises as goal-derived, and the same case then comes
back as a plain `Theorem`. Nothing about what the verifier accepts changes, and
the certificate is built and kernel-checked the same way either way; what is
lost is the *signal*. So a clause first proved on a retry cannot be told apart
from an ordinary proof by the status word alone, and an analyst who wants to
know whether a Core's premises are jointly satisfiable should ask that question
directly rather than read it off the launch records.

### Number of epochs

An **epoch** (also called a consultation, or a round) is one complete cycle:
the verifier pushes the current state to the proposer, the proposer submits one
proposal, and the verifier checks it and updates its state. One epoch is one
such push-propose-check cycle.

The count for an input is the number of entries in
`examples/<ID>/rounds.json`'s `rounds` array, which is also its
`consultations` field and the `rounds` column of `progress.md`. Each entry
carries that epoch's `clauses_proposed`, `clauses_dropped`, and the Core and
pending sizes the push showed.

`rounds.json` also carries `agent_seconds` and `verifier_seconds` per epoch.
Those split one epoch between the proposer and the verifier; they are the
harness's estimate from its own log file timestamps, `agent_seconds` includes
the harness's overhead, `verifier_seconds` is the gap to the next epoch and is
null on the last one, and **neither is search time**. Do not sum them.

### Search time

`search_seconds` in `verifier/<ID>/result.json`, in seconds, measured by the
campaign runner on a monotonic clock. It is the only search-time figure.

- It **starts** when the search loop begins: after the proposer process has
  started and completed its handshake, immediately before the task is pushed.
- It **stops** when the search returns its result: after acceptance or failure,
  including the proposer's own shutdown, and before any record is written and
  before any certification begins.

It therefore excludes runner startup, Lean worker startup and build, proposer
startup and handshake, record writing, and certification of every kind. It is
written on every result whose search started, and on none whose search did not,
so an input that failed before the search loop has no `search_seconds` key at
all rather than a zero.

An input that hit its limit is reported as a **timeout**, not as a number. It
still carries a `search_seconds` — the measurement runs whatever the search
then did — but that figure is just where the allowance ran out, and its
`status` is `search_timeout`. Quoting it as a duration would treat a censored
observation as a completed one; report the input as a timeout at its limit and
exclude it from any mean.

Nothing else is search time: not file timestamps, not the harness's own
per-epoch split, not the total elapsed time of the campaign command.

### Certification time

Certification is not yet timed per input in `result.json`. What exists is the
published tree's own `Certificate/timing.csv`, one row per proof job, with the
columns

```
job,profile,vampire_elapsed_s,vampire_peak_mb,transform_s,proof_module_lean_s,reconstruction_lean_s
```

— the job's name, the solver profile it ran under, the solver's wall clock and
peak memory, the proof-transformation pipeline's wall clock, and the two Lean
compilations (the published proof module, and its reconstruction module).

Because certification is a separate later step, run on its own and possibly on
a different machine, its timings are reported separately from search timings
and are not comparable with them.

## 2. What is in a run directory

A harness run directory (`experiment run` writes one; a bare `campaign run`
writes only the `verifier/` part):

| Path | What it is | For analysis? |
| --- | --- | --- |
| `run.json` | The resolved spec, the exact command, the code revision, start/finish, exit code. | Yes — provenance. |
| `progress.md` | One row per input: status, epochs, clauses proposed/dropped, Core/pending/dead, search time. | Yes — the overview. |
| `progress.json` | The same rows, machine-readable. | Yes. |
| `launcher.log` | Everything the command printed. | Debugging. |
| `verifier/campaign-settings.json` | The resolved controls, the input list, the proposer selection. | Yes — comparability. |
| `verifier/resource-limits.json` | The nine workspace and API guard values in force. | Yes — see §5. |
| `verifier/summary.json` | `all_accepted`, `all_certified`, `interrupted`, selected and unrun inputs, and every `result.json` inlined. | Yes. |
| `verifier/<ID>/result.json` | **The input's result**: status, `search_seconds`, `failure_kind`, controls, proposer. | Yes — the authority. |
| `verifier/<ID>/Accepted.json` | The acceptance receipt. | Yes — see §3. |
| `verifier/<ID>/Core.json` or `Counterexample.json` | The accepted answer. | Yes — see §3. |
| `verifier/<ID>/Certificate/` | The published Lean proof and its `timing.csv`, present only once certified. | Yes. |
| `verifier/<ID>/artifacts/` | The artifact store: `manifest.json`, `run-configuration.json` and binary payloads — the clause ledger, the consultation transcripts, the solver witnesses. | Debugging and deep dives. |
| `agent/<ID>/events.jsonl` | The proposer harness's own event log for that input. | Debugging. |
| `agent/<ID>/request-N/` | Per-epoch prompt, provider stream, MCP traffic, submissions. | Debugging. |
| `examples/<ID>/summary.md` | A readable digest of both trees for one input. | Yes — for reading one case. |
| `examples/<ID>/rounds.json` | The per-epoch breakdown. | Yes — see §1. |

The artifact store, the transcripts and the provider streams are diagnostic
material. They are large, they are digest-bound evidence rather than tidy data,
and no paper measure is read from them.

One caution when counting rounds from `agent/<ID>/request-N/submissions.jsonl`:
a row is one `submit` call, not one round. The harness refuses locally what it
can decide from the push alone — a payload that is not JSON, a binding that is
not the one this consultation issued, an unauthorized drop, a formula already
dead, a clause Lean's admission refuses — and such a payload never reaches the
verifier and spends nothing. Those rows read `"forwarded": false` and
`"verdict": "refused_locally"`, with `detail` naming the fault the model was
told. Only `"forwarded": true` rows are rounds.

## 3. Reading the records

### `Core.json` — an accepted inductive invariant

```json
{"kind": "whiel_framework_ii_core_rows", "version": 1,
 "rows": [{"level": 0, "source": "..."}, {"level": 1, "source": "..."}]}
```

Each row is one clause of the invariant with the **level** at which it was
proved inductive. Levels are a stratification: a level-0 clause is inductive on
its own, and a level-`n` clause was proved using the clauses below level `n` as
premises. So the rows are read bottom-up, and the level column is a measure of
how much scaffolding the invariant needed, not of difficulty in time.

**Clause syntax.** A clause is one quantifier-free assertion in relational
algebra. The operators are `∪` union, `∖` difference, `×` product, `⊆`
inclusion, `=` and `≠`, `∧ ∨ ¬`, `σ[#i = #j]` and `σ[#i = c]` selection,
`π[i, j, ...]` projection, `∅[n]` the empty relation of arity `n`, `{d}` a
singleton and `⊤` the top relation. There is no intersection operator. `#n` is
a column reference, counting from 0 across the operand: in `σ[#1 = #2] (X × Y)`
with both binary, `#0 #1` are `X`'s columns and `#2 #3` are `Y`'s. Composition
of two binary relations is therefore written `π[0,3] (σ[#1 = #2] ((X × Y)))`.

**Relation names.** Two prefix letters, an underscore, an index run and the
program's own name:

| Form | Meaning |
| --- | --- |
| `op_z<Name>` | A program relation of the input schema, ordinary copy. |
| `oa_z<Name>` | An auxiliary relation the preprocessing introduced (written `<Name>_aux` in the task text). |
| `of_z<N>` | A phase flag: several loops are preprocessed into one, and the flags tell the phases apart. |
| `yp_z<Name>`, `ya_z<Name>`, `yf_z<N>` | The **prophecy** copy of the same relation: its value when the loop exits, one fixed value, the same at every iteration. Written `<Name>∞` in the task text. |
| `op_s…z<Name>` | An indexed relation; each `s` before the `z` is one index level. |

The first letter is the copy (`o` ordinary, `y` prophecy); the second is the
family (`p` program, `a` auxiliary, `f` flag); `z` closes the index run. A
clause mentioning any prophecy relation has minimum level 1; one mentioning
none has minimum level 0. A clause over both copies relates the running state
to the exit state, which is what lets an invariant shaped like the
postcondition hold at every iteration and still deliver it at exit.

**Constants** are `kn<decimal>` for a natural number, `kbt` and `kbf` for the
two Booleans, and `ks<escaped>` for a text value. The escape keeps lowercase
letters and digits as themselves and writes every other character as `_`
followed by six hexadecimal digits of its code point.

**Worked example — `Example0001`.** The program computes the transitive closure
`T` of an edge relation `E` by naive iteration, with `S` the next-round value;
the postcondition asks that `T` be transitively closed. Its accepted Core:

```
level 0  (op_zS = (op_zE ∪ π[0,3] (σ[#1 = #2] ((op_zE × op_zT)))))
level 1  (π[0,3] (σ[#1 = #2] ((op_zT × yp_zT))) ⊆ yp_zT)
```

The first says: *`S` is exactly `E` together with the composition `E ; T`* —
the loop body's assignment, transcribed. It mentions no prophecy relation, so
it is a fact about the running state and sits at level 0. The second says:
*composing the running `T` with the final `T` lands inside the final `T`*. It
mentions `yp_zT`, the value `T` has at loop exit, so it is level 1; at exit the
two copies agree and it collapses to `T ; T ⊆ T`, which is the postcondition.

**Worked example with several prophecy levels — `Example0106`.** A left-linear
closure loop over `Base`, with `T` the closure, `T_aux` the previous round's
value, and `RBound` a relation the program never touches:

```
level 0  (op_zT = (op_zBase ∪ π[0,3] (σ[#1 = #2] ((oa_zT × op_zBase)))))
level 0  (oa_zT ⊆ op_zRBound)
level 0  (op_zT ⊆ op_zRBound)
level 1  (π[0,3] (σ[#1 = #2] ((yp_zT × op_zT))) ⊆ yp_zT)
```

The first transcribes the body: *`T` is `Base` together with `T_aux ; Base`*.
The second and third say *both the previous round's value and the current one
stay inside the given bound `RBound`* — these are what discharge the
postcondition's upper-bound half, and they need the precondition's statement
that `RBound` is closed. The fourth is the prophecy clause: *the final `T`
composed with the running `T` stays inside the final `T`*, which at exit is
transitivity of the result.

### `Counterexample.json` — an accepted refutation

```json
{"kind": "whiel_framework_ii_counterexample", "version": 1,
 "instance": {"relations": [{"name": "p::E", "rows": [["num:0", "num:1"]]}]},
 "instance_identity": "...", "scope_identity_sha256": "...",
 "fuel_consumed": 6, "fuel_policy": {...}, "provenance": {...}, "task": {...}}
```

- `instance.relations` is a finite database over the **input** schema: one
  entry per relation, each with its rows. A relation that is empty in the
  witness is still listed, with `"rows": []`.
- Every cell is a string in canonical form: `num:<n>` a natural number,
  `str:<text>` a text value, `bool:0` and `bool:1` the Booleans. A bare JSON
  number is not a cell.
- Relation names here are the schema's own keys (`p::E`, or `o:p::E` with the
  lift prefix), not the clause spelling of §3.
- `fuel_consumed` is how many steps the replay of the program on this instance
  took; `fuel_policy` is the bound it ran under (`kind`, an optional host fuel
  bound, and the wall-clock `validation_limit_nanos`). They describe the
  validation, not the difficulty of the input.
- `provenance` says where this instance came from: `consultation` with the
  digests of the epoch that proposed it, in a campaign run; `recorded_witness`
  for an instance checked in with the benchmark.
- `instance_identity` and `scope_identity_sha256` are digests that bind the
  instance to this input; `task` names the input's module, namespace and source
  digest.

### `Accepted.json` — the receipt

A short envelope written the moment the untrusted verifier accepted. Use two
fields: `verdict` (`valid` or `invalid`) and `search` (`elapsed_seconds` and
`limit_seconds`, the same measurement `search_seconds` reports). `record` names
the file beside it that holds the answer. The `core` block is machine identity
data — digests, the frozen partition, scope identity — and can be ignored for
analysis.

## 4. Settings and comparability

Compare `search_seconds` on the **same machine under similar load**, with
matching experiment controls and toolchain. Matching settings or machine class
alone is insufficient. Vampire's portfolio divides a wall-clock allowance into
strategy slices, so processor speed and contention can change which strategy
finishes and which retry rung succeeds, as well as the elapsed time. Treat
cross-host results as separate measurements and record each host's hardware.

`verifier/campaign-settings.json` holds `schema_version`, the resolved `inputs`
list, the `proposer` selection, and `controls`; every `result.json` repeats the
same controls as `campaign_controls`.

| Field | One line |
| --- | --- |
| `search_limit_seconds` | The per-input search allowance. |
| `certification_limit_seconds` | The separate per-input certification allowance. |
| `consultation_limit_seconds` | Optional allowance for one epoch, including its corrections; null means none. |
| `iteration_limit` | Optional cap on epochs per input; null means none. |
| `transport_retries` | Extra attempts per epoch after a transit failure. |
| `certificate_solver_limit_seconds` | Seconds per solver job during certification. |
| `counterexample_validation_limit_seconds` | Wall-clock allowance for replaying a proposed counterexample. |
| `certify` | `inline`, `deferred` or `never`. |
| `casc_portfolio` | `enabled` or `disabled`: whether a proof-lane launch may escalate from the direct strategy into the `casc_2025` portfolio. |
| `proof_casc_share`, `proof_casc_retry_share` | The portfolio's share of a launch's baseline and of the time a retry adds beyond it. Both are `0` when the policy is `disabled`. |
| `retry_allowance_seconds` | The cumulative launch allowances in force, in seconds: how long one clause check's key may search on its first launch, its second and its third. `[30, 90, 240]` unless the run set `--retry-allowance`, and never null. |
| `premise_role_retries` | The TPTP role a *retry* launch writes the check's premises under: `negated_conjecture` unless the run set `--retry-premise-role axiom`. A first launch always writes them as `axiom`. |
| `workers` | Clause checks in flight at once for one input. Every other budget is derived from it. |
| `resource_limits` | The nine workspace and API guard values (also in `resource-limits.json`). |
| `budgets.checks` | The same number as `workers`. |
| `budgets.lanes` | Lanes per check: always 2, a proof lane racing a finite-model lane. |
| `budgets.finite_model_lane` | Whether the second lane is on; always true in production. |
| `budgets.vampire_processes` | Solver processes that may run at once: `checks × lanes`. |
| `budgets.lean_workers` | Lean worker processes serving admission and validation. |
| `budgets.lean_worker_threads` | Threads inside one Lean worker. |
| `budgets.lean_round_trip_timeout_seconds` | How long one Lean request may take. |
| `budgets.cpu_permits`, `budgets.runtime_worker_threads` | The run's CPU permit pool and async runtime threads. |
| `budgets.certification_jobs` | Certificate builds in parallel during certification. |
| `budgets.vampire_memory_limit_mb` | What one solver process is launched under. |
| `budgets.vampire_planned_footprint_mb` | What the memory estimate divides by. |
| `budgets.host_parallelism`, `budgets.host_memory_bytes` | The machine the defaults were derived from. |
| `budgets.memory_estimate_checks`, `budgets.exceeds_memory_estimate` | What the memory estimate allowed, and whether the effective `checks` exceeded it. Reported only: memory no longer bounds `checks`. |
| `budgets.exceeds_host_parallelism` | Whether `checks x lanes` exceeds `host_parallelism`. Reported only. |

**How a launch's solver time is spent.** Each clause check races a proof lane
against a finite-model lane. Every stage of both lanes is told the limit it runs
under, and every one of those limits is a function of the launch's allowance
alone, never of the wall clock left when the stage started — the solver's
schedules scale their strategy slices by that number, so an unstated or drifting
limit is a different search, not a longer one. The runner keeps its own deadline
behind each proof stage as a backstop, two seconds past that stage's stated
limit, so the ordinary end of a stage is the solver stopping itself and
reporting: an inconclusive result of that launch, charged to the retry ladder.

Inside the proof lane one process runs at a time: the **direct** strategy first,
under its own limit, and then — only if the direct stage ran out of its prefix or
came back unknown — the **`casc_2025` portfolio**, under its own. The portfolio
is single-core with a fixed seed and no schedule shuffling. For allowance `a`,
with the baseline `b` every launch keeps (30 seconds unless the run set
`--retry-allowance`), the portfolio's share is
`ceil(proof_casc_share · b + proof_casc_retry_share · (a − b))` and the direct
prefix is the rest; the two shares partition `a` exactly, though each is rounded
up to the next decisecond on its way to the solver. The portfolio is given its
share whichever escalation reached it — a direct stage that gives up early does
not hand it the leftover, because the leftover is wall clock; the launch simply
ends early instead.

The finite-model lane is never split and must outlive every proof-lane stage, so
it is given the launch's own outer deadline: `a` plus the runner's grace for each
proof stage, `a + 4 s` with the portfolio on and `a + 2 s` with it off. Its
stated limit therefore coincides with that deadline rather than sitting behind
it, and what ends this lane in practice is the race — the other lane concluding,
or the deadline. Since the proof lane ordinarily stops itself at `a`, the
finite-model lane can search alone for up to the grace afterwards; that is time
the proof lane does not get, and it is the lane that produces `invalid`
verdicts, so at small allowances it is worth reporting alongside the allowance
itself. At the defaults over the default 30/90/240 ladder:

| Launch | Allowance | Direct | Portfolio | Finite model |
| --- | --- | --- | --- | --- |
| 1st | 30 s | 22.5 s | 7.5 s | 34 s |
| 2nd | 90 s | 37.5 s | 52.5 s | 94 s |
| 3rd | 240 s | 75 s | 165 s | 244 s |

One check can therefore hold both its solver slots for 240 seconds plus the
graces, and a key only reaches that rung after a 30-second and a 90-second
launch in earlier epochs — at least 364 seconds of a 600-second
`--search-limit` spent on one key. At `--workers 4` that is one of the four
concurrent checks occupied for 40 % of the input's whole allowance, so an input
with several such keys will meet the search limit mid-sweep rather than
finishing it. That is the intended trade — the third rung exists for checks
nothing shorter reaches — but it belongs in any reading of a run that ends on
`OverallTimeout`.

The rungs grow faster than the baseline because only the part of a launch
beyond that baseline is shared at `proof_casc_retry_share`, so a ladder in
equal steps would leave the last portfolio share small. A portfolio share is
not a deadline it may stop short of, either: the schedule scales every strategy
slice by the limit it is given, so a problem the portfolio proves at one limit
can time out at a larger one and be proved again at a larger one still. That is
why every per-stage limit is a fixed function of the ladder and the two shares,
and why the ladder is recorded — a share is a search, not an amount of
patience.

**The premise role a launch renders under.** A clause check is one
implication: the premises are the negated guard and the invariant clauses, and
the conjecture is what they must entail. The first launch of a check writes
those premises under the TPTP role `axiom`; every retry writes the same
formulas, with the same names, bodies and order, under
`premise_role_retries` — `negated_conjecture` by default, asserted as written
rather than negated, so the two renderings are the same logical problem. The
word is a search hint: the solver treats `axiom` formulas as background theory
and deprioritises them, which is the wrong instinct when the premises are the
hypotheses of the implication being proved. It is not uniformly better, so the
first launch keeps the plain rendering. Both lanes of a launch read the one
rendering that launch produced.

The condition each accepted clause
was proved under is recorded per clause in `Core.json`'s frozen payload inside
`Accepted.json`, as `initialization_profile` and `step_profile`; certification
runs each job under the profile its label names.

**Comparability rule.** Two runs' results and timings may be compared only when
all of the following match: the entire `campaign_controls` block including
`budgets`, `retry_allowance_seconds` and `premise_role_retries` — a run whose
launches get 30/90/240 seconds has searched each key for a different length of
time than one whose launches get 5/12.5, and a run whose retries are
goal-tagged has run a different search on the same formulas than one whose
retries are not, whatever else the two share; the code revision (`run.json`'s `git_revision`); the solver and Lean
build (the toolchain pins the run verified); and the same machine under similar
load. A
difference in any one of them changes how many checks race for a core and how
long a borderline check has, which changes both timings and, at the margin,
which inputs are solved at all. Report the controls block with the numbers.

`proposer` records the endpoint the run was told to start — a path and an
opaque argument array. It is a selection, not verified provenance, and it names
no model. Which model produced a run is the operator's record, not the
verifier's.

## 5. The flags the experiments set

The specs in the harness's `experiments/` directory fix these:

| Flag | Value | Why |
| --- | --- | --- |
| `--workers` | 4 | Deliberately modest and laptop-replicable: 4 checks, so 8 solver processes. Not a machine maximum; on a machine with at least 8 logical cores this is also the default, so the specs set it explicitly only so a smaller machine still runs the same configuration, with a warning rather than a silent narrowing. |
| `--search-limit` | 600 s | The per-input search allowance, the same for every input. |
| `--certify` | `never` | A collaborator's campaign stops at acceptance; certification is a separate later `campaign certify --run <run>/verifier`, which needs no model and can run elsewhere. |
| `--retention` | `all` | Keeps the clause ledger and the consultation records, without which an epoch cannot be reconstructed. |
| `--transport-retries` | 0 (the default) | A transit failure is not retried on the same epoch: the epoch is recorded as failed, its feedback is published, and the search continues with a fresh one. |
| `--casc-portfolio` | `on` (the default) | A proof-lane launch that the direct strategy does not settle escalates into the `casc_2025` portfolio for the rest of its allowance. Turning it off is an ablation, not a normal run. |
| `--proof-casc-share`, `--proof-casc-retry-share` | 0.25 and 0.75 (the defaults) | How the launch allowance is divided between the direct prefix and the portfolio; see §4. |
| `--retry-premise-role` | `negated_conjecture` (the default) | The role a retry launch writes the check's premises under; see §4. `axiom` is an ablation, not a normal run. |
| `--tools` | all six (the default) | The proposer may use `countermodel`, `strongest_refutations`, `history`, `ledger`, `validate_clauses`, `evaluate_clauses`. Restricting them is an ablation, not a normal run. |
| `--workspace-bytes`, `--workspace-files`, `--workspace-entries`, `--workspace-directories` | raised, by `--retention all` itself now that no explicit flag is set | See §6. |
| `--minimum-free-bytes` | default | So a genuinely full disk still stops the run. |

**Exit codes.** 0 every input certified; **4 every input accepted and awaiting
certification — the success code of a `never` or `deferred` run**; 3 an
incomplete or failed input, or a resource guard stopping the campaign; 2 an
argument or bootstrap failure; 130 interrupted.

## 6. Independence and repeatability

Each input is an **independent trial**. Before its search the campaign builds
it a fresh input directory and staging root, resolves the Lean worker and the
pinned solver, binds a fresh verifier state with its own clause catalogue and
ledger, and starts a **new proposer endpoint** with no memory of any earlier
input. Inputs run one after another, and the next starts only after the
previous one has finished searching, certifying where applicable, and cleaning
up. No state, no clause and no conversation crosses between inputs.

Two things qualify that independence:

1. **The workspace guard is campaign-wide.** It counts the live bytes, files,
   directory entries and directories of the whole run, not of the input
   currently running. Under `--retention all` every earlier input's ledger,
   consultation records and artifacts are still on that count, so at the
   ordinary per-input allowances a long run would stop partway through against
   its predecessors' residue rather than anything the current input did. This
   is why `--retention all` itself raises those four limits, unless an
   explicit `--workspace-*` flag says otherwise for one of them; the specs no
   longer need to set them separately. If a run reports `resource_exhausted`
   with unrun inputs, check this first. A later standalone `campaign certify
   --run <run>/verifier` (§5's `--certify never`) inherits the same raised
   limits from the run's own recorded settings for any flag it is not given,
   so the certification step does not reintroduce the small default the
   search itself never used.
2. **The limits are wall-clock, so checks are load-sensitive.** A clause check
   has a fixed number of seconds. On a loaded machine a borderline check that
   would have been proved comes back `timed_out` instead, the clause stays
   pending, and the input may end differently. Run a campaign on a quiet
   machine, and do not run two campaigns at once.

**Model sampling is unseeded.** Nothing in the campaign fixes a sampling seed
for the proposer, and providers do not guarantee determinism even at a fixed
temperature. Two runs of the same spec against the same model will differ in
which clauses are proposed, in the number of epochs, and sometimes in which
inputs are solved. Treat a campaign as one sample: report the configuration and
the number of runs, and do not present a single run's per-input epoch count as
a property of the model.

The replay proposer is the exception and is fully deterministic: it consults
nothing and submits the repository's recorded answer for each input. Use it to
check the pipeline, never as a result.

## 7. Checking a replay against its transcript

A campaign's own transcript can be frozen into one small file --
`python3 -m agent_houdini export-transcript RUN_DIR transcript.json`, see the
[harness README](../agent_houdini/README.md#freezing-a-transcript-for-a-collaborator)
-- and replayed by
[the replay proposer's transcript mode](../agent_houdini/README.md#the-replay-proposer),
consultation by consultation, with no model at all. `python3 -m agent_houdini
compare-runs transcript.json REPLAY_RUN` (or two live run directories,
ORIGINAL and REPLAY, without a transcript file at all) then reports three
named checks, each PASS or FAIL with its specific differences listed, and
exits 0 only if all three pass:

- **1st replay fidelity check** -- every input present in both runs has the
  same verdict class: accepted valid, accepted invalid, or not accepted
  (every status other than `valid[_uncertified]`/`invalid[_uncertified]`
  counts as not accepted, so an original that ended `search_timeout` matches
  a replay that ended `incomplete`). An input present in only one run is
  listed and, by default, ignored; `--require-all` makes that a failure.
- **2nd replay fidelity check** -- for every input accepted valid in both, the
  accepted Core is the same set of clauses and each clause is committed at
  the same level; for every input accepted invalid in both, the same
  counterexample instance (each relation's own set of rows).
- **3rd replay fidelity check** -- the same set of `(clause, check kind,
  level, outcome)` entries in the two runs' attempt ledgers, restricted on
  both sides to rounds that *completed* (the verifier finished a
  consultation and issued the next request, or accepted; `attempt_history`'s
  own `consultations` list says which one did not, always the last),
  ignoring order, timing, attempt numbering and duplicates. An entry whose
  outcome is inconclusive on either side is excluded from the pass/fail
  decision and listed separately as a timing difference. An input with no
  completed round at all -- the limit expired before the original ever
  finished a single consultation, so there is no catalog to check anything
  against -- is reported by all three checks as "no completed round --
  nothing to compare" and never fails on its account.

### Why a transcript replay of a timed-out input can still match exactly

A naive replay of an input the original's own search limit cut off does not
match: it submits every recorded consultation, including one the original
never got a real answer from, and content the original's own correction
cycle refused and never checked.

- **A correction never runs a round.** B's own message to the proposer says
  so verbatim -- "Your previous response was refused and no round ran" --
  whether the correction is an envelope refusal (a stale response binding,
  decided before a single clause is read) or a content refusal (a lexical
  error, a drop conflict). `export-transcript` reads each consultation's own
  number from its retained prompt and collapses a correction cycle to its
  *last* request: the earlier, corrected-away attempt's clauses are dropped
  from the file entirely, because replaying them would hand the live
  verifier a *freshly rebound*, no-longer-refused version of content the
  original never admitted -- generating real ledger entries for clauses the
  original's own search never got to check at all. This was the dominant
  cause the first time this check failed on `Example0001`: two of its four
  consultations were envelope-refused corrections, and a naive replay,
  by re-binding and resubmitting their original content anyway, checked
  clauses the original had, by design, thrown away unread.
- **A round the deadline reached but never answered is marked `cut_off` and
  is not replayed.** `TranscriptSource` ends the search there (see
  [the replay proposer](../agent_houdini/README.md#the-replay-proposer))
  instead of submitting nothing, exactly as it does at the true end of the
  transcript. Because that round is never replayed, and B never admits a
  clause on a round it cancels, the replay's own catalog ends up with
  exactly the clauses admission ever gave the original: the task's own
  ambient scope plus whatever a completed round proposed, nothing a cut-off
  round would have added. No further per-clause filtering of the expected
  ledger is needed or applied for this reason: every entry the original's
  own ledger records -- ambient clauses included, which no round ever
  explicitly "proposes" -- already belongs to a round that completed. An
  earlier version of this tool filtered the expected ledger down to clause
  text a surviving round's own submission literally contained; that dropped
  ambient/precondition clauses too, which is a masking bug, not this rule,
  and is exactly the residue seen comparing `Example2010`: two identical
  entries for an ambient precondition clause (`initialization`/`maintenance`
  level 0, `proved`, present and matching on both sides) were dropped from
  the *original*'s own expected ledger alone because no round had "proposed"
  it, which then read as "only in replay". Removing that filter, plus the
  `completed_rounds` restriction in `compare-runs` itself (so a replay-side
  entry produced after the original's last completed round, including
  anything decided while the replay was closing, is ignored rather than
  reported), is what makes the 3rd check an exact comparison on a timed-out
  input rather than a residue report -- a real difference within a completed
  round still fails it.

**Known limitations.**

- The compared entry is `(clause text, check kind, level, outcome)`; nothing
  in the retained ledger identifies a check's own premises stably across two
  different runs' internal state, so a clause legitimately re-checked under
  a different premise set in a later round -- proved once, refuted later, or
  the reverse -- appears as two ordinary, separately-comparable set members
  rather than one entry distinguished by round. This is rare (it takes a
  clause whose provability genuinely changes as the Core evolves) and is not
  mistaken for a fidelity failure only because both members must still
  appear on both sides to pass; if you see it, it is this limitation, not
  evidence either side did something different from the other.
- A clause's ledger text is read from the run's own final catalog snapshot,
  which the deadline can land before ever publishing (a settlement recorded
  as `final_owner_unavailable` rather than `final_owner_projection` --
  empirically the more common of the two for a genuinely non-accepted
  input, not a rare corner). Every ledger row then falls back to a
  run-local `#<id>` label instead of real clause text, and two runs'
  `#<id>` labels compare unrelated internal numberings, not the same clause
  under two names, so a difference there says nothing reliable either way;
  read a PASS or FAIL on an input in this state with that in mind, or skip
  it with `--expect-different`.

Replaying a transcript under identical conditions on an equivalently loaded
machine should settle every check the original settled. In practice
identical conditions cannot be fully reproduced -- solver work is
wall-clock-sensitive (§6) -- so a timing-sensitive clause check can come back
decided on one side and inconclusive on the other. That is reported as a
timing difference under the 3rd check, not as a verifier change: only a
difference in a *decided* outcome, or in the 1st or 2nd check, says something
changed. `--expect-different ID[,ID...]` names inputs whose differences are
still reported but do not fail a check, for a verifier change already known
to affect specific inputs.
