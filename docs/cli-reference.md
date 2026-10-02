# AgentHoudini CLI reference

The Rust verifier command, `whiel-symbolic campaign run`, accepts any executable
implementing the public proposer API. It requires an explicit endpoint or the
explicit no-proposer diagnostic. AgentHoudini's separate Python launcher owns
provider selection and native configuration.
The [B parser](../whiel_runner/src/campaign_cli.rs),
[C launcher](../agent_houdini/launcher.py) and their help define accepted options.

```text
whiel-symbolic campaign run (--input ID[,ID...] | --all)
  (--proposer-executable PATH | --no-proposer) [OPTIONS]
whiel-symbolic campaign certify --run DIR [OPTIONS]
```

B option values are separate arguments, except the supported `--proposer-arg=VALUE`
form. `--input`, `--retry-allowance` and `--proposer-arg` may repeat; other options
may appear once. Each proposer argument is forwarded as one opaque value,
including spaces, empty strings or `--help`; no shell splitting occurs.
Durations are finite positive seconds (fractional seconds accepted except
`--certificate-solver-limit`, which requires positive whole seconds); counts are
unsigned integers. Resource guards require positive values; optional host limits
accept zero. Duplicate input IDs after alias resolution are rejected. Unknown
options are refused without echoing their values.

## Inputs, processes and storage

| Option | Default | Meaning |
| --- | --- | --- |
| `--repo PATH` | current directory | Repository containing current inputs and pinned tools. |
| `--input ID[,ID...]` | required unless `--all` | Current exact IDs or numeric aliases such as `1`/`0001`; repeat to extend a subset. |
| `--all` | off | All immediate current `Benchmark/*/Input.lean` inputs; exclusive with `--input`. |
| `--destination DIR` | fresh `artifacts/campaigns/<id>` | New output root; existing destinations are refused. |
| `--worker PATH` | watched worker build | Existing fixed-ambient worker executable; checked task identity must match input. |
| `--workers N` | `clamp(floor(cores / 2), 1, 4)` | Clause checks the run may have in flight at once. Every other concurrency budget is derived from it; it does not parallelize model consultations or inputs. See [derived budgets](#derived-concurrency-budgets). |
| `--retention certificate-only\|all` | certificate-only | Artifact retention after settlement, and whether the run records its consultations. A published `Valid` or `Invalid` certificate tree never carries the solver-evidence subtree (per-job `problem.p` and normalized `leancheck.lean`) either way; under `all` a `Valid` certification's evidence is kept beside the run's other payloads, under `<destination>/<input>/CertificateEvidence/`, and under `certificate-only` it is dropped. |
| `--certify inline\|deferred\|never` | inline | When this run certifies what its search accepts. See [searching and certifying separately](#searching-and-certifying-separately). |
| `-h`, `--help` | — | Print usage without creating output or starting a process. |

### Searching and certifying separately

A campaign is an untrusted search followed by a deterministic certification.
The search consults the proposer; the certification consults nothing, uses no
model, and costs minutes and gigabytes per input.

Whatever the mode, the moment the untrusted verifier accepts, the run writes
into the input's directory `Core.json` (valid) or `Counterexample.json`
(invalid) together with `Accepted.json`, an envelope naming that record, the
verdict, the search's timing, the input's task identity and, for a valid
result, the frozen Core's own payload. Those records are written **before** any
certification starts, so a certification that fails or times out no longer
loses the invariant the search found.

- `inline` certifies each input immediately after its own search, in process.
- `deferred` searches every input first and then runs one certification phase —
  exactly the phase `campaign certify` performs — over the whole run directory.
- `never` stops at acceptance. The run directory is certified later, and
  possibly elsewhere, with `campaign certify --run DIR`.

Under `deferred` and `never` an input that has been accepted but not yet
certified carries the status `valid_uncertified` or `invalid_uncertified`, and
the run's `summary.json` reports `all_accepted` true and `all_certified` false.
An uncertified input has neither a `Certificate/` tree nor a
`CertificateEvidence/` directory — only a certification produces either, so
under `--certify never` the whole run directory has none when `campaign run`
returns. A run that ends with every input accepted and none certified exits
with code 4 rather than 0. An accepted record authorizes nothing: only a
published, kernel-checked `Certificate/` tree does.

### `campaign certify`

```text
whiel-symbolic campaign certify --run DIR [OPTIONS]
```

Certifies every accepted, uncertified input of a run directory from the records
its search left, by the same standalone path `certificate build --core` and
`--counterexample` take, publishes `Certificate/` beside each record, and
rewrites that input's `result.json` (with the axiom closure from the build
receipt) and the run's `summary.json`.

| Option | Default | Meaning |
| --- | --- | --- |
| `--run DIR` | required | The campaign run directory to certify. |
| `--repo PATH` | current directory | Repository containing the current inputs and pinned tools. |
| `--worker PATH` | watched worker build | Existing fixed-ambient worker executable; resolved once and shared by every job. |
| `--jobs N` | `min(cores / 2, (memory - 4 GB) / 4 GB)`, at least 1 | Inputs certified at once. Each job is a whole Lean elaboration, so memory bounds it as much as cores do; the reading is total physical memory, not free memory and not a container's own limit, so the default keeps one job's headroom and this stays the operator's knob on a shared or limited machine. |
| `--workspace-bytes`, `--workspace-files`, `--minimum-free-bytes`, `--workspace-entries`, `--workspace-directories` | the run's own recorded limit; see below | The workspace guard the phase runs under. A certification spends gigabytes per input, so it is guarded like a search; `campaign run --certify deferred` inherits the run's own guard instead of starting a second one, and skips the phase entirely when that guard has already refused the run. |
| `--certification-limit SECONDS` | 600 | Certification allowance per input. |
| `--certificate-solver-limit SECONDS` | 60 | Positive whole seconds per valid leancheck job. |
| `--retention certificate-only\|all` | certificate-only | Under `all`, a valid build's solver evidence is kept as `CertificateEvidence/` beside its certificate. |

**The workspace guard's default is the run's own, not a fresh small one.**
`campaign certify --run DIR` parses its own `--retention` and `--workspace-*`
flags independently of the run being certified, so its plain defaults are the
small `certificate-only` figures regardless of what the run itself needed. An
omitted `--workspace-*`/`--minimum-free-bytes` flag therefore adopts, field by
field, the limit the run's own `campaign-settings.json`
(`controls.resource_limits`) actually recorded — the same raised figures a
`--retention all` run needed — rather than the small default; an explicit flag
still wins for its own limit. Only when that record cannot be read at all does
an omitted flag fall back to the ordinary `--retention`-keyed default below,
and the command says so on its output. `campaign run --certify deferred`
inherits its own guard directly and never makes this decision.

A run directory is untrusted input to this command, so nothing in it is taken
at its word:

- An input that already carries a `Certificate/` tree its own result claims is
  **re-checked, not skipped**: the identity recorded in `Accepted.json` is
  compared against the input on disk, and the tree goes through the same
  revalidation the inline publication performs — every module rebuilt from
  source, the theorem elaborated at the exact `Input.lean` declaration type,
  the axiom closure audited to exactly std3. That costs a Lean build per
  already-certified input, which is the price of the claim being checked
  rather than assumed. A tree that does not pass, or whose result names no
  `certificate_module`/`certificate_theorem` to revalidate it with, is
  reported as `certification_unchecked` and left exactly where it is.
- An input whose declarations or scope changed since it was accepted is
  reported as `input_changed` and is not certified; the other inputs still are.
- A published tree is never replaced or removed, an input the command never
  entered keeps the status it had, and `result.json` and `summary.json` are
  installed atomically. A result that was lost or truncated is rebuilt from the
  acceptance envelope beside it rather than stopping the run.
- Leftovers of an interrupted certify are cleared on entry. It stages under its
  own fresh root and never re-reserves the search run's.
- One certification runs at a time per run directory; a second is refused by
  name rather than racing the first.

Exit codes: 0 every selected input certified, 2 argument or bootstrap failure,
3 some input is neither certified nor accepted, 4 every input accepted and some
still uncertified, 130 interrupted.

### Derived concurrency budgets

`--workers N` means N concurrent clause checks. Nothing else is user-facing:
the run derives every other budget from N, the machine's parallelism and the
number of solver lanes one check occupies, and writes all of them verbatim into
`campaign-settings.json` under `controls.budgets`. These records let a reader
compare resource controls. Timing comparisons additionally require the same
machine and similar load; see the
[analyst's guide](analysts-guide.md#4-settings-and-comparability).

| Budget | Derivation |
| --- | --- |
| `checks` | N, from `--workers`; by default `clamp(floor(cores / 2), 1, 4)`. |
| `lanes` | Vampire slots one check occupies at once. A campaign races two lanes, so 2. |
| `finite_model_lane` | Whether the finite-model lane races the proof lane. It does, always. |
| `vampire_processes` | `checks x lanes`. The race takes a check's slots atomically. |
| `lean_workers` | `min(checks, 4)`. Obligation preparation is not the throughput gate. |
| `lean_worker_threads` | 1. A spawned worker's `LEAN_NUM_THREADS` is pinned, never inherited. |
| `lean_round_trip_timeout_seconds` | The allowance one Lean worker exchange runs under before the worker counts as lost. |
| `cpu_permits` | The machine's parallelism. These bound CPU-heavy jobs, not Lean exchanges. |
| `runtime_worker_threads` | The machine's parallelism, at least 2. |
| `certification_jobs` | `checks`. Settlement's solver and packaging fan-out, which an explicit `--workers` has always fed. |
| `host_parallelism` | What the machine reported. |
| `host_memory_bytes` | Physical memory, or null when it could not be read. |
| `vampire_memory_limit_mb` | The `--memory_limit` every Vampire process is launched with: the pinned build's own default, recorded so a run says what it ran under. |
| `vampire_planned_footprint_mb` | What one Vampire process is planned to occupy. A planning figure, not enforced; the memory estimate divides by this. |
| `memory_estimate_checks` | `host_memory / (lanes x vampire_planned_footprint)`, floored at 1; null when memory could not be read. |
| `exceeds_memory_estimate` | Whether the effective `checks` (default or explicit) exceeds that estimate. |
| `exceeds_host_parallelism` | Whether `checks x lanes` exceeds `host_parallelism`. |

Every campaign check races a proof lane against a finite-model lane, so a
clause that is not inductive comes back refuted with a Lean-validated
countermodel rather than merely unproved within the budget. A production check
configuration cannot be built without the finite-model lane, so no option,
default or omitted argument reaches a proof-only search; proof-only exists only
as an explicitly named test configuration. The race takes both
its Vampire slots atomically, so N concurrent checks need `2N` processes;
deriving the budget as `checks x lanes` is what stops the lane policy from
silently turning `--workers N` into `N/2` concurrent checks. Even `--workers 1`
gets two slots, so the two lanes always race rather than running in turn.

**Neither memory nor the core count caps `checks`.** The verifier is fast
relative to the proposer, so concurrency beyond a few checks buys little
measurable throughput, and a default must not claim a large machine on the
operator's behalf: the default is `clamp(floor(cores / 2), 1, 4)`, full stop.
A check also costs a Vampire process per lane, and a process is bounded by
memory rather than by a core, so the run's output warns — but does not
narrow anything — when the effective `checks` (default or explicit) exceeds
`host_memory / (lanes x vampire_planned_footprint)`, and separately when
`checks x lanes` exceeds `host_parallelism`.

Two memory numbers are recorded, and they are not the same thing.
`vampire_memory_limit_mb` is the limit every process is *launched under* — the
pinned build's own default, passed explicitly so a run states it, and
deliberately far above any real footprint. `vampire_planned_footprint_mb` is
what a process is *planned to occupy*, and is what the estimate divides by;
dividing by the hard limit would report every ordinary machine as exceeding a
one-check estimate. Nothing enforces the planning figure.

When the machine's memory cannot be read, nothing is reported on that account
and the default stands as the core rule alone gives it. An explicit
`--workers` is always honoured, with a warning on the run's output when it
exceeds either the memory estimate or the core count.

**Choosing N.** On a machine with at least 8 logical cores the default equals
4 — the same `workers: 4` the shipped experiment specs set explicitly, so a
smaller machine still runs the same configuration, with a warning rather than
a silent narrowing. Raising N past `cores / 2` mostly adds queueing rather
than throughput; on a many-core server the practical ceiling is the
proposer's own pace, not this machine's cores or memory.

Numeric selectors resolve dynamically against pure-digit `Example` suffixes: `1`
and `0001` both select `Example0001`. An ambiguous numeric match fails; use an
exact ID. Selecting `1,Example0001` also fails because it repeats the same input.
A number never infers an ID whose suffix carries a letter; pass that exact ID.

Input discovery rejects unsafe IDs and linked input directories; a current
input must be registered in the Lean worker. After an input change, run
`python3 scripts/generate_fixed_ambient_registry.py` and rebuild the worker
with the watched script. `--check` verifies registry source without changing it.
See [the corpus contract](../Benchmark/CORPUS.md).

## Generic endpoint selection

| B option | Meaning |
| --- | --- |
| `--proposer-executable PATH` | Required unless `--no-proposer`; executable file implementing wire 3. Relative paths resolve against `--repo`. |
| `--proposer-arg VALUE` | Repeat for each opaque argument. Requires an executable. The child starts in B's private transport directory, so pass absolute input/config paths when needed. |
| `--no-proposer` | Exclusive with an executable; source-exhausted diagnostic without an endpoint process. Input admission and the controller still run. |

B does not inspect provider configuration, authentication, prompts, sessions or
MCP. It supervises the generic endpoint and enforces its API and verifier limits.
See the [wire contract](../whiel_runner/src/proposer_api/wire/README.md).

## AgentHoudini launcher

Use C's public command for native agents:

```bash
python3 -m agent_houdini campaign run \
  --verifier "$PWD/whiel_runner/target/release/whiel-symbolic" \
  --provider codex --model <model> --reasoning-effort medium \
  -- --repo "$PWD" --input 1
```

C options precede the first `--`; B's options follow it. C chooses the endpoint,
so B's three endpoint-selection flags cannot also appear after that delimiter.
The endpoint mode started by B runs C's coordinator; it does not launch another
campaign. C validates configuration and resolves the provider CLI before replacing itself
with B's public executable.
Configuration failure returns 2; interrupted preflight returns 130 after cleanup.

Provider/model/effort, `--provider-cli`, `--isolation` and `--agent-*` settings belong
to C. `--model` is required and is passed to the provider CLI verbatim; C keeps no
model table and no default model. `--reasoning-effort` is optional and is also passed
through unchanged. `--provider-cli PATH` selects an explicit CLI executable for either
provider; otherwise `claude`/`codex` is resolved from `PATH`. See
`python3 -m agent_houdini campaign run --help` and the
[C README](../agent_houdini/README.md); B has no native registry or fallback.
C's `--no-proposer` before the separator skips native preflight and selects B's
explicit diagnostic.
See [provider setup](providers-and-auth.md) for native login and Linux confinement.

## Time and retries

| Option | Default | Meaning |
| --- | --- | --- |
| `--search-limit SECONDS` | 600 | Per-input search allowance after worker setup/input admission. |
| `--certification-limit SECONDS` | 600 | Separate certification/publication allowance after search. |
| `--consultation-limit SECONDS` | absent | Whole outer consultation, including corrections and transport retries, within the overall search allowance. |
| `--transport-retries N` | 0 | Additional NoResponse/TransportFailure attempts per request; checked range 0..8. |
| `--certificate-solver-limit SECONDS` | 60 | Positive whole seconds per valid-certificate Leancheck solver job; excludes transformation and kernel wall time. No invalidity solver job. A clause the search only reached on its top ladder rung may need more than the default here. |
| `--iteration-limit N` | absent | Positive maximum consultation count; exhaustion is a resource failure, not a verdict. |
| `--counterexample-validation-limit SECONDS` | 30 | Call-local Lean counterexample validation allowance, also bounded by enclosing search time. |
| `--retry-allowance SECONDS` | production ladder | Repeatable, nonempty, strictly increasing cumulative solver allowances. Replaces the ladder; does not add time to search. |
| `--retry-premise-role axiom\|negated_conjecture` | negated_conjecture | The TPTP role a *retry* launch writes the check's premises under. A first launch always writes them as axioms. See [how a launch's solver time is spent](#how-a-launchs-solver-time-is-spent). |
| `--casc-portfolio on\|off` | on | Whether a proof-lane launch may escalate from the direct strategy into the `casc_2025` portfolio. See [how a launch's solver time is spent](#how-a-launchs-solver-time-is-spent). |
| `--proof-casc-share FRACTION` | 0.25 | The portfolio's share of a launch's initial proof allowance. A decimal from 0 through 1 with at most six fractional digits. |
| `--proof-casc-retry-share FRACTION` | 0.75 | The portfolio's share of the time a retried launch adds beyond that baseline; same range and spelling. |

The baseline search solver budget is 30 seconds and the default production
ladder is 30/90/240 seconds. That top rung is four times the default
`--certificate-solver-limit`, so a clause accepted only on a third launch may
need a larger certificate solver limit before it certifies; an uncertified
input is reported as uncertified and authorizes nothing, so this is a budget to
set rather than a result to doubt. These are proof-search allowances, not native model
transport retries. The current command has zero transport retries per request
and no separate consultation deadline by default. If a configured consultation
limit expires, that request is closed; the controller may begin another
until the overall search or iteration guard ends the search. This is distinct
from solver retry and correction allowances. The whole certification phase
remains bounded independently of each certificate solver job. An external interrupt still
cancels either phase; exhausting search time cannot cancel a later independent
certification phase. Certification can itself time out.

### How a launch's solver time is spent

Each clause check races a proof lane against a finite-model lane. **Every stage
of both lanes is told the limit it runs under**, and every one of those limits
is a function of the launch's allowance alone — never of how much wall clock
happened to be left when the stage started. That is what makes one campaign run
twice run the same searches: the solver's `casc_2025` schedules scale every
strategy slice by `--time_limit`, and its default saturation algorithm decides
what it can afford to keep from the same number, so an unstated or drifting
limit is not a longer or shorter search but a different one.

The runner keeps its own deadline behind each **proof** stage as a backstop, at
that stage's stated limit plus a fixed two-second grace. The ordinary end of a
stage is therefore the solver stopping itself and reporting, which the run
records as an ordinary inconclusive result of that launch and charges to the
retry ladder; the backstop only stops a solver that does not stop.

**The premise role.** A check is one implication: its premises are the
negated guard and the invariant clauses, and its conjecture is what they must
entail. The first launch of a check writes those premises under the TPTP role
`axiom`; every retry launch writes the same formulas, with the same names,
bodies and order, under `--retry-premise-role` — `negated_conjecture` by
default, which asserts them exactly as written rather than negating them, so
the two renderings are the same logical problem. The word is a search hint:
Vampire treats `axiom` formulas as background theory and deprioritises them,
which is the wrong instinct when the premises are the hypotheses of the very
implication being proved. It is not uniformly better, which is why the first
launch keeps the plain rendering and `--retry-premise-role axiom` restores the
old behaviour for an ablation. Both lanes of a launch read the one rendering
that launch produced, and each rendering is its own immutable artifact, so a
retry never overwrites what the first launch was given.

**Proof lane.** One process at a time, direct first: the direct strategy under
its own limit, then, if it did not settle the condition, the `casc_2025`
portfolio under its own. The portfolio runs single-core with a fixed seed, no
worker-seed randomization and no schedule shuffling.

For a launch with allowance `a`, the split is computed from the run's
`--proof-casc-share` q, its `--proof-casc-retry-share` r, and the baseline b
every launch keeps — 30 seconds, or the first `--retry-allowance` value when
one is given:

- the portfolio's share is `ceil(q·b + r·(a − b))`, and the direct prefix is the
  remainder, `a − that`. The two shares partition `a` exactly; each is then
  rounded **up** to the next decisecond on its way to the solver, so the two
  stated limits can sum to a fraction of a second more than `a` (the default
  ladder and shares land on exact deciseconds, so they do not);
- the direct stage runs first and is given its prefix as `--time_limit`;
- the portfolio stage starts only on an escalation — the direct stage ran out of
  its prefix, returned unknown, or there was no prefix because
  `--proof-casc-share` is 1. A malformed direct output or a direct process
  failure does not escalate;
- the portfolio is given **its share**, always, whichever escalation reached it.
  A direct stage that gives up early does not hand the portfolio the leftover:
  the leftover is wall clock, and a schedule scaled by wall clock is a different
  schedule every run. The launch then simply ends early;
- the portfolio is the terminal rung: there is no third stage and no
  re-escalation, and a direct-proved condition never reaches the portfolio.

**Finite-model lane.** Never split, and it must outlive every proof-lane stage,
so it is given the launch's own outer deadline rather than a limit behind it:
`a` plus the runner's grace for each proof stage the launch may run — `a + 4 s`
with the portfolio on, `a + 2 s` with it off. Its stated limit therefore
coincides with the runner's deadline instead of sitting a grace behind it, and
what ends this lane in practice is the race: the other lane concluding, or that
deadline.

One consequence is worth stating for a frozen configuration. The proof lane
ordinarily stops itself at `a`, so the finite-model lane can go on searching
alone for up to the grace — 4 seconds with the portfolio on, 2 with it off. That
is search time the proof lane does not get, and since the finite-model lane is
the one that produces `invalid` verdicts, it can turn a launch that would have
timed out into a verdict. It is a fixed number of seconds, not a fraction, so it
matters most at small allowances: it is a seventh of a 30-second launch and
several times a 1-second one.

With the portfolio on at the defaults (q = 0.25, r = 0.75), over the default
30/90/240 ladder:

| Launch | Allowance | `--time_limit`, direct | `--time_limit`, portfolio | `--time_limit`, finite model |
| --- | --- | --- | --- | --- |
| 1st | 30 s | 22.5 s | 7.5 s | 34 s |
| 2nd (1st retry) | 90 s | 37.5 s | 52.5 s | 94 s |
| 3rd (2nd retry) | 240 s | 75 s | 165 s | 244 s |

The rungs grow faster than the baseline because only the part of a launch
beyond that baseline is shared at r: a ladder in equal steps spends most of
its added time on the direct prefix, and its last portfolio share stays small.
A portfolio share is also not merely a deadline — the schedule scales every
strategy slice by the limit it is given, so a problem the portfolio proves at
one limit may time out at a larger one and be proved again at a larger one
still. That is the reason the per-stage limits are fixed functions of the
ladder and the two shares, and the reason the ladder is recorded: a share is a
search, not an amount of patience.

With `--casc-portfolio off` there is no second proof stage: the direct stage is
given the whole allowance — 30, 90 and 240 seconds — and the finite-model lane
`a + 2 s`. This is the one respect in which `off` is not byte-identical to
builds before the portfolio was wired: those builds stated no limit at all on
these two lanes, so the solver applied its own 60-second default and every rung
above it stopped at 60 seconds.

`off` also means no launch can produce a `casc_2025` winner, and the two share
options are then refused rather than recorded as a split that never
happened. The ladder itself is recorded too, as `retry_allowance_seconds` —
the cumulative launch allowances actually in force, `[30, 90, 240]` when
`--retry-allowance` is absent — because every per-stage limit above is a fixed
function of a rung and the two shares, so the rungs are what a reader needs and
the stage limits are not recorded again. The policy and both shares are
recorded in `campaign-settings.json`
under `controls`, alongside the retry premise role as `premise_role_retries`,
because two runs whose policies differ are running different
searches and their results are not comparable.

## Tools and optional host limits

`--tools countermodel,strongest_refutations,history,ledger,validate_clauses,evaluate_clauses`
selects exact optional query names; all six are enabled by default. `--no-tools`
disables them and is exclusive with `--tools`. Duplicate or unknown names fail.
`submit` always remains available and is not part of `--tools`. C-local skills
use `WHIEL_AGENT_SKILLS_FILE`; `get_skill` is rejected in the B query list.
C reads that library (a directory with `index.json` and one Markdown file per
skill, or a JSON file) once per consultation into an immutable snapshot, with
fixed byte bounds and nonblocking descriptor checks. Skills remain available
independently of B's optional query policy; they grant no semantic permissions.

Every host limit below is **absent by default** and takes an unsigned integer N.
These limits are disclosed to the proposer. A refusal or documented truncation
is not a semantic verdict on a clause or input.

| Option | Unit and effect |
| --- | --- |
| `--catalog-size N` | Maximum admitted catalog clauses. |
| `--clause-text-bytes N` | Bytes in one submitted clause's text. |
| `--countermodel-retention-tuples N` | Maximum model tuples retained in full; larger validated refutations remain known with an explicit omission. |
| `--drop-references N` | Drop references in one response. |
| `--evaluation-cost N` | Draft count × selected evaluated-instance count in one `evaluate_clauses` call; no silent partial evaluation. |
| `--level-bound N` | Maximum clause level; constrains admission and promotion. |
| `--proposal-size N` | Clauses in one response. |
| `--pushed-core N` | Core clauses shown in one push; omitted entries are explicitly marked. |
| `--reply-bytes N` | Bytes in one provider response. |
| `--strongest-refutations N` | Returned maximal-refutation entries; truncation is explicit. |

B has no session-mode option; sessions belong to the proposer. `--compress-core`
remains deferred. A caller-supplied executable and opaque arguments select a
proposer, not a new checker or arbitrary backend operation.

## Resource safeguards

All values below are positive integer bytes or counts. They are operational
limits, separate from optional semantic host limits and solver time allowances.

| Option | Default | Scope |
| --- | ---: | --- |
| `--api-traffic-bytes N` | 1073741824 (1 GiB) | Cumulative encoded generic API bytes per input. |
| `--api-messages N` | 16384 | Cumulative generic API packets per input. |
| `--artifact-bytes N` | 4294967296 (4 GiB) | Cumulative staged ArtifactStore payload bytes per input. |
| `--artifact-files N` | 50000 | Cumulative ArtifactStore payload file creations per input. |
| `--workspace-bytes N` | 8589934592 (8 GiB); 68719476736 (64 GiB) under `--retention all` with no explicit `--workspace-*` flag | Sampled live bytes in campaign-owned trees. |
| `--workspace-files N` | 100000; 1000000 under `--retention all` with no explicit `--workspace-*` flag | Sampled live regular files across those trees. |
| `--minimum-free-bytes N` | 2147483648 (2 GiB) | Minimum observed free bytes per involved filesystem. |
| `--workspace-entries N` | 200000; 2000000 under `--retention all` with no explicit `--workspace-*` flag | Visited entries per scan; pending traversal is also bounded. |
| `--workspace-directories N` | 25000; 250000 under `--retention all` with no explicit `--workspace-*` flag | Directories per scan. |

The workspace guard counts a whole campaign's live material, not one input's,
so under `--retention all` every earlier input's ledger, consultation records
and artifacts are still on the count when a later input runs; the raised
defaults give a retained run the room its own retention requires. Any
explicitly given `--workspace-*` flag wins for that limit regardless of
retention. `campaign certify` follows the same rule for its own `--retention`
flag; a *standalone* `campaign certify --run DIR` additionally adopts the run
being certified's own recorded limits for any flag it was not given — see
[`campaign certify`](#campaign-certify) above.

B counts generic API traffic in both directions, including packet headers,
attachments and lifecycle exchanges. Its cumulative allowance is shared across
requests and endpoint recovery; startup or final shutdown can exhaust it. The
wire also bounds each packet independently. C separately accounts for rendered
prompts, MCP and native work, using `--agent-*` limits before the launcher
separator. B does not accept a client-supplied debit or inspect native traffic.
The [wire contract](../whiel_runner/src/proposer_api/wire/README.md) defines exact
framing. Transport failures and resource exhaustion are nonsemantic.

Artifact budgets charge before staged writes/file creation, across scopes,
stdout and retained stderr. Deletion, retention cleanup or a failed attempt does
not refund this cumulative allowance. Direct metadata/certificate writes are
outside that exact payload budget and are observed by the workspace guard.
Exhaustion never refutes a proposal. Authoritative API exhaustion also stops
later campaign inputs and is reported in the summary, including when first
detected during startup or shutdown. A genuine cleanup failure retains priority
as the primary failure while the resource cause remains recorded.

B's workspace accounting covers campaign output and retained generic endpoint
transport directories. C separately monitors native scratch workspaces. B's
dedicated scan thread waits one second after each scan, so scan duration adds
detection latency; phase and
prepublication checkpoints also scan. Scans do not follow observed symlinks.
Transient missing metadata causes up to two whole-scan retries; persistent
metadata/free-space errors stop the campaign with a resource diagnostic.

Child processes can overshoot between observations. These safeguards are not a
filesystem quota, hard whole-process RSS limit, or whole-machine disk monitor.
Configured values appear in `resource-limits.json`, campaign settings and
feedback. See [results](results-and-troubleshooting.md) for early-stop reporting.

## What a run records

`--retention all` also turns on recording. Under it a run keeps two records of
its own conduct, published through the same staged, atomic artifact path as
every other payload and swept by the same budgets:

- **consultation records** — the actual API traffic of every consultation, as
  the hash-linked frames described under
  [recorded consultations](proposer-host-protocol.md#recorded-consultations),
  published as `runtime_trace` records under scope
  `["root", "consultation-records"]`;
- **attempt history** — the rounds the search performed: each ledger row with
  its clause, level, role, verdict and any refutation or invalidation, and each
  transport attempt against the proposer, published as one `runtime_trace`
  record under scope `["root", "attempt-history"]`.

The input's `result.json` names both: `consultation_records` gives the frame
count, chain head, kind, scope and the manifest ids of the frames in chain
order, and `attempt_history` gives the kind, scope and id of that record — or,
for either, the `error` that refused it. See
[results](results-and-troubleshooting.md) for the exact fields.

Both are published for **every** settlement outcome — `valid`, `invalid`,
`search_timeout`, iteration exhaustion, resource failure and interruption —
not only for a certified one. A run that fails still leaves what it did.

The recording is bounded by the run's own `--api-traffic-bytes` allowance,
because it copies that traffic. A recording that outgrows it is a run failure,
not a silent truncation; lower the allowance or shorten the run rather than
expecting a partial record. The frames are also staged as one set and promoted
only once all of them are written, so a recording refused by an artifact budget
publishes no frames at all, and `result.json` says so.

The default `--retention certificate-only` records neither. That run's
behaviour is unchanged: nothing is copied, and no recording fault can end a
consultation. Turn recording on when you intend to keep the evidence, not by
default.

## Exit codes

| Code | Meaning |
| --- | --- |
| 0 | Every selected input published a checked valid or invalid certificate. |
| 2 | Argument or bootstrap failure. |
| 3 | At least one input incomplete or failed. |
| 4 | Every selected input was accepted and the uncertified ones are still *awaiting* certification (`--certify never`, or a `deferred` run whose certification phase did not run). Its own code so that no script reading 0 as "certified" can read an uncertified run as certified, and none reading 3 as "something went wrong" can read a deliberate two-step run as a failure. A refusal a later certification cannot resolve — `input_changed`, `certification_unchecked`, `certification_failed`, `certification_timeout` — is a failure and takes 3, even when every input was accepted. |
| 130 | Interrupted. |

A checked `invalid` result is successful certification of a counterexample,
not a command failure. Inspect [result files](results-and-troubleshooting.md).
