# Whiel: VLDB artifact reproduction guide

Whiel verifies imperative relational programs against Hoare specifications.
A Python agent proposes invariants or counterexamples; a Rust verifier checks
those proposals using Lean and Vampire. A separate certifier produces Lean
proofs of the original specification or its negation. Search acceptance and
Lean certification are distinct results.

The artifact includes 86 benchmark tasks: 69 valid and 17 invalid, each with a
reference answer and a Lean certificate. Start with the token-free checks below
before running model-backed experiments. All commands are run from the repository
root. Generated files belong under ignored `artifacts/`; use a new output path
for each run.

**Auditing a certified answer:** read [AUDIT.md](AUDIT.md) before relying on a
certificate. It maps the Lean definitions behind the exact theorem, explains
the trust boundary, and shows how to check valid and invalid certificates and
their axioms.

- [Linux setup and builds](#linux-setup-and-builds)
- [Search and paper experiment settings](#search-and-paper-experiment-settings)
- [Token-free replay checks](#token-free-replay-checks)
- [Certification and shipped proof checks](#certification-and-shipped-proof-checks)
- [Direct Lean baseline](#lean-coding-agent-baseline-direct-lean)
- [Results, benchmark report and further documentation](#results-benchmark-report-and-further-documentation)

## Linux setup and builds

Use Linux x86_64 with Git, Python **3.11+**, Rust/Cargo supporting edition 2024,
elan, C/C++ build tools, CMake, Make, GNU coreutils, process utilities (`ps`,
`pgrep`, `pkill`), GNU Parallel, util-linux (`taskset`, `lscpu`) and bubblewrap.
The sandbox requires enabled user and PID namespaces and a system-installed Python interpreter; a virtual environment
interpreter is not supported by the bubblewrap relay. The Python package uses
only the standard library. The optional PDF report also needs `pdflatex`.

Install elan and Rust using their maintained installers, and the other tools
using your Linux distribution's package manager. `python3` must resolve to the
required interpreter because subprocesses also invoke that name. Lean is pinned
to **4.30.0-rc1** in [lean-toolchain](lean-toolchain); Lake and Mathlib follow that
pin. The upstream VampLean revision is pinned in [lakefile.toml](lakefile.toml).

```bash
python3 -c 'import sys; print(sys.version); assert sys.version_info >= (3, 11)'
elan toolchain install "$(cat lean-toolchain)"
bash scripts/setup_nosync.sh
LEAN_NUM_THREADS=1 scripts/watchdog.sh 4194304 lake --keep-toolchain update vamp_lean
LEAN_NUM_THREADS=1 scripts/watchdog.sh 4194304 lake exe cache get
python3 scripts/build_leancheck_vampire.py --jobs 4
python3 scripts/check_toolchain.py
```

Keep `--keep-toolchain`: the pinned upstream VampLean package declares a different
Lean version. [VampLean](https://github.com/vprover/vamplean) is fetched from
unmodified upstream source; it is not vendored in this repository. The patched
Vampire source, patch order and binary identity are controlled by
[toolchain.lock.json](toolchain.lock.json) and
[toolchain/leancheck-vampire/](toolchain/leancheck-vampire/). The build script
places the solver under `toolchain/build/` and checks its source, patches,
version and binary SHA-256. The recorded binary environments are **Linux x86_64
with GCC 11.5.0 (Red Hat 11.5.0-14)** and **macOS arm64 with Apple clang 17.0.0**
(`clang-1700.6.4.2`). Their CMake versions are 3.31.8 and 4.3.4 respectively.
A different compiler can produce a different binary digest from the same source.

For another compiler environment, run
`python3 scripts/build_leancheck_vampire.py --bootstrap --force --json` to obtain the local
digest, review the receipt, and record it under that platform's
`roles.leancheck_vampire.sha256` entry in `toolchain.lock.json`. Update the
corresponding compiler/build-environment description and retain the receipt.
Then rerun the strict toolchain check. `--force` replaces the generated solver
checkout, so run it only when no job uses that checkout or solver.
`--bootstrap` does not change the lock
and its success is not a passing identity check. This produces a locally pinned
Vampire build: subsequent receipts carry a **different Vampire identity** from
the paper's binary. Keep the source, patch, Lean and other dependency pins
unchanged. The [compiler-specific pin procedure](docs/providers-and-auth.md#vampire-build-environments-and-local-pins)
gives the commands and fields to inspect. The LRAT checker uses CaDiCaL supplied
with the pinned Lean toolchain.

Build the library, worker, all certificate prerequisites and release verifier:

```bash
LEAN_NUM_THREADS=1 scripts/lake_build_watched.sh
LEAN_NUM_THREADS=2 scripts/lake_build_watched.sh \
  fixed_ambient_encoding_worker VampLean \
  Mathlib.Tactic.Linter.UnusedTactic Mathlib.Tactic.Sat.FromLRAT \
  Whiel.Vampire.ClauseProjection Whiel.Vampire.EmptyDomainLRAT \
  Whiel.Synthesis.FrameworkII.FixedAmbient.CertifyJob
cargo build --release --locked --manifest-path whiel_runner/Cargo.toml --bins
```

Use the release `whiel-symbolic` binary for search measurements. The watched
build script polls Lean processes with a default 4 GiB per-process threshold.
Use `LEAN_NUM_THREADS=1` for clean builds and `2` for incremental builds. Avoid
unrelated simultaneous Lean builds: the build watchdog scans Lean processes
across the machine. The certificate commands prepare their prerequisites even
when `--worker` supplies an existing worker.

### Provider CLI setup

The four paper specs start with Codex 0.148.0, GPT-5.5 and medium reasoning.
Install the pinned CLI and catalog, then perform a native login:

```bash
python3 agent_houdini/setup_cli.py --json
python3 agent_houdini/setup_cli.py --verify-only --json
artifacts/provider-cli/0.148.0/x86_64-unknown-linux-musl/codex \
  -c 'cli_auth_credentials_store="file"' login --device-auth
```

The installer downloads and verifies the CLI; it does not log in or call a
model. Login needs an account with access to the selected model. Native
credentials stay local and must not be included in exported results. If using
a different supported CLI installation, change `provider_cli` in a copied spec
or omit it to use `PATH`. The launcher passes model and reasoning-effort strings
through to the provider. Provider availability is determined by the account;
setup does not guarantee access to every model used in the paper. The GPT-6 Astra
escalation requires **Codex CLI 0.154.0**: 0.148.0 rejects that model. Install
0.154.0 separately and select its executable with `provider_cli` in the copied
spec. `setup_cli.py` installs 0.148.0; it has no CLI-version override.

The search sandbox hides the repository, reference answers and previous runs
from the proposer while allowing provider network access. Native login,
credential permissions and the supported Claude alternative are described in
[providers and authentication](docs/providers-and-auth.md).

## Search and paper experiment settings

Run a single input with the Python campaign launcher. Options before `--`
configure the proposer; options after it configure the verifier:

```bash
unset WHIEL_AGENT_SKILLS_FILE WHIEL_AGENT_SKILLS_JSON
python3 -m agent_houdini campaign run \
  --verifier whiel_runner/target/release/whiel-symbolic \
  --provider codex --model gpt-5.5 --reasoning-effort medium \
  --provider-cli artifacts/provider-cli/0.148.0/x86_64-unknown-linux-musl/codex \
  --isolation bwrap --agent-retention all \
  -- --input Example0001 --destination artifacts/campaigns/example0001 \
  --search-limit 600 --workers 4 --retention all --certify never --no-tools
```

This is the paper's plain Whiel interface: proposal submission and verifier
feedback, without optional query tools or skills. Replace `--input Example0001`
with `--all` for the full benchmark, or with a comma-separated list for a subset.
Each input receives its own search budget. `--certify never` records accepted
answers for later certification and keeps certification out of search time.

For structured run records, use an experiment spec. A dry run prints the command
without launching processes or creating output:

```bash
unset WHIEL_AGENT_SKILLS_FILE WHIEL_AGENT_SKILLS_JSON
python3 -m agent_houdini experiment run \
  agent_houdini/experiments/full-benchmark.json --dry-run
python3 -m agent_houdini experiment run \
  agent_houdini/experiments/full-benchmark.json
```

Unlike the single-input example, **the shipped full-benchmark spec enables all
six query tools** and no skills. It therefore selects the Whiel + Tools arm.
It uses GPT-5.5, medium reasoning, a 600-second search allowance per input,
four verifier workers, no iteration cap, full retention and no certification.
The selected `certification_limit_seconds: 1800` is unused when `certify` is
`never`; a later `campaign certify` has its own flags and defaults.

### All shipped experiment specs

| Spec under `agent_houdini/experiments/` | Purpose and settings |
| --- | --- |
| [paper/whiel.json](agent_houdini/experiments/paper/whiel.json) | Paper Whiel arm: no query tools or skills; GPT-5.5 first pass capped at 6 iterations. |
| [paper/whiel-skills.json](agent_houdini/experiments/paper/whiel-skills.json) | Paper Whiel + Skills arm: six skills, no query tools; no iteration cap. |
| [paper/whiel-tools.json](agent_houdini/experiments/paper/whiel-tools.json) | Paper Whiel + Tools arm: six query tools, no skills; GPT-5.5 first pass capped at 6 iterations. |
| [paper/whiel-tools-skills.json](agent_houdini/experiments/paper/whiel-tools-skills.json) | Paper Whiel + Tools + Skills arm: six query tools and six skills; GPT-5.5 first pass capped at 6 iterations. |
| [full-benchmark.json](agent_houdini/experiments/full-benchmark.json) | All 86 inputs, GPT-5.5 medium, tools enabled, no skills; 600 s search, 4 workers, search only. |
| [sample-5.json](agent_houdini/experiments/sample-5.json) | Five inputs: 0001, 0134, 4001, 4041 and 5040; the same model and controls as full-benchmark. |
| [subset-template.json](agent_houdini/experiments/subset-template.json) | Three starter inputs; copy and edit `name` and `inputs` for another subset. Same model and controls. |
| [weak-model-smoke.json](agent_houdini/experiments/weak-model-smoke.json) | Twenty inputs, 600 s, 4 workers, search only. Set `provider`, `model`, `reasoning_effort`, `provider_cli` and `isolation` in a copy before running; the shipped template deliberately omits the model. |
| [replay.json](agent_houdini/experiments/replay.json) | All 86 reference answers, no provider; 600 s, 4 workers, search only. Expected acceptance count: 86. |
| [transcript-replay-template.json](agent_houdini/experiments/transcript-replay-template.json) | Recorded consultation replay, no provider; 90 s safety limit, 4 workers. Replace `transcript` with an exported JSON transcript and set its input list. |
| [full-benchmark-lean-agent.json](agent_houdini/experiments/full-benchmark-lean-agent.json) | Direct Lean configuration: GPT-5.5 medium, `agent_seconds: null`. Use `agent_houdini.lean_baseline`, not `agent_houdini experiment`. |

Copy configurable specs into `artifacts/experiments/` to keep each run's settings
separate. Unknown JSON keys are rejected. Some free-text `notes` in the shipped
specs describe earlier results; they are not the current benchmark verdicts or
acceptance criteria. Read the input records and report for current ground truth.

### Mapping the paper experiments

The four [paper specs](agent_houdini/experiments/paper/) select GPT-5.5 medium,
a 600-second search allowance, four verifier workers, full retention,
`certify: "never"`, and `token_usage: "codex-rollout"`. Their `notes` describe the
paper's fresh-attempt escalation protocol. The generic `full-benchmark.json`
is an uncapped tools-only run; use the dedicated specs for the initial paper
passes.

| Paper configuration | Shipped spec | Optional query tools | Skills | Initial iteration cap |
| --- | --- | --- | --- | --- |
| Whiel | `paper/whiel.json` | No | No | 6 |
| Whiel + Skills | `paper/whiel-skills.json` | No | Six | None |
| Whiel + Tools | `paper/whiel-tools.json` | Six | No | 6 |
| Whiel + Tools + Skills | `paper/whiel-tools-skills.json` | Six | Six | 6 |

Spec paths in this table are relative to `agent_houdini/experiments/`.
The six query tools are `countermodel`, `strongest_refutations`, `history`,
`ledger`, `validate_clauses` and `evaluate_clauses`. Disabling them preserves
proposal submission. Skills are read through `get_skill` from
`agent_houdini/skills/v1`; they do not change the verifier's acceptance rules.
The recorded `neutral-v1` prompt is the **current default** in
[agent_houdini/prompt_assets/](agent_houdini/prompt_assets/), so no selector is
needed. Do not add a `prompt_variant` key: unknown spec keys are rejected.

Run each arm in the following stages, retaining earlier successes:

1. Run its shipped GPT-5.5 spec.
2. For the three capped arms, rerun their failures with GPT-5.5 and
   `iteration_limit: null`. Whiel + Skills already starts uncapped.
3. Rerun remaining failures with `model: "gpt-5.6-sol"`, medium effort and no
   iteration cap.
4. Rerun remaining failures with `model: "gpt-6-astra"`, medium effort and no
   iteration cap. Set `provider_cli` to the separately installed
   `artifacts/provider-cli/0.154.0/x86_64-unknown-linux-musl/codex`, or its local
   repo-relative installation path.

For each later stage, copy the corresponding arm spec into
`artifacts/experiments/`, give it a distinct `name`, set `all_inputs: false`,
and set `inputs` to that arm's remaining canonical IDs (for example,
`["Example0001", "Example0013"]`). Preserve the tools, skills, 600-second
allowance and four workers. **Every stage starts a fresh attempt**, without
carrying prior search state; neither the experiment runner nor pool retries
or escalates automatically. Exclude infrastructure failures from ordinary
unsolved-task selection until their cause is resolved.

| Paper experiment | Reproduction mapping |
| --- | --- |
| RQ1: Whiel versus baselines | `paper/whiel.json`, including the uncapped GPT-5.5 reruns above; Direct Lean uses its separate section below. |
| RQ1: Whiel, one round | Analyze the first completed round of the same Whiel runs. `--iteration-limit 1` is a separate bounded diagnostic, not the paper's retrospective first-round measurement. |
| RQ2: tools and skills | All four paper specs and their GPT-5.5 stages above. |
| RQ3: stronger models | Fresh uncapped Sol and Astra attempts on each arm's remaining failures; cumulative coverage combines the stages. |
| RQ4: task properties | Join the Whiel-arm search results to benchmark tags and prophecy annotations; this is analysis of the preceding runs. |
| RQ5: certification | Certify the saved accepted answers from all four arms with the resource controls below. Reference-answer certification is a separate check. |

For RQ4, the current report marks 42 valid tasks as using prophecy, whereas the
paper's table uses 41. Exact reproduction of that grouping requires the paper's
annotation snapshot, which is not shipped as a separate dataset here.

### Run four tasks concurrently

The paper used four simultaneous tasks, with one spec per case. The shipped
[task-pool scheduler](agent_houdini/experiment_pool.py) uses GNU Parallel to
create those single-input specs and schedule independent campaigns. A campaign
itself processes its inputs sequentially. `workers: 4` controls concurrency
**within one input**: four clause checks, with up to eight Vampire processes
and four Lean workers; pool `--jobs 4` controls the number of simultaneous inputs.

Prepare four separate native logins under `artifacts/provider-auth/whiel-pool`
using the [worker login procedure](#3-log-in), setting `baseline_auth_root` to
that directory. Then preview or launch an arm:

```bash
python3 -m agent_houdini experiment pool \
  agent_houdini/experiments/paper/whiel.json --jobs 4 --dry-run
python3 -m agent_houdini experiment pool \
  agent_houdini/experiments/paper/whiel.json --jobs 4 \
  --auth-root artifacts/provider-auth/whiel-pool
```

The pool clears inherited skill-catalog variables, writes `specs/<ID>.json`
for each input, and waits for cleanup before reusing its slot. Substitute a
copied escalation spec to run a later stage. See the
[experiment guide](agent_houdini/experiments/README.md) for pool outputs,
exit codes, and the token-free concurrency/isolation probe in
[pool_preflight.py](agent_houdini/pool_preflight.py).

### Token metering

All four paper specs and `full-benchmark.json` set
`token_usage: "codex-rollout"`. With Codex, Linux `bwrap`, and full agent
retention, each consultation records observed input, cached-input, output and
reasoning counters in `agent/<ID>/request-N/usage.jsonl` beneath its run.
Each run's `token-usage.json` summarizes these counters, coverage, and an
API-equivalent cost estimate from a dated price snapshot. Pool children each
have their own report.

Only the last cumulative total per consultation is summed. Cached input is
already included in input; reasoning is already included in output. Missing
usage is unknown, not zero, and interrupted consultations may be incomplete.
The estimate is neither a subscription bill nor a quota measurement. Tokens
can still be recorded for GPT-6 Astra, but the current pricing table has no
Astra entry, so its price and cost estimate are null. See the
[token-accounting details](agent_houdini/experiments/README.md#optional-token-and-cost-accounting).

## Token-free replay checks

Both replay routes exercise the real verifier without contacting a model. They
still run Lean and Vampire and need the builds above.

### Reference-answer replay: 86 inputs

```bash
python3 -m agent_houdini experiment run agent_houdini/experiments/replay.json
```

Expected result: **86 accepted inputs** (69 `valid_uncertified`,
17 `invalid_uncertified`) and **exit code 4**. This exit code is deliberate:
all inputs were accepted and certification was disabled. Check the generated
run's `progress.md` and `verifier/summary.json`, rather than treating any nonzero
exit as equivalent. An incomplete input, wrong verdict or fewer than 86 accepted
inputs fails this check. The reference proposer submits the checked-in
`Core.json` or `Counterexample.json` through the normal proposer API.

### Exported-transcript replay and three fidelity checks

A transcript replay repeats each recorded consultation rather than submitting
one final reference answer. First export a finished model-backed harness run
with full retention to a new JSON file. Replace `original_run` with the run to
export:

```bash
original_run=artifacts/runs/REPLACE-WITH-ORIGINAL-RUN
mkdir -p artifacts/transcripts artifacts/experiments
python3 -m agent_houdini export-transcript \
  "$original_run" artifacts/transcripts/original.json
cp agent_houdini/experiments/transcript-replay-template.json \
  artifacts/experiments/transcript-replay.json
```

Edit that copied spec: set `transcript` to
`"artifacts/transcripts/original.json"` and `inputs` to the exported input IDs.
Review the transcript's recorded `controls` and match relevant verifier options
in the replay spec, using `verifier_args` for options without dedicated keys.
Use the **exported JSON file** as replay input and as the original in the
comparison. Do not replay a raw run directory. The template's 90-second search
limit is a safety net for real proof search, not simulated model latency;
raise it to the original allowance if needed for the selected accepted inputs.

```bash
python3 -m agent_houdini experiment run \
  artifacts/experiments/transcript-replay.json --dry-run
python3 -m agent_houdini experiment run \
  artifacts/experiments/transcript-replay.json
```

Set `replay_run` to the directory printed by that command, then compare:

```bash
replay_run=artifacts/runs/REPLACE-WITH-REPLAY-RUN
python3 -m agent_houdini compare-runs \
  artifacts/transcripts/original.json "$replay_run/verifier" --require-all
```

Require `PASS` for all three checks and comparison exit code 0:

1. The same verdict class: accepted valid, accepted invalid, or not accepted.
2. The same accepted invariant clauses and levels, or the same counterexample.
3. The same set of clause/check-kind/level/outcome ledger entries, ignoring
   order, duplicate entries, timing and attempt numbers. Entries inconclusive
   on either side are reported separately as timing differences.

`--require-all` makes a missing input fail comparison. An exhausted transcript
for an unsolved input can finish `incomplete` instead of the original
`search_timeout`; both have the same non-accepted verdict class. Its campaign
exit need not be 4. The three-check comparison determines replay fidelity.

## Certification and shipped proof checks

Certification needs no provider login or model calls. It proves the exact
original Hoare target and audits dependencies. The expected axioms are exactly
`propext`, `Classical.choice` and `Quot.sound`. A Vampire success message or an
`Accepted.json` record alone is not a Lean certificate.

### Certify a search run

Set `run_dir` to a completed experiment's directory:

```bash
run_dir=artifacts/runs/REPLACE-WITH-RUN
whiel_runner/target/release/whiel-symbolic campaign certify \
  --run "$run_dir/verifier" --jobs 1 \
  --certification-limit 300 --certificate-solver-limit 300 --retention all
```

The command consumes each `Accepted.json` and its `Core.json` or
`Counterexample.json`, publishes `Certificate/`, and updates `result.json` and
`summary.json`. It preserves per-job solver profiles from the accepted record,
refuses changed input identities and can resume a partially certified campaign.
`--jobs` counts simultaneous **inputs**; it is not the search `--workers` knob.

RQ5's first pass used **300 seconds per certificate, a 10 GiB RSS guard per
process, 12-core CPU affinity per run, and two runs concurrently** on disjoint
physical cores. It also used a 96 GiB aggregate process-tree RSS guard per run,
a 300-second allowance per Vampire job and 12 internal solver workers. The
available inner parallelism setting is:

```bash
WHIEL_CERTIFICATE_COMPILER=lake WHIEL_CERTIFICATE_CANDIDATE_TIMEOUT_SECONDS=0 \
WHIEL_CERTIFICATE_SOLVER_JOBS=12 \
  whiel_runner/target/release/whiel-symbolic campaign certify \
  --run "$run_dir/verifier" --jobs 1 \
  --certification-limit 300 --certificate-solver-limit 300 --retention all
```

When inner parallelism exceeds one, this command requires `--jobs 1`. Two
concurrent attempts therefore require separately scheduled run directories.
The initial measured pass and extended retries have different settings:

| Setting | Initial pass | Extended retry |
| --- | --- | --- |
| Whole-certificate allowance | `--certification-limit 300` | `--certification-limit 3600` |
| Per-job Vampire allowance | `--certificate-solver-limit 300` | `--certificate-solver-limit 31536000` |
| External per-process RSS cap | 10 GiB | None |
| External aggregate process-tree RSS cap | 96 GiB | 128 GiB |

The long retry solver allowance does not extend its 3,600-second certificate
clock. Preserve the initial pass's records and use a separate copy of the
accepted-run records for extended retries; their outcomes do not belong in the
initial 300-second measurements. Use `taskset` for CPU affinity and the shipped
RSS watcher around two independent `campaign certify --jobs 1` commands for
memory guards and concurrency. The [RQ5 resource recipe](docs/rq5-certification.md)
gives a complete example using standard Linux tools and the existing Python
watcher. `ulimit`/`prlimit` virtual-address-space limits are not substitutes for
the measured per-process RSS guard. The watched Lean build scripts alone do
not impose all these controls.

Bootstrap precedes the per-input certification clock and contributes to
whole-command wall time. The recipe's wrapper records that wall time and
observed RSS; it does not reproduce the paper supervisor's exact sampling
window. Keep those wrapper measurements separate from certificate-phase
measurements when reporting results.

### Build a certificate from a saved answer

For a standalone valid answer:

```bash
whiel_runner/target/release/whiel-symbolic certificate build \
  --input Example0001 --core Benchmark/Example0001/Core.json \
  --destination artifacts/certificates/Example0001/Certificate \
  --profile direct --time-limit-seconds 300
```

For a standalone invalid answer:

```bash
whiel_runner/target/release/whiel-symbolic certificate build \
  --input Example0013 --counterexample Benchmark/Example0013/Counterexample.json \
  --destination artifacts/certificates/Example0013/Certificate
```

Destinations must not exist. These commands use fresh artifact directories;
they do not replace the shipped certificates. `--core` and `--counterexample`
are mutually exclusive. `--time-limit-seconds` is a per-job Vampire limit for
`--core`, not a whole-certificate limit. Standalone `--profile` forces one
profile on all jobs; use `campaign certify` when preserving the search's
recorded profiles matters. Invalidity certification rechecks the concrete
instance in Lean and needs no solver job, although CLI bootstrap still verifies
the pinned toolchain.

### Check the shipped Lean proofs

After the initial library build above, prepare the test imports before running
standalone checks. Then check the placement ledger, registry and both sets of
certificates:

```bash
LEAN_NUM_THREADS=2 scripts/lake_build_watched.sh \
  Whiel.Synthesis.Tests.All Benchmark.Example0001.Certificate.Valid
python3 scripts/place_certificates.py --check
python3 scripts/generate_fixed_ambient_registry.py --check
LEAN_NUM_THREADS=2 scripts/lake_build_watched.sh Benchmark.Certificates
LIMIT_KB=12582912 LEAN_NUM_THREADS=1 \
  scripts/lake_build_watched.sh Benchmark.OutsideLibrary
LEAN_NUM_THREADS=1 scripts/watchdog.sh 4194304 lake env lean \
  Whiel/Synthesis/Tests/FixedAmbientRegistryAxiomAudit.lean
LEAN_NUM_THREADS=1 scripts/watchdog.sh 4194304 lake env lean \
  Whiel/Synthesis/Tests/FixedAmbientRegistryCaseAxiomAudit.lean
```

`--check` validates generated records without regenerating them or measuring
certificate memory. `Benchmark.OutsideLibrary` holds proofs assigned a larger
build allowance: **12 GiB** (`12582912` KiB). Its certificates are as fully
checked as those in `Benchmark.Certificates`. Lake can reuse compiled modules;
for a source check of one shipped certificate, use its file explicitly:

```bash
LEAN_NUM_THREADS=1 scripts/watchdog.sh 12582912 lake env lean \
  Benchmark/Example0134/Certificate/Valid.lean
```

A passing standalone gate is silent. Do not edit an axiom audit to make an
unexpected dependency pass. [Benchmark/CORPUS.md](Benchmark/CORPUS.md) explains
reference answers, certificate placement and the corpus layout.

## Lean coding-agent baseline (Direct Lean)

A coding agent reads a benchmark's Lean Hoare statement, writes a proof, compiles
it and revises it in a bubblewrap sandbox. The supplied experiment configuration
uses **GPT-5.5 medium, no agent time limit, no added runtime memory limit, and a
180-second independent final check**. Lean heartbeats are unlimited. The agent
can finish naturally without finding a proof.

The agent receives the original task, generic Whiel/Databases semantics and proof
lemmas, and Lean's compiler. Reference answers, other tasks, Houdini, synthesis
and preprocessing automation, Vampire, skills and the query API are unavailable.
The exact prompt is in [lean_agent.py](agent_houdini/lean_agent.py).

Run all commands below from the repository root. This baseline runs independently
of the AgentHoudini service and does not require a Vampire executable.

### Published experiment provenance

The paper's **20/86** result used GPT-5.5 medium, four workers, unlimited
agent time, no added runtime memory limit, unlimited Lean heartbeats, and a
180-second final check. The shipped
[full-benchmark-lean-agent.json](agent_houdini/experiments/full-benchmark-lean-agent.json)
matches the recorded configuration in
[experiment-20261001.json](whiel_runner/direct_lean/experiment-20261001.json),
including its configuration digest. `agent_seconds: null` selects unlimited
agent time; `600` is the largest supported finite agent budget, not the limit
used for this row. The provenance file records 20 accepted proofs (4 valid,
16 invalid) and is not itself a runnable spec. The independent acceptance check
verifies the exact goal and proof dependencies, permits ordinary recursive
helpers, and independently rechecks `native_decide` computations.

### 1. Install and build

Use Linux x86_64 with Python 3.11+, Rust supporting edition 2024, elan, GNU
coreutils and the system bubblewrap executable. User/PID namespaces must be enabled.
The Lean version and library dependencies are pinned in the repository.

```bash
bash scripts/setup_nosync.sh
LEAN_NUM_THREADS=1 scripts/watchdog.sh 4194304 lake exe cache get
LEAN_NUM_THREADS=2 scripts/lake_build_watched.sh \
  Whiel.Concrete.Notation Whiel.Hoare.Concrete Benchmark.Inputs
cargo build --locked --manifest-path whiel_runner/direct_lean/Cargo.toml
python3.11 agent_houdini/setup_cli.py --json
```

The installer downloads the native CLI and model catalog used by the supplied
[configuration](agent_houdini/experiments/full-benchmark-lean-agent.json).
It does not log in or call a model. For another supported Linux architecture or
CLI installation, update `provider_cli` and `model_catalog` in that configuration
to your local paths. Keep the checkout at its build location.

### 2. Prepare the benchmark

```bash
mkdir -p artifacts/lean-agent artifacts/runs
python3.11 -m agent_houdini.lean_baseline prepare \
  --checker whiel_runner/direct_lean/target/debug/whiel-direct-lean \
  --bundle artifacts/lean-agent/bundle
```

This prepares all 86 cases and verifies each exported task against its original
`Benchmark/ExampleNNNN/Input.lean`. For a small run, append
`--inputs Example0001 Example0013`. Only the selected cases will run. Each bundle
and run destination must be new; generated bundles are specific to this machine.

After updating the checker, rebuild it with the Cargo command above and prepare
a bundle at a new path. Bundles pin the audit code; an old bundle cannot be reused
with a checker whose audit code has changed. Use the new bundle path in the run
command below.

### 3. Log in

Each concurrent worker uses a separate native login. For four workers:

```bash
baseline_auth_root="artifacts/lean-agent/auth"
mkdir -p "$baseline_auth_root"
chmod 700 "$baseline_auth_root"
for worker in 1 2 3 4; do
  mkdir -p "$baseline_auth_root/worker-$worker"
  chmod 700 "$baseline_auth_root/worker-$worker"
  CODEX_HOME="$(realpath "$baseline_auth_root/worker-$worker")" \
    artifacts/provider-cli/0.148.0/x86_64-unknown-linux-musl/codex \
    -c 'cli_auth_credentials_store="file"' login --device-auth
  chmod 600 "$baseline_auth_root/worker-$worker/auth.json"
done
```

Complete each device login with an account that can use the selected model.
Do not copy a single login file into several worker directories. For one worker,
create only `worker-1` and use `--jobs 1` below.

### 4. Run

First validate the configuration without model calls:

```bash
python3.11 -m agent_houdini.lean_baseline run \
  agent_houdini/experiments/full-benchmark-lean-agent.json \
  --checker whiel_runner/direct_lean/target/debug/whiel-direct-lean \
  --bundle artifacts/lean-agent/bundle \
  --auth-root "$baseline_auth_root" --jobs 4 \
  --out artifacts/runs/lean-agent
```

**Append `--launch` to start the experiment.** Before paid calls, the runner tests
compilation/repair, isolation, cancellation and rejection of `sorry` using a local
fake model service. Each worker also checks its task in the sandbox before its
model call. Up to four cases run concurrently, each with a fresh agent session.

The shipped `agent_houdini/experiments/full-benchmark-lean-agent.json` sets
`agent_seconds` to `null` for the unrestricted experiment. A positive budget up to 600 seconds is also supported; the prompt is
identical. Ctrl-C stops the campaign and cleans up active workers. Proof failures,
missing submissions and final-check timeouts are recorded and dispatch continues;
authentication, native-process or setup failures stop new dispatch. Trials are
never automatically retried or overwritten.

### 5. Read results

```bash
python3.11 -m agent_houdini.lean_baseline summarize artifacts/runs/lean-agent
```

- `summary.json` and `cases.csv`: completion, acceptance counts, durations and
  token totals. A campaign exit code of 0 means every case finished; it does not
  mean every proof succeeded. Exit 2 means incomplete dispatch or infrastructure
  failure.
- `cases/ExampleNNNN/`: exact prompt, tool transcript, saved workspace,
  `response.json`, token usage and `result.json` with independent checker output.
- `run.json`: model, reasoning effort, resource settings and input provenance.

The submission is `Solution.lean` importing `Task`, plus `valid` or
`invalid` in `verdict.txt`, both within the sandbox workspace. Helper declarations are allowed; theorem
`DirectLeanTask.answer` must prove the original `DirectLeanTask.goal` or its
negation. The goal is partial correctness over all instances, not just examples.
Only the final saved files are collected.

Acceptance independently checks the exact goal and proof dependencies. Classical
reasoning and `native_decide` are allowed; native computations are independently
rechecked. This trusts Lean's native compiler/runtime as well as its kernel.
`sorry`, `admit`, unproved custom axioms and changing the target are rejected.

Token records include input, cached input, output and reasoning tokens when
reported; cached/reasoning counts are subsets. Interrupted usage may be incomplete.
All run artifacts stay under ignored `artifacts/`; no results or credentials are
part of the implementation.

## Results, benchmark report and further documentation

An experiment creates `artifacts/runs/<model>-<date>[-<name>]/` and records the
resolved spec, exact command and revision in `run.json`. Use:

```bash
run_dir=artifacts/runs/REPLACE-WITH-RUN
python3 -m agent_houdini experiment report "$run_dir"
```

- `progress.md` / `progress.json`: per-input status, search time and rounds.
- `verifier/summary.json`: campaign acceptance and certification totals;
  `verifier/<ID>/result.json` is the authoritative per-input result.
- `verifier/<ID>/Accepted.json`, `Core.json` or `Counterexample.json`: saved
  search answers; `Certificate/` contains the separately checked proof.
- `examples/<ID>/summary.md` and `rounds.json`: consultations, clauses,
  countermodels and the recorded interaction with the proposer.
- `agent/`: retained prompts and native interaction logs. Keep these local;
  use exported transcripts for replay and sharing.

Search `search_seconds` excludes certification and admission. Per-consultation
`agent_seconds` and `verifier_seconds` in `rounds.json` are timestamp estimates,
not another per-input search timer. Campaign exit 0 means every selected input
was certified; 4 means every input was accepted with certification still
pending; 3 means at least one input was incomplete or failed; 2 means argument
or bootstrap failure; 130 means interruption. Direct Lean has its own exit codes,
as described above. Fresh model runs can differ from the paper's reported counts.

The self-contained [benchmark report](Benchmark/report/) reads only
`Benchmark/`, including input metadata, source references, tags and shipped
certificates. Rebuild its JSON, HTML, sheets and PDF with:

```bash
python3 Benchmark/report/build_report.py
python3 -m unittest discover -s Benchmark/report/tests
```

Use `--no-pdf` on the build command if `pdflatex` is unavailable. The report's
certified status comes from the certificate trees, not a model prediction or a
spec's historical note. See [Benchmark/CORPUS.md](Benchmark/CORPUS.md) for the
86-case inventory and contributor/source conventions.

Further reference:

- [Auditing a certificate](AUDIT.md): exact theorem statements, formalization map and trust boundary.
- [Experiment specs and task pool](agent_houdini/experiments/README.md): paper stages, scheduling and token metering.
- [RQ5 certification resources](docs/rq5-certification.md): CPU affinity, concurrent runs and RSS guards.
- [CLI reference](docs/cli-reference.md): complete command options.
- [Providers and authentication](docs/providers-and-auth.md): setup and sandbox details.
- [Analyst's guide](docs/analysts-guide.md): result schemas and comparisons.
- [Tools and skills](docs/tools-and-skills.md): query tools and invariant tutorials.
- [Proposer API](docs/proposer-api.md): writing a different proposer.
- [Certificate compilation](docs/certificate-compilation.md): proof construction and checking.

## Credits

The Python AgentHoudini package credits **Fangzhu Shen**. Benchmark contributions
are credited per case in `Benchmark/<ID>/Input.lean`; contributors include
Jesse Comer, Fangzhu Shen, Leo Zhang, Mayur Naik, Sudeepa Roy and Val Tannen.
Original problem and system sources are recorded separately in each case's
metadata and the benchmark report. Whiel builds on Lean, Mathlib, Vampire,
VampLean and CaDiCaL.

## Contributing Style

For Lean files in this repository, prefer:

- `namespace`-organization (`Schema`, `Instance`,
  `RelAlg`, etc.).
- Never let a `namespace` cross a major section boundary:
  close it before the next section header, then reopen.
- Do not use one high-level `namespace` to wrap an entire
  file when the file contains section headers.
- Put each section header outside all namespaces; open the
  namespace immediately after the header.
- Put a full empty line between section headers and
  namespace openings, between namespace openings and the
  first declaration, and between the final declaration and
  namespace closings.
- `variable` declarations should be scoped locally to the
  namespace/section where they are used.
- Narrow assumptions (only include the typeclasses
  needed by the local block).
- Do not use `sorry`, `admit`, `classical`,
  `noncomputable`, or `partial`.
- The `partial` prohibition does not apply to notation
  files, where syntax expanders may need Lean metaprogram
  recursion.
- Keep code lines at or below the section-bar width
  (currently 60 characters).
- The standard major-section header format:

```lean
------------------------------------------------------------
-- Section Title
------------------------------------------------------------
```

- Concise comments (`/- ... -/`) on key
  definitions and theorems.
- Prefer plain `/- ... -/` comments over
  `/-- ... -/` doc comments.
- For comments above definitions, use exactly one of:
  - One-line form (if it fits width):
    `/- Short comment. -/`
  - Multi-line form (if it does not fit):
    open/close markers on their own left-aligned lines,
    with content indented one level (i.e., two spaces).

### Naming Conventions

For database formalizations, prefer the following variable names:

- `D`: domain type.
- `A`: relation-name type.
- `F`: function-name type.
- `α`: attribute-name type.
- `Γ Δ Θ`: schemas, with `Γ` usually the ambient or base
  schema and `Δ`/`Θ` for related or extended schemas.
- `Λ`: first-order signatures.
- `X Y Z`: relation symbols, usually as schema members.
- `f g`: function symbols.
- `n m k`: arities or natural-number indices.
- `t u v`: tuples.
- `R S T`: finite relations or sets, by local context.
- `Q`: domain-of-quantification or active-domain-style
  subsets of `D`.
- `C`: finite sets of constants.
- `I J K`: unnamed instances over schemas.
- `M N`: finite structures.
- `e`: relational algebra expressions.
- `q`: RelCalc queries.
- `φ ψ χ`: RelCalc or FOL formulas, and relational
  algebra selection conditions.
- `P`: Datalog programs.
- `r`: Datalog rules.
- `σ τ`: variable assignments.
- `h...`: proof hypotheses, named by content when useful,
  such as `hExt`, `hMem`, or `hAr`.

When more names are needed, add natural-number subscripts,
for example `I₁`, `I₂`, `A₁`, or `A₂`.
Avoid suffixes that duplicate type information already
present in the declaration, such as `IΓ` or `IΔ`; write
`(I : Instance D Γ)` and `(J : Instance D Δ)` instead.

### Top-of-file Specification Notes

For files that define a key language, semantics,
construction, translation, or metatheorem, add a short block
comment after the imports and before the first section
header. This comment should help a reader check the intended
specification and the main correctness path without reading
every construction lemma.

Use the same plain block-comment style as other comments:

```lean
/-
  This file specifies ...

  Key definitions include:
    * `Namespace.Declaration`

  The main construction is:
    * `Namespace.construction`

  Correctness is proven by:
    * `Namespace.theorem_name`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/
```

Guidelines:

- Mention only the declarations that are central to the
  specification or correctness path. Do not list routine
  helper definitions, supporting lemmas, or every theorem in
  the file.
- Top comments should orient readers at a high level, not
  inventory the file. If `Instance.update` is listed, for
  example, assume its local lookup and algebraic lemmas live
  nearby.
- For translation files, call out the main translation
  function or construction, and any key correctness,
  equivalence, preservation, or soundness theorems.
- Complex constructions should be presented with an explicit
  specification of what correctness means and a theorem
  proving that the construction meets that specification.
  Ideally, structure the file as:
  1. specification details;
  2. construction;
  3. proof of correctness.
  This ordering is preferred, not mandatory; use a different
  order when it makes the file easier to read.
- For complex constructions, include a very short
  description of the construction idea in the top comment.
  When possible, reference standard terminology from the
  literature.
- Put declaration names in backticks, including fully
  qualified namespaces when helpful, e.g.
  `` `Program.MinimalModel` `` or
  `` `FOL.Semantics.evalTermList_toList` ``.
- Group declarations by role when that helps readability:
  key definitions, construction, correctness, or key
  theorems.
- It is fine to end with a catch-all sentence saying that
  intervening definitions and lemmas are construction,
  helper, or proof support.
