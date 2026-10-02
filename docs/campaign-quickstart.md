# Run an AgentHoudini campaign

Run these commands from the repository root. First complete the
[toolchain and native login setup](providers-and-auth.md). The Python agent
launcher sends its selected prompt, synthesis feedback and tool responses to
the chosen provider account. Start with a small input; `--all` is an actual
research run.

Analysing a finished campaign for a write-up? Read the
[analyst's guide](analysts-guide.md): what the four measures are, where each
one comes from, how to read the accepted records, and when two runs may be
compared.

## Three things to know before you read a result

1. **The search-time measure is `search_seconds` in each input's
   `result.json`.** The campaign runner measures it, it excludes admission and
   certification, and it is the only figure to report as search time. It is
   also the only per-input time the harness shows: nothing derived from file
   timestamps is rendered anywhere, because a second figure beside this one
   would be read as a rival measure of the same thing.
2. **Exit code 4 is the normal success code of a `--certify never` or
   `--certify deferred` run.** It means every selected input was accepted and
   the accepted ones are still awaiting certification. 0 means every input was
   also certified; 2 is an argument or bootstrap failure, 3 an incomplete or
   failed input, 130 an interruption.
3. **Searching and certifying are two steps, and the run directory travels.**
   A run made with `--certify never` holds everything certification needs, so
   it can be copied to another machine — or simply left until later — and
   finished there with
   `whiel-symbolic campaign certify --run <run>/verifier`.

## Build once

```bash
bash scripts/setup_nosync.sh
LEAN_NUM_THREADS=1 scripts/watchdog.sh 4194304 lake --keep-toolchain update vamp_lean
LEAN_NUM_THREADS=1 scripts/watchdog.sh 4194304 lake exe cache get
python3 scripts/build_leancheck_vampire.py --jobs 2
LEAN_NUM_THREADS=2 scripts/watchdog.sh 4194304 python3 scripts/check_toolchain.py
LEAN_NUM_THREADS=1 scripts/lake_build_watched.sh \
  fixed_ambient_encoding_worker VampLean \
  Mathlib.Tactic.Linter.UnusedTactic Mathlib.Tactic.Sat.FromLRAT \
  Whiel.Synthesis.FrameworkII.FixedAmbient.CertifyJob
CARGO_BUILD_JOBS=2 cargo build --release --manifest-path whiel_runner/Cargo.toml --bins
```

Confirm that `python3` is version 3.10 or newer before starting. The cache
fetch avoids compiling Mathlib from source; see the
[Linux cache remedies](providers-and-auth.md#mathlib-cache-on-linux) for CA-bundle
or open-file-limit errors. One Lean thread is used for the initial build;
incremental builds may use two. The solver builder captures its output until
completion, so a fresh build may be silent for 10--20 minutes.

VampLean is an upstream Lake dependency. Keep `--keep-toolchain` when resolving
it so upstream's newer Lean declaration does not upgrade Whiel's pinned Lean
version. The existing Vampire binary and both local patches remain pinned.

Campaigns build the release verifier: a debug build makes every clause check
about three times slower, and `cargo test` is what still uses the debug build.

Use the watched build script, not bare `lake build`. A fresh Linux machine
needs reviewed native toolchain hashes first; see the
[Linux solver setup](providers-and-auth.md#vampire-build-environments-and-local-pins).
The campaign and standalone certificate commands prepare the same certificate
prerequisites automatically, including when an existing worker is supplied.
Building them here moves that cost into setup and makes startup failures easier
to distinguish from synthesis failures.

Retain the full checkout for verifier tools and inputs. Rust B owns Houdini,
queries and certification; Python C owns native agents, prompts, sessions,
MCP and sandboxing. Editing C does not require a Cargo rebuild. Native tools
invoke C's Python MCP relay; B communicates only through the generic proposer
API. Optional Linux confinement mounts only the exact interpreter/relay and
other required resources, with no broad C or repository mount.

## Check the command without a model

```bash
whiel_runner/target/release/whiel-symbolic campaign run --help
whiel_runner/target/release/whiel-symbolic campaign run --input Example0001 \
  --no-proposer --iteration-limit 1 --search-limit 5 --certification-limit 5
```

The no-model run is a diagnostic, not a proof attempt: incomplete output and
exit code 3 are expected. It still uses the real input admission and controller.
Both help and `--no-proposer` avoid starting a proposer process. B requires
`--proposer-executable` or `--no-proposer`; it has no default agent.

## Run one input

```bash
python3 -m agent_houdini campaign run \
  --verifier "$PWD/whiel_runner/target/release/whiel-symbolic" \
  --provider codex --model <model> \
  -- --repo "$PWD" --input Example0001
```

`--model` is required and has no default: give the exact model string your
provider CLI accepts. `--reasoning-effort` is optional and is passed through
unchanged. C defaults to the Codex provider and local execution. B defaults to
600 seconds of search and a separate 600 seconds for certification per input;
its default `--workers` is derived from the machine alone, `floor(cores / 2)`
clamped to 1..4, so pass an explicit `--workers N` to keep concurrency fixed.
Compare search times on the same machine under similar load; matching worker
counts and other controls does not make timings interchangeable across hosts.
See [settings and comparability](analysts-guide.md#4-settings-and-comparability).
No bubblewrap is required for local mode. To select the native Claude adapter:

```bash
python3 -m agent_houdini campaign run \
  --verifier "$PWD/whiel_runner/target/release/whiel-symbolic" \
  --provider claude --model <model> --reasoning-effort medium \
  -- --repo "$PWD" --input Example0001
```

Claude requires its own native login; any installed CLI version is accepted and
the reported version is recorded as provenance only. A collaborator may begin with `--iteration-limit 1 --search-limit 90
--certification-limit 120`; this bounds exploration, not model cost or success.

C options precede the first `--`; opaque B campaign options follow it. C
validates native configuration and resolves the provider CLI before invoking B. B neither calls C's configuration helper nor
interprets native options. The launcher prints its private C log directory;
B prints its separate campaign output directory. See the
[CLI reference](cli-reference.md#agenthoudini-launcher).

## Run a subset or all current inputs

```bash
python3 -m agent_houdini campaign run \
  --verifier "$PWD/whiel_runner/target/release/whiel-symbolic" \
  -- --repo "$PWD" --input 0001,0013 --destination artifacts/my-first-campaign
python3 -m agent_houdini campaign run \
  --verifier "$PWD/whiel_runner/target/release/whiel-symbolic" \
  -- --repo "$PWD" --all
```

Use a fresh destination each time. Inputs are discovered from immediate current
`Benchmark` directories, not a fixed list. Inputs run
sequentially: the next input starts only after the preceding input finishes
search, certification (when applicable), and joined cleanup. `--workers N` sets
the clause checks one input may have in flight at once, not the number of
simultaneous model accounts or input campaigns. Every other concurrency budget
is derived from N and recorded in `campaign-settings.json` under
`controls.budgets`. Neither memory nor the core count caps the default: it is
`floor(cores / 2)`, at least 1 and at most 4, whatever this machine's memory
holds — the verifier is fast relative to the proposer, so a default must not
claim a large machine. A check still costs one Vampire process per lane, each
with a planned footprint, so the run's output warns, without narrowing
anything, when the effective checks exceed what the machine's memory is
estimated to hold, and separately when `checks x lanes` exceeds the machine's
own logical cores. Every check
races a proof lane against a finite-model lane, so a check takes two Vampire
processes and a clause that is not inductive comes back refuted with a
Lean-validated countermodel rather than merely unproved. On a machine with at
least 8 logical cores the default equals 4, the same `workers: 4` the shipped
experiment specs set explicitly, so a smaller machine still runs the same
configuration, with a warning rather than a silent narrowing. See
[derived concurrency budgets](cli-reference.md#derived-concurrency-budgets).
Numeric
`0001` and `1` both resolve to `Example0001`; exact current IDs also work.
A number never selects an ID whose suffix carries a letter; pass that exact ID.

## Search now, certify later

Certification is deterministic, consults no model and costs minutes and
gigabytes per input. For a long campaign, keep it out of the search:

```bash
python3 -m agent_houdini campaign run \
  --verifier "$PWD/whiel_runner/target/release/whiel-symbolic" \
  -- --repo "$PWD" --all --certify never --destination artifacts/searched
whiel-symbolic campaign certify --repo "$PWD" --run artifacts/searched
```

`--certify deferred` does both in one command: every input is searched, then one
certification phase runs over the whole run directory. In every mode, including
the default `inline`, each accepted input's record (`Core.json` or
`Counterexample.json`) and its `Accepted.json` envelope are written the moment
the untrusted verifier accepts, so a certification that fails or times out no
longer loses the result.

Until an accepted input is certified its status reads `valid_uncertified` or
`invalid_uncertified`, `summary.json` reports `all_accepted` without
`all_certified`, and the command exits **4** — its own code, distinct from 0,
3 and 130, so no script can read an uncertified run as a certified one.
`campaign certify` is idempotent and resumable, takes `--jobs` and
`--retention`, and refuses an input whose declarations changed since it was
accepted. Run standalone like this, it also runs under the workspace guard the
run itself needed: an omitted `--workspace-*`/`--minimum-free-bytes` flag
adopts the run's own recorded limit rather than `campaign certify`'s own small
`certificate-only` default, so a run made with `--retention all` (as above)
certifies under the same raised allowance it searched under. See
[the CLI reference](cli-reference.md#campaign-certify) for the exact rule.

The run directory is self-contained: it can be copied or moved to another
machine with the checkout and certified there, days later, without repeating
the search or consulting any model. `--run` takes the campaign destination,
which inside an experiment run directory is its `verifier/` subdirectory.

## Run an experiment from a spec file

```bash
python3 -m agent_houdini experiment run agent_houdini/experiments/subset-template.json
```

The spec names the inputs, provider, model, isolation and limits; the command
puts B's destination, C's logs, the resolved spec, the exact command and a
readable digest (`progress.md`, `examples/<ID>/summary.md`) together under one
`artifacts/runs/<model>-<date>[-<name>]/` directory. `experiment report DIR`
rewrites the digest for a running or finished run. The spec files that ship
with the repository are listed in
[experiments/README.md](../agent_houdini/experiments/README.md); see also the
[C README](../agent_houdini/README.md#experiments).

## Check the pipeline without a model

`agent_houdini/tests/replay_proposer.py` is a generic wire-3 proposer that
consults nothing: for each input it submits the answer the repository already
records (`Benchmark/<ID>/Core.json`, or `Benchmark/<ID>/Counterexample.json`
for an invalid case) through the same proposal channel an agent uses, so the
untrusted verifier does exactly the work it would do for an agent that answered
correctly on its first consultation.

```bash
python3 -m agent_houdini experiment run agent_houdini/experiments/replay.json
```

or, without the harness, straight to B:

```bash
whiel_runner/target/release/whiel-symbolic campaign run \
  --repo "$PWD" \
  --proposer-executable "$(command -v python3)" \
  --proposer-arg "$PWD/agent_houdini/tests/replay_proposer.py" \
  --proposer-arg --repo --proposer-arg "$PWD" \
  --input Example0001,Example0013 --destination artifacts/replay-check \
  --workers 4 --search-limit 600 --certify never --retention all
```

The expected outcome over the solved corpus is that **every solved case is
accepted**: `valid_uncertified` or `invalid_uncertified` in each
`result.json`, `all_accepted` in `summary.json`, exit code 4. Any rejection, or
any input whose search reaches its limit, is a verifier incompleteness defect —
the answer was right and already published, so nothing about the proposal can
be at fault. An input with neither record has nothing to replay; the proposer
declines and B ends that input at once rather than holding the search open.
See [the harness README](../agent_houdini/README.md#the-replay-proposer).

## Inspect the outcome

Read `<destination>/campaign-settings.json` for resolved controls and inputs,
`resource-limits.json` for operational allowances, then `summary.json` and each
`<ID>/result.json`. The summary records selected and unrun inputs if a resource
guard or interruption stops the campaign early, and answers separately whether
every search reached a verdict (`all_accepted`) and whether every verdict was
certified (`all_certified`).
A `valid` or `invalid` result includes a published `Certificate/` checked against
the exact input and allowed axioms. `invalid` also supplies a checked
`Counterexample.json`. A solver success, model tool call, submission acknowledgment,
Core file, or search timeout alone is not a certificate.

See [results and troubleshooting](results-and-troubleshooting.md) before
rerunning failures, and the [full reference](cli-reference.md) before changing
limits. A proof-lane launch escalates into the `casc_2025` portfolio by default
(`--casc-portfolio off` for a direct-only run); C owns its session policy.
`campaign-settings.json`, `summary.json` and each `result.json` use schema 3
and describe verifier controls and the opaque endpoint selection;
`resource-limits.json` keeps its own schema 2. Native identity, prompt/source/command provenance and agent limits
are recorded separately in C's bounded logs.

## Sharing a campaign with a collaborator

Run one campaign with `retention: all` and `agent_retention: all` (every spec
under [`experiments/`](../agent_houdini/experiments/README.md) already sets
these), then freeze its transcript into one small file:

```bash
python3 -m agent_houdini export-transcript artifacts/runs/<run> transcript.json
```

This is the file to send: the run's own recorded verifier controls, its
`provider`/`model`/`reasoning_effort`, and, per input, every consultation's
own submission in round order and the record a replay is checked against
(verdict class and status, the accepted Core with levels or the
counterexample instance, the attempt ledger). No path, prompt, MCP exchange,
provider stream or solver output is in it -- there is nothing left to strip.
A collaborator replays it (below) and checks their replay against it with
`compare-runs`, without ever needing the run directory itself.

### Replaying a transcript

`agent_houdini/tests/replay_proposer.py` normally submits the repository's
own recorded answer for each input (see
[the replay proposer](../agent_houdini/README.md#the-replay-proposer)). Given
`--transcript PATH`, naming a transcript file (the one `export-transcript`
wrote you) or a retained run directory instead, it replays that transcript's
own recorded responses: for each input, consultation *N* answers with the
content the original proposer submitted at its own consultation *N*,
re-bound to the new run so the live verifier accepts it, including a
response that was malformed in the original run, so the verifier's handling
of it is exercised again.

A consultation the transcript has nothing recorded for, and the end of the
transcript, both **end the search at once by closing the connection**,
rather than declining (which the verifier does not treat as ending the
input -- it opens a fresh consultation on the same exhausted input instead,
which used to spin, measured directly against the real verifier, into tens
of thousands of consultations within a search limit of tens of seconds) or
holding the request open (which avoids the spin but just idles out the
search limit). The verifier reads the closed connection as its endpoint
having exited, ends the input at once -- on the order of ten milliseconds,
measured -- as `incomplete`/`InfrastructureFailure`, and proceeds to the next
input normally. That is a different word from the original run's own ending
(`search_timeout` for a genuinely non-accepted input), which is why
`compare-runs` (below) treats every non-accepted status as one class rather
than the exact word.

Because a transcript replay pays no model latency, give it a short search
limit anyway, as a plain safety net: `search_limit_seconds: 90` is
comfortably above what an *accepted* input's own real proof search needs
(the verifier's own share of a consultation round, typically seconds) and far
below the 600 seconds a real model's campaign uses.
[`agent_houdini/experiments/transcript-replay-template.json`](../agent_houdini/experiments/transcript-replay-template.json)
is a starting point: fill in `transcript` and `inputs` and run it as any
other spec.

```bash
python3 -m agent_houdini experiment run agent_houdini/experiments/replay.json
```

with `"transcript": "<path to transcript.json or a retained run>"` and
`"search_limit_seconds": 90` added to a copy of the spec (or any spec with
`"proposer": "replay"`), or, without the harness, straight to B:

```bash
whiel_runner/target/release/whiel-symbolic campaign run \
  --repo "$PWD" \
  --proposer-executable "$(command -v python3)" \
  --proposer-arg "$PWD/agent_houdini/tests/replay_proposer.py" \
  --proposer-arg --repo --proposer-arg "$PWD" \
  --proposer-arg --transcript --proposer-arg /path/to/transcript.json \
  --input Example0001 --destination artifacts/transcript-check \
  --workers 4 --search-limit 90 --certify never --retention all
```

This is token-free like the ordinary replay proposer, and it is the way to
reproduce, or debug, a real campaign's outcome without paying for the model
again.

### Checking a replay against the transcript it was replayed from

```bash
python3 -m agent_houdini compare-runs transcript.json artifacts/runs/<replay>
```

reports three named checks -- verdict class, the accepted Core/counterexample,
and the attempt ledger -- PASS or FAIL with the specific differences listed,
and exits 0 only if every check passes. See
[`compare-runs`](../agent_houdini/README.md#comparing-an-original-and-a-replay)
for what each check compares, `--require-all`/`--expect-different` and the
`--json` machine-readable report. `ORIGINAL` may equally be a run directory
or a bare verifier destination, so the same command also checks two live
campaigns of the same inputs against each other, not only a transcript
replay.

### The whole run directory, when a transcript file is not enough

`export-run` copies the whole run directory instead of freezing a transcript
-- every prompt, every MCP exchange, the clause ledger's own artifact files
-- for the rare case a collaborator needs to read all of that, not just
replay and compare:

```bash
python3 -m agent_houdini export-run artifacts/runs/<run> <destination>
```

This copies the run directory to `<destination>`, leaving out every
`native-*` file and refusing to leave `<destination>` in place if anything it
copied still carries this machine's own layout -- the account's user name,
its home directory, a temp-directory path or the machine's host name. A
refusal prints every hit, file and line or byte offset, so it can be fixed at
the source rather than worked around. `python3 -m agent_houdini export-run
--check-only artifacts/runs/<run>` runs the same check in place, without
copying anything, so you can see what would block an export before making
one.

`native-*` files (`native-stdout.jsonl`, `native-stderr.txt`,
`native-debug.txt`, one triple per consultation under
`agent/<ID>/request-N/`) are the raw provider CLI streams: local debugging
material for the person who ran the campaign, and never published or sent
anywhere. Everything a collaborator needs to read the run -- results,
certificates, the clause ledger, prompts, submissions and MCP traffic -- is
in the files the export keeps. Send the exported directory as it stands;
nothing further needs stripping.
