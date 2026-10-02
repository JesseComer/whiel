# Experiment specs

One JSON file per experiment, read by

```sh
python3 -m agent_houdini experiment run agent_houdini/experiments/<spec>.json
```

The command creates one run directory, `<output_root>/<model>-<YYYYMMDD>[-<name>]/`
(a `-2`, `-3` suffix when the name is taken), records the resolved spec and the
exact launcher command in its `run.json`, starts the campaign with the
verifier's destination at `verifier/` and the agent logs at `agent/`, and when
the campaign has ended writes `progress.md` (one row per input) and
`examples/<ID>/summary.md` (that input's consultations, submitted clauses, the
verifier's clause ledger, countermodels and file locations), next to links to
the input's `verifier/<ID>` and `agent/<ID>` directories.

`python3 -m agent_houdini experiment report <run-dir>` rewrites the digest at
any time, including while the campaign is still running. Given an older
campaign directory (`artifacts/campaigns/<name>`) it builds
`artifacts/runs/<name>` with links to that directory and to its
`artifacts/agent-logs/<name>` sibling, then writes the same digest there.

## Four concurrent Whiel searches

The paper ran four tasks concurrently, using one spec per case. The shipped
scheduler, `agent_houdini/experiment_pool.py`, uses GNU Parallel to run one
independent campaign per input, with a separate generated spec for each case. Install GNU Parallel and complete
the normal [campaign setup](../../docs/campaign-quickstart.md) first. The native
pool supports Codex with `bwrap` isolation and requires `certify: "never"`.

Each slot needs a separately logged-in native home under a private directory:
`worker-1/auth.json` through `worker-4/auth.json`. Use the native CLI's file-backed
login with `CODEX_HOME` set to each worker directory; directories must have mode
`0700` and login files `0600`. The [worker login example](../../README.md#3-log-in)
shows the commands; set `baseline_auth_root` to the pool auth directory.
Do not copy one login file into multiple slots.
For the commands below, use `artifacts/provider-auth/whiel-pool` as that root.

```bash
python3.11 -m agent_houdini experiment pool \
  agent_houdini/experiments/paper/whiel.json --jobs 4 --dry-run

python3.11 -m agent_houdini experiment pool \
  agent_houdini/experiments/paper/whiel.json --jobs 4 \
  --auth-root artifacts/provider-auth/whiel-pool
```

Use `--parallel` to select another GNU Parallel executable if needed. The first
command only displays the queue; the second launches model calls. `--jobs 4`
means four cases at a time. The spec's `workers` field independently controls
verifier concurrency within each case; all other spec settings are preserved.

The pool writes `specs/<ID>.json`, `records/<ID>.json`, `logs/<ID>.log`,
`cases/<ID>/<run>/`, `pool.json`, `progress.md`, and GNU Parallel's `joblog.tsv`.
A slot is reused after the child campaign finishes cleanup and reporting.
Accepted searches, search timeouts and iteration exhaustion allow the queue to
continue; infrastructure or resource failures stop dispatch. There are no
automatic retries. Ctrl-C stops dispatch and drains running jobs. Exit 4 means
all searches were accepted, 3 includes unsuccessful or stopped searches, and
130 indicates interruption; inspect `pool.json` for the distinction.

Run the real concurrency/isolation probe without model calls:

```bash
python3.11 -m agent_houdini.pool_preflight check "$(command -v parallel)"
```

It uses eight synthetic jobs to check four overlapping workers, immediate slot
refill, private login mounts, hidden sibling workspaces and released auth locks.

## Shared prompt

The current default prompt in `agent_houdini/prompt_assets/` uses the wording
from the recorded `neutral-v1` experiments. No prompt selector is needed.
For historical specs containing
`prompt_variant: "neutral-v1"`, remove that key; unknown spec keys are rejected.
Saved run prompts remain the record of what historical agents received.

## Spec fields

| Key | Meaning | Default |
| --- | --- | --- |
| `name` | suffix of the run directory name | none |
| `notes` | free text, copied into `run.json` and `progress.md` | `""` |
| `proposer` | `agent` runs the C launcher against a provider; `replay` runs the token-free replay proposer, which consults nothing and so takes none of the provider, model, isolation, skill or agent keys | `agent` |
| `transcript` | `replay` proposer only: an `export-transcript` JSON file (see [collaborator transcript replay](../../docs/campaign-quickstart.md#replaying-a-transcript)) whose own recorded responses are replayed consultation by consultation, instead of the repository's single recorded Core/Counterexample answer; relative to `repo` | none (the repository's own recorded answer) |
| `answers` | `replay` proposer only: a directory of recorded answers to replay instead of the repository's own `Benchmark/` — `<directory>/<ID>/Core.json` or `Counterexample.json`. A campaign's verifier destination has this shape, and a harness run directory is read through its `verifier/`, so this replays the answers an earlier run accepted (an *answer replay* of that run); not together with `transcript`; relative to `repo` | none (`Benchmark/`) |
| `provider`, `model`, `reasoning_effort` | passed to the provider CLI verbatim; `model` is required | `codex`, —, none |
| `provider_cli` | explicit CLI executable, relative to `repo` | resolved from `PATH` |
| `isolation` | `bwrap` or `local` | `bwrap` |
| `inputs` / `all_inputs` | the inputs, as `--input` accepts them (`Example0001`, `0001`, `1`), or every current input | — |
| `repo` | the checkout holding `Benchmark/` and the pinned tools | the checkout containing `agent_houdini/` |
| `verifier` | the `whiel-symbolic` executable, relative to `repo` | `whiel_runner/target/release/whiel-symbolic` |
| `output_root` | where run directories are made, relative to `repo` | `artifacts/runs` |
| `search_limit_seconds`, `certification_limit_seconds`, `consultation_limit_seconds`, `iteration_limit`, `workers` | the verifier's limits | the verifier's defaults (600 s, 600 s, none, none, and `workers` = `floor(cores / 2)` clamped to 1..4) |
| `retention` | the verifier's `--retention`; `all` keeps the ledger and the consultation records the digest reads | `all` |
| `certify` | the verifier's `--certify`: `inline`, `deferred` or `never`. Prefer `deferred` for a large campaign: every search finishes first and one certification phase follows, so the agents are not paid for while a deterministic build runs. `never` leaves the run directory for `campaign certify --run <run>/verifier` later, possibly on another machine | `inline` |
| `agent_retention` | C's `--agent-retention`; `all` keeps prompts, CLI streams, MCP traffic and submissions | `all` |
| `token_usage` | `off` or `codex-rollout`; the latter retains observed token counters and writes an API-equivalent cost report; requires Codex, Linux `bwrap`, and `agent_retention: all` | `off` |
| `agent_thinking_tokens` | Claude only: the per-turn thinking cap | none |
| `skills_dir` | a skill library directory (`index.json` plus one Markdown file per skill, see `agent_houdini/skills/v1/`) served through `get_skill` and listed in the prompt; relative to `repo`. Absent means no skills: the ablation baseline | none |
| `skills_file` | the older single-JSON-file catalog for `get_skill`; exclusive with `skills_dir` | none |
| `verifier_args`, `agent_args` | further raw arguments for B (after `--`) and for C (before it) | `[]` |

An unknown key is refused, so a misspelled limit cannot silently fall back to a
default. `--dry-run` prints the run directory and the command without creating
either.

## The specs that ship here

All 86 reference answers are certified: 69 valid and 17 invalid. The `notes`
in `full-benchmark.json` describe one past search run, not the benchmark's
verdicts or its current certification status.

| Spec | What it runs |
| --- | --- |
| `paper/whiel.json` | Whiel: no query tools or skills; GPT-5.5 first pass capped at 6 iterations |
| `paper/whiel-skills.json` | Whiel + Skills: six skills, no query tools; no iteration cap |
| `paper/whiel-tools.json` | Whiel + Tools: six query tools, no skills; GPT-5.5 first pass capped at 6 iterations |
| `paper/whiel-tools-skills.json` | Whiel + Tools + Skills: six query tools and six skills; GPT-5.5 first pass capped at 6 iterations |
| `full-benchmark-lean-agent.json` | Direct Lean: use `agent_houdini.lean_baseline`; unlimited agent time (`agent_seconds: null`), matching the recorded 20/86 paper run |
| `full-benchmark.json` | every current input (`all_inputs: true`): 86 of them, 69 valid and 17 invalid, all with certified reference answers |
| `sample-5.json` | five inputs, four valid and one invalid |
| `subset-template.json` | a starting point for a partial run; edit `inputs` and `name` |
| `weak-model-smoke.json` | twenty inputs (15 valid, 5 invalid), all with certified reference answers; a model template with no model selected, so fill in `provider` and `model` first |
| `replay.json` | all 86 inputs through the token-free replay proposer, with no model at all — every one now carries a recorded answer |
| `transcript-replay-template.json` | a starting point for replaying an `export-transcript` JSON file (see [collaborator transcript replay](../../docs/campaign-quickstart.md#replaying-a-transcript)); edit `transcript` and `inputs`. Its 90-second `search_limit_seconds` is a safety net, not a target — a transcript replay pays no model latency, so a non-accepted input ends `incomplete` within a couple of seconds by closing the connection, well under the limit, and the limit mainly bounds an *accepted* input's own real proof search |

## Paper stages and subsets

The four paper specs start with GPT-5.5 medium, Codex CLI 0.148.0, a
600-second search budget, four verifier workers, full retention,
`certify: "never"`, and `token_usage: "codex-rollout"`. Their `notes` record
this escalation sequence:

1. Run the shipped GPT-5.5 pass. Three arms have `iteration_limit: 6`;
   `whiel-skills.json` is uncapped.
2. Rerun failures of the capped arms with GPT-5.5 and `iteration_limit: null`.
3. Rerun remaining failures with `model: "gpt-5.6-sol"`, medium effort,
   and no iteration cap.
4. Rerun remaining failures with `model: "gpt-6-astra"`, medium effort,
   and no iteration cap. This stage needs Codex CLI **0.154.0** because
   0.148.0 rejects the model. Install it separately and select it with
   `provider_cli`; the path recorded in the specs is
   `artifacts/provider-cli/0.154.0/x86_64-unknown-linux-musl/codex`.
   `agent_houdini/setup_cli.py` only installs 0.148.0.

Copy each arm spec into `artifacts/experiments/` for a later stage. Give it a
new `name`, set `all_inputs: false`, and populate `inputs` with that arm's
remaining canonical IDs, such as `Example0001`. Keep its tool/skill settings,
600-second allowance and four workers. The pool rejects numeric aliases and
specs that combine `all_inputs: true` with a nonempty `inputs` list. It has no
model or input override flags: edit the copied spec.

Every stage starts fresh, without previous search state. Retain earlier
successes for cumulative coverage; there are no automatic retries. The pool
clears both `WHIEL_AGENT_SKILLS_FILE` and `WHIEL_AGENT_SKILLS_JSON`. When using
ordinary `experiment run` or `campaign run` directly, unset both variables to
prevent an inherited skill catalog changing a no-skills arm.

## The proof lane's two strategies

No spec here names a key for it, because every spec uses the verifier's own
defaults: a proof-lane launch runs the direct strategy first, under a prefix
cutoff, and escalates into the `casc_2025` portfolio for the rest of its
allowance when direct does not settle the condition. The two shares that divide
a launch are `--proof-casc-share` (0.25, the portfolio's share of the 30-second
baseline every launch keeps) and `--proof-casc-retry-share` (0.75, its share of
the time a retry adds beyond that baseline), and `--casc-portfolio off` removes
the second stage entirely. An experiment that wants any of these passes them
through `verifier_args`; the run's `campaign-settings.json` records the policy
and both shares either way, and two runs whose settings differ here are not
comparable. `docs/cli-reference.md` states the resulting per-launch schedule.

The model-driven search specs share these controls: `workers: 4` (4 clause
checks, so up to 8 solver processes), `search_limit_seconds: 600`, `retention: all`,
`agent_retention: all` and `certify: "never"`. On a machine with at least 8
logical cores, 4 is also the verifier's own default, so the specs set it
explicitly only so a smaller machine still runs the same configuration
(with a warning, rather than a silent narrowing). A collaborator's campaign
stops at acceptance; certification is a separate later step,
`whiel-symbolic campaign certify --run <run>/verifier`, which needs no model
and can run on another machine. Copy a spec for a new experiment and change the
inputs, the model and the limits.

The generic search specs have no iteration cap; the paper specs use the
first-pass caps described above. `iteration_limit: null` (or omitting that
key) leaves `--iteration-limit` out of the command. Search is
still bounded by the 600-second search budget and the other resource guards.
An explicit positive `iteration_limit` remains available for bounded diagnostics;
historical run records retain the limits used when those runs were launched.

`retention: all` itself now raises the campaign-wide workspace guard, so no
spec here needs `verifier_args` for it: `--workspace-bytes`, `--workspace-files`,
`--workspace-entries` and `--workspace-directories` each take a larger default
whenever the run has no explicit flag of its own for that limit. That guard
counts **the whole campaign's** retained material, not one input's, so under
`retention: all` every earlier input's ledger, consultation records and
artifacts are still on the count when a later input runs; at the ordinary
per-input allowances a long run would stop partway through against its
predecessors' residue rather than anything the current input did. An
experiment that wants a different limit still sets it through `verifier_args`,
and that explicit value wins over the raised default. `--minimum-free-bytes` is
left at its default so a genuinely full disk still ends the run.

`replay.json` is not a research run: it is the pipeline check described in
[the harness README](../README.md#the-replay-proposer). Its expected outcome is
that every one of its inputs is accepted and the command exits 4; any rejection
or timed-out search is a verifier incompleteness defect.

## Reading results

A finished (or still running) experiment produces:

```
artifacts/runs/<model>-<YYYYMMDD>[-<name>]/
├── run.json                       resolved spec, exact command, git revision, timing, exit code
├── progress.md                    one row per input: status, rounds, proposed/dropped, Core/pending/dead, search time
├── progress.json                  machine-readable version of progress.md, with per-round detail
├── launcher.log                   combined stdout/stderr of the campaign
├── verifier/<ID>/                 B's output: result.json, Certificate/, artifacts/
├── agent/<ID>/                    C's logs: events.jsonl, request-N/{prompt.txt, submissions.jsonl, ...}
└── examples/<ID>/                 per-input digest
    ├── summary.md                 each consultation's push state, agent messages, clause ledger, countermodels
    ├── rounds.json                per-round breakdown: agent/verifier split, proposed/dropped, core/pending counts
    ├── agent -> ../../agent/<ID>
    └── verifier -> ../../verifier/<ID>
```

Start with `progress.md` for the overview, then open `examples/<ID>/summary.md`
for a specific input's detail. `rounds.json` is for scripts and analysis —
it carries the same per-round data in machine-readable form.

### The two kinds of time

`search` in `progress.md` and `search_seconds` in `rounds.json` are the
verifier's own measurement of one input's search, and they are the only
per-input time anywhere in the digest.

`agent_seconds` and `verifier_seconds` in each round of `rounds.json` are a
different thing: the split of **one consultation** between the model and the
verifier, which is the only model-versus-verifier division an experiment
records. They are the harness's estimate from its own log file timestamps, not
a measurement either side made — `agent_seconds` spans that consultation's
request records and carries the harness's own overhead with it, and
`verifier_seconds` is the gap to the next request, so it is null on the last
round. Neither is search time and no input total is formed from them; every
`rounds.json` says so in its own `round_seconds_meaning`.

## Regenerating the digest mid-run

The digest (`progress.md`, `progress.json` and every `examples/<ID>/summary.md`
and `rounds.json`) can be rewritten at any time, including while the campaign is
still running:

```sh
python3 -m agent_houdini experiment report <run-dir>
```

This reads the current state of the verifier and agent logs and regenerates all
digest files in place. Run it whenever you want an up-to-date snapshot without
waiting for the campaign to finish.

## Optional token and cost accounting

All four `paper/*.json` specs and `full-benchmark.json` enable token accounting
with `"token_usage": "codex-rollout"`. To enable it in another experiment, add the
same field to that spec. It requires `provider: codex`, Linux `isolation: bwrap`
and `agent_retention: all`. Set `"token_usage": "off"` or omit the field to
disable it.

Follow the normal [campaign quickstart](../../docs/campaign-quickstart.md).
Ensure the spec's `provider_cli` points to your installed Codex, or omit that
field to resolve it from `PATH`. Preview the existing full-benchmark command
without launching a model:

```sh
python3 -m agent_houdini experiment run agent_houdini/experiments/full-benchmark.json --dry-run
```

Remove `--dry-run` to launch. Metering does not change the prompt, model,
effort, tools, search limits or verifier acceptance rules.

Each consultation retains numeric counters in
`agent/<ID>/request-N/usage.jsonl`. At the end of a metered experiment,
`token-usage.json` summarizes observed tokens, coverage and API-equivalent
cost, including the model-specific dated price snapshot. Each pool child
writes its own report. GPT-6 Astra has no entry in the current price table:
its observed tokens are retained, but pricing and cost estimates are null.
Temporary raw rollouts stay in fresh request-local scratch and normal shutdown removes
them; host session history is never mounted.

Only the last cumulative total of each consultation is summed. Cached input
is part of input, and reasoning is part of output: neither is added twice.
The report's `requests` are consultations, not model API requests or Houdini
iterations. Coverage distinguishes `complete`, `partial` and `unknown`;
interrupted responses can leave unreported tokens. Missing usage is unknown,
not zero. Cost is an estimate for observed tokens at the recorded rates, not
a subscription bill or weekly-quota measurement. Unsupported prices remain
null; read coverage and `requests_with_cost_estimate` alongside the total.

Regenerate the report without model calls:

```sh
python3 -m agent_houdini experiment report <run-dir>
python3 -m agent_houdini.token_usage <run-dir> --model <exact-model-used>
```

These commands cannot recover usage that was never recorded. Preserve the
original report for historical pricing; future code may carry different rates.
