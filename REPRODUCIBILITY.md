# Reproducing the paper experiments

The **paper-specific reproduction scripts** run Whiel search, the Direct Lean
baseline, and RQ5 certification with the parameters below. Whiel-OneRound uses
the first round of each Whiel run. Run commands from the repository root. Each
paid experiment or model stage requires its own explicit command.

## Whiel Search

<a id="search-setup"></a>
### Setup

Use Linux x86_64 with the following prerequisites:

- System Python 3.11 or newer, Git, Rust/Cargo, and elan with `lake` on `PATH`.
- C/C++ compiler, CMake and Make; GNU Parallel; bubblewrap with working user
  namespaces; `ps`, `pgrep`, `pkill`, `taskset`, `lscpu` and GNU `timeout`.
- Provider access to GPT-5.5, GPT-5.6 Sol and GPT-6 Astra, with capacity for four
  concurrent tasks.

[toolchain.lock.json](toolchain.lock.json) pins Lean 4.30.0-rc1 and patched
Vampire. The Linux Vampire digest was built with Red Hat GCC 11.5.0 and CMake
3.31.8. Setup requires binaries to match their recorded SHA-256 digests.

```bash
python3 scripts/reproduce_paper.py setup
```

Setup downloads dependencies, builds the patched Vampire and release runner,
and performs watched Lean builds including certificate prerequisites. It makes
no model calls. Lean builds use one thread and a 4 GiB per-process watchdog;
Vampire compilation uses four jobs. Do not overlap another Lean build: the
watchdog detects Lean processes machine-wide.

**Setup installs both required Codex CLI versions locally.** It does not depend
on a globally installed Codex CLI:

| Experiments | CLI version |
| --- | --- |
| GPT-5.5 search, GPT-5.6 Sol escalation, Direct Lean | 0.148.0, verified against the shipped lock |
| GPT-6 Astra escalation | 0.154.0, verified against the official release's archive digest |

Binaries and installation records are saved under `artifacts/provider-cli/`.
Authenticate explicitly before running search:

```bash
python3 scripts/reproduce_paper.py login
```

This uses CLI 0.148.0 to perform native device login for four independent worker
stores under `artifacts/paper-reproduction/auth/`. Follow each displayed login
prompt. Both CLI versions use these stores; existing credentials are reused.

<a id="search-run"></a>
### Run the experiments

The script uses four configurations, with these starting specs:

| Configuration | Spec | Verifier tools | Skills |
| --- | --- | --- | --- |
| Whiel / Base | [whiel.json](agent_houdini/experiments/paper/whiel.json) | No | No |
| Whiel + Skills | [whiel-skills.json](agent_houdini/experiments/paper/whiel-skills.json) | No | Yes (all 6) |
| Whiel + Tools | [whiel-tools.json](agent_houdini/experiments/paper/whiel-tools.json) | Yes | No |
| Whiel + Tools + Skills | [whiel-tools-skills.json](agent_houdini/experiments/paper/whiel-tools-skills.json) | Yes | Yes (all 6) |

Fixed search parameters: medium reasoning, 600 s per attempt including proposer
and verifier, four verifier workers per task, four tasks concurrently, no
iteration or separate consultation cap. The default prompt is `neutral-v1`;
skill arms use `skills_dir="agent_houdini/skills/v1"`. Records use
`retention=all`, `agent_retention=all`, `token_usage=codex-rollout` and
`certify=never`.

> **WARNING: PAID MODEL RUNS.** Each of the following commands makes paid model
> calls. Run only the stages you intend to pay for. Each command runs its named
> model across the four configurations; it does not start the next model.

First run GPT-5.5 on all 86 inputs in each configuration:

```bash
python3 scripts/reproduce_paper.py search gpt-5.5
```

Then explicitly escalate the remaining unsolved inputs to GPT-5.6 Sol:

```bash
python3 scripts/reproduce_paper.py search gpt-5.6-sol
```

Finally, explicitly escalate those still unsolved to GPT-6 Astra:

```bash
python3 scripts/reproduce_paper.py search gpt-6-astra
```

Each escalation starts fresh attempts on its selected subset and retains earlier
successes. Interruptions and infrastructure errors stop that stage; ordinary
search timeouts count as unsolved. Repeating a stage is refused. To start a new
trial while preserving previous records, use `search gpt-5.5 --new`.

<a id="search-results"></a>
### Understanding the results

```bash
python3 scripts/reproduce_paper.py report
```

This makes no model calls. It shows each stage's accepted/total count and
percentage, cumulative coverage per configuration, and paths to raw records.
A stage percentage uses its selected subset; cumulative coverage counts each
input once against all 86. Fresh model responses and costs may differ from the
paper's runs.

Records are under `artifacts/paper-reproduction/`; `current.json` points to the
trial's `manifest.json`. Trial state `ready` means the last command completed and
other experiments await explicit launch; `complete` means Whiel search, Direct
Lean and certification all finished. Failed/interrupted trials retain their
partial records. Setup also uses ignored `.lake/`, Rust target directories and
`toolchain/build/` caches.

| Record | Meaning |
| --- | --- |
| Trial `manifest.json` | Expected inputs, states, resolved specs, commands, source hashes and run paths. |
| Trial `report.md` | Counts and paths printed by `report`; pending experiments are identified. |
| Pool `progress.md` / `pool.json` | Readable and machine-readable case outcomes. |
| Child `verifier/<ID>/result.json` | Authoritative verdict, `search_seconds` and failure details. `valid_uncertified` and `invalid_uncertified` are search successes. |
| Child `examples/<ID>/summary.md` | Submitted answers, verifier consultations and final outcome. |
| Child `agent/<ID>/request-N/` | Provider streams and token records. `codex-rollout` meters provider rollout events; summaries distinguish input, cached input, output and reasoning tokens. Missing measurements are not zero. |

See the [analyst's guide](docs/analysts-guide.md) for field definitions.

## Whiel-OneRound

### Setup

Whiel-OneRound uses only the first round of each Whiel run: one proposal followed
by invariant or counterexample checking, without verifier feedback. Use the
GPT-5.5 records from the plain `whiel` configuration above. RQ2 compares the
first-round results across all four configurations.

### Run the experiments

> **WARNING: GENERATING SEARCH RECORDS USES PAID MODEL RUNS.** If needed, run the
> GPT-5.5 stage in [Whiel Search](#search-run). Once those records exist, this
> comparison requires no additional model calls.

Locate the recorded runs with:

```bash
python3 scripts/reproduce_paper.py report
```

### Understanding the results

Count a first-round success when the final result is accepted and exactly one
verifier consultation completed. Divide by 86 for the baseline success rate.
Use GPT-5.5 records; the Sol and Astra escalations are separate comparisons.

The authoritative `attempt-history` artifact has
`consultations[].outcome="accepted"` for a completed submission or decline;
this field records completion, not the task's final verdict. The existing
`agent_houdini.experiment.read_verifier_input` loader retrieves that artifact,
and `agent_houdini.compare_runs.completed_rounds` counts completed consultations.
An accepted final result is recorded in `verifier/<ID>/result.json`.

`examples/<ID>/summary.md` also displays verifier consultations. Provider request
counts in `rounds.json` can include correction exchanges and are not verifier
round counts. Its per-request time estimates are not authoritative first-round
search times; `result.json.search_seconds` measures the full search.

## Direct Lean

### Setup

Complete the [toolchain installation and device login](#search-setup). Direct
Lean uses CLI 0.148.0 and the same four worker stores. It can run independently
of Whiel search.

### Run the experiments

> **WARNING: PAID MODEL RUNS WITH UNLIMITED AGENT TIME.** This launches GPT-5.5
> for all 86 inputs. The agent has no time budget, so this command has no fixed
> total model cost.

```bash
python3 scripts/reproduce_paper.py direct-lean
```

Fixed parameters come from
[full-benchmark-lean-agent.json](agent_houdini/experiments/full-benchmark-lean-agent.json):
GPT-5.5, medium reasoning, four concurrent tasks, `agent_seconds=null`, unlimited
Lean heartbeats, no added runtime memory guard, a 180 s final check and no
automatic retries. The command uses the current trial, or creates one if none
exists. `direct-lean --new` explicitly creates a fresh trial.

<a id="direct-lean-results"></a>
### Understanding the results

```bash
python3 scripts/reproduce_paper.py report
```

`direct-lean/run/summary.json` contains `proof_checked`, `total`, outcomes and
observed token totals. The success fraction is `proof_checked / total`.

The report also writes `direct-lean-audit.json` in the trial directory. This
reads saved checker receipts and lists each case's axioms and native assertions:

- `accepted_std3_only`: only `propext`, `Classical.choice` and `Quot.sound` (or a
  subset), with no recorded native assertions.
- `accepted_native_assertions`: accepted native assertions, such as those from
  `native_decide`. A kernel fallback does not change the original receipt's
  classification to std3-only.
- `unexpected_accepted_axioms`, `rejected`, or
  `missing_or_inconsistent_evidence`: inspect the listed receipt and result.
  A finished attempt that submitted no proof can have no checker receipt.

The checker records native assertions across the candidate, including unused
helpers, so a recorded helper axiom need not occur in the final theorem.

## Certification

### Setup

Complete the shared [toolchain setup](#search-setup) and all three Whiel search
stages. Certification uses their accepted answers; it does not require the
Direct Lean baseline. **Certification makes no model calls and needs no model
login.**

RQ5 requires at least 24 available physical CPU cores and enough memory for two
attempts, each guarded at 96 GiB. The script selects disjoint sets of 12 physical
cores within its allowed CPU affinity. If setup has already completed in this
checkout, no additional installation command is needed.

### Run the experiments

```bash
python3 scripts/reproduce_paper.py certify
```

The script makes one certification attempt per input/configuration using its
earliest accepted search answer. It copies the answer into the trial's
certification directory and preserves the search records.

| Fixed parameter | Value |
| --- | --- |
| Host / CLI whole-certificate limits | 300 s / 300 s |
| Internal Vampire allowance | 300 s |
| Memory guards | 10 GiB per process; 96 GiB per process tree |
| Parallelism | Two attempts concurrently; 12 physical cores, 12 solver workers and `LEAN_NUM_THREADS=12` per attempt |
| Compiler | Lake |
| Candidate timeout | None (`WHIEL_CERTIFICATE_CANDIDATE_TIMEOUT_SECONDS=0`) |
| Bootstrap watchdog backstop | 128 GiB |
| RSS sampling interval | Nominally 0.2 s |

Timeouts and memory failures advance to the next answer after cleanup;
infrastructure or cleanup failures stop the queue. Attempts are not retried.

### Understanding the results

```bash
python3 scripts/reproduce_paper.py report
```

`certification/<arm>/<ID>/supervisor.json` contains the outcome and nested
`measurement`: `elapsed_seconds`, `peak_process_rss_kb`, `peak_tree_rss_kb`, exit
and cleanup status. Successful records also retain the exact input theorem,
standard-axiom check and certificate build settings. See [AUDIT.md](AUDIT.md)
for the certificate's trust boundary and formalization map.

The success fraction is `certified` outcomes divided by selected accepted
answers. Compute successful-attempt time and peak-memory statistics from those
successes, keeping failed-attempt costs separately.

RSS is resident memory. The `_kb` fields are KiB; divide by 1,048,576 for GiB.
The process peak is the largest sampled individual process; the tree peak is
the largest sampled sum across the owned process tree. Elapsed time includes
cached bootstrap and joined cleanup. Peaks exclude cleanup; because the watcher
samples before checking the deadline, its last sample can slightly exceed
300 s. Time and memory guards can therefore be exceeded slightly before stopping.
