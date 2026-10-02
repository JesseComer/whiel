# AgentHoudini files

This directory owns the Python agent harness (C): provider configuration,
native execution, authentication, sessions, prompts, MCP, sandboxing, skills,
agent resource limits and logs. Houdini's authoritative state, queries,
admission and certification remain in the Rust engine (B). C consumes its
versioned public API; a proposal receipt is not admission or certification.

The Python runtime, configuration, logs and separate public entry modes are
joined for K2 acceptance against the reviewed generic API 3 / wire 3 contract.
Temporary native code in B is migration-only and is removed at K3.

| Directory | Contents |
| --- | --- |
| `agent_houdini/` | Python proposer, native runtime, setup, sandbox, tests and fixtures. |
| `whiel_runner/src/proposer_api/` | Engine-owned semantic API, immutable observations, queries and proposal contracts. |
| `whiel_runner/src/proposer_host/` | Generic endpoint lifecycle, transport limits and failed-endpoint cleanup. |
| `whiel_runner/src/framework2/` | Engine-owned canonical feedback, query dispatch, search and certification. |
| `agent_houdini/toolchain/` | C-owned native CLI pin and capability configuration. |
| `reports/agent_houdini/` | The proposal method's semantic/algorithmic contract. |

Use the [collaborator guide](../docs/README.md) for setup and commands, the
[API guide](../docs/proposer-api.md) for customization, and the
[process protocol](../docs/proposer-host-protocol.md) for transport. Read [AGENTS.md](AGENTS.md)
before editing. The [campaign entry point](../whiel_runner/CAMPAIGNS.md) stays short.
Engine integration tests remain under `whiel_runner/tests/`.

Build the public `whiel-symbolic` verifier independently. C's Python source
changes do not require a Cargo rebuild. C may add its own helper modules or
dependencies without a B-owned registry change. It does not import engine
internals or load their sources.
Other proposal methods can use the same engine authority without inheriting
the agent harness.

## Python frontend

| Module | Responsibility |
| --- | --- |
| `frontend.py` | Consultation lifecycle and native AgentHoudini frontend dispatch. |
| `protocol.py` | Versioned generic socket frames and binary attachments. |
| `json_wire.py` | Bounded strict JSON encoding and decoding. |
| `mcp_client.py` | MCP messages and translation to canonical query/submission requests. |
| `prompt.py` | The rendered prompt: C's assets, its selection of the push, and B's two documents. |
| `prompt_assets/` | C-owned explanation the prompt is assembled from. |
| `render.py` | `render-prompt`: the same rendering, offline, from a recorded push. |
| `tool_catalog.py` | Tool schemas and the validated advertised inventory. |
| `skills.py` | C-owned guidance catalog and local `get_skill`. |
| `stop.py` | One stop signal and the shielded join used by every C owner. |
| `process_tree.py` | Owned native processes, pipe pumps and joined group cleanup. |
| `provider_config.py` | Provider selection: pass-through model/effort strings and argument validation. |
| `launcher.py` | Pure C configuration and the public generic B command builder. |
| `agent_log.py` | Exclusive private JSONL logs with byte/event/record bounds and redaction. |
| `run_records.py` | Per-consultation retention: prompt, CLI stream, MCP traffic and submissions. |
| `show_run.py` | `show-run`: an offline per-consultation summary of a recorded run. |
| `export_run.py` | `export-run`: copy a run directory for a collaborator, without the raw provider streams, refusing output that carries this machine's own layout. |
| `export_transcript.py` | `export-transcript`: freeze one run's transcript into a single small file -- no paths, prompts, provider streams or solver output -- for a collaborator to replay and for `compare-runs` to check a replay against. |
| `compare_runs.py` | `compare-runs`: three named replay fidelity checks between an original run (or its `export-transcript` file) and a replay of it. |
| `experiment.py` | `experiment run`/`report`: a campaign from a spec file into one run directory, and its readable digest. |
| `experiment_pool.py`, `pool_preflight.py` | `experiment pool`: GNU Parallel scheduling of independent single-input campaigns, plus a model-free sandbox check. |
| `experiments/` | Experiment spec files. |
| `setup_cli.py`, `bwrap.py`, `preflight.py` | Native pin verification, optional narrow Linux confinement and diagnostics. |

## Experiments

`python3 -m agent_houdini experiment run SPEC.json` runs a campaign from a spec
file into one self-describing run directory:

```
artifacts/runs/<model>-<YYYYMMDD>[-<name>]/
    run.json          the resolved spec, the exact command, revision, timing, exit code
    launcher.log      everything the launcher and the verifier printed
    verifier/         B's destination: campaign-settings.json, summary.json, <ID>/result.json, <ID>/Certificate/
    agent/            C's logs: launcher.jsonl, <ID>/events.jsonl, <ID>/request-N/{prompt.txt,...}
    progress.md       one row per input: verdict, consultations, clauses submitted, Core size, search time
    examples/<ID>/    summary.md, plus links verifier -> ../../verifier/<ID> and agent -> ../../agent/<ID>
```

`summary.md` reads both trees for one input: each consultation's push (Core,
pending, last round's outcomes, latest result), what the agent said, the tools
it called, what it submitted and the verifier's reply, then the verifier's own
clause ledger (every clause with its final standing and every check by level,
role and outcome), the countermodels, and where the files are.
`python3 -m agent_houdini experiment report RUN_DIR` rewrites that digest at any
time, for a running campaign too, and turns an older
`artifacts/campaigns/<name>` directory into `artifacts/runs/<name>` with links.
The spec keys are listed in [experiments/README.md](experiments/README.md).

### Searching and certifying in two steps

A campaign is an untrusted search followed by a deterministic certification.
The search consults the agent; the certification consults nothing and costs
minutes and gigabytes per input. The `certify` spec key decides where the two
meet, and for a large campaign the answer is `deferred`:

```json
{ "certify": "deferred" }
```

Every input is then searched first, each verdict written to
`verifier/<ID>/Accepted.json` with `Core.json` or `Counterexample.json` beside
it the moment the untrusted verifier accepts, and one certification phase
follows the last search. Nobody — a person or an agent paying to poll — is held
through the deterministic tail, and the search timings are measured without a
certification loading the same machine.

`"certify": "never"` stops at acceptance. The run directory is then finished
whenever and wherever suits, from the records alone:

```
whiel-symbolic campaign certify --run artifacts/runs/<run>/verifier
```

That command is idempotent and resumable, takes `--jobs` and `--retention`, and
refuses an input whose declarations changed since it was accepted. Until it has
run, those inputs read `valid_uncertified` or `invalid_uncertified` in
`progress.md`, the run's `summary.json` says `all_accepted` but not
`all_certified`, and `campaign run` exits 4 rather than 0. An accepted record is
not a certificate: only the published `Certificate/` tree is.

A run directory made this way is self-contained: copy or move it to another
machine with the checkout and certify it there, later, without repeating the
search or consulting any model.

### Reading a run: three fixed points

For analysing a finished campaign — the four measures and where each comes
from, the run directory file by file, how to read `Core.json`,
`Counterexample.json` and `Accepted.json`, and when two runs are comparable —
see the [analyst's guide](../docs/analysts-guide.md).

- **`search_seconds` in each input's `result.json` is the search-time
  measure.** The campaign runner writes it, it excludes admission and
  certification, and nothing else is to be reported as search time. It is also
  the only per-input time the digest shows: no whole-input span of the
  harness's own is rendered anywhere, because a second input total beside this
  one would be read as a rival measure of the same thing. The per-consultation
  `agent_seconds`/`verifier_seconds` in `rounds.json` are not that — see
  [the two kinds of time](experiments/README.md#the-two-kinds-of-time).
- **Exit code 4 is the normal success code of a `never` or `deferred` run.**
  It says every selected input was accepted and the accepted ones still await
  certification. 0 additionally means certified; 2, 3 and 130 are argument or
  bootstrap failure, an incomplete or failed input, and interruption.
- **Searching and certifying are two separate steps**, and the second consults
  nothing, so it can be run whenever and wherever suits.

### The workspace guard under a long retained run

B's workspace guard counts the live bytes, files, entries and directories of
**the whole campaign**, not of the input currently running. Under
`retention: all` every earlier input's ledger, consultation records and
artifacts are still on that count, so at the ordinary per-input allowances a
long run would stop partway through against its predecessors' residue.
`retention: all` itself now raises those four limits when the run gives no
explicit flag of its own for one of them, so no spec in `experiments/` needs
to pass them through `verifier_args`; an experiment that wants a different
value still can, and that explicit value wins.

`--minimum-free-bytes` stays at its default, so a genuinely full disk still
ends the run.

## The replay proposer

`tests/replay_proposer.py` runs the real campaign pipeline with no model at
all. It is a generic wire-3 proposer executable, started exactly as the agent
harness is (`campaign run --proposer-executable`), and for each input it
submits the answer the repository already records — `Benchmark/<ID>/Core.json`
for a valid case, with its rows in level order, or
`Benchmark/<ID>/Counterexample.json` for an invalid one — through the same
bounded proposal channel an agent uses, bound to the exact push. The untrusted
verifier then does exactly the work it would do for an agent that proposed the
right answer on its first consultation: the Vampire proof lane racing the
finite-model lane, the Lean worker and leveled Houdini. Nothing is short cut
and nothing asserts the answer is right.

It has two modes, named for what they replay. An **answer replay** submits one
final answer per input: by default the repository's own record, or, with
`--answers DIRECTORY` (spec key `answers`), the answers under
`DIRECTORY/<ID>/` — a campaign's verifier destination, or a harness run
directory through its `verifier/` — so the answers an earlier run accepted can
be put back through the verifier in seconds. A **transcript replay**
(`--transcript`, spec key `transcript`) submits what a recorded run's proposer
submitted, round by round, wrong and partial proposals included; it is
described under [replaying a transcript](../docs/campaign-quickstart.md#replaying-a-transcript).
An answer replay shows that the verifier accepts known answers; a transcript
replay shows that it makes the same decisions on a whole recorded search.

It reads the benchmark records a real proposer must never see, so it lives with
the tests and is never part of the proposer runtime.

Run it from a spec:

```sh
python3 -m agent_houdini experiment run agent_houdini/experiments/replay.json
```

or start B directly, which needs no harness at all:

```sh
whiel_runner/target/release/whiel-symbolic campaign run \
  --repo "$PWD" \
  --proposer-executable "$(command -v python3)" \
  --proposer-arg "$PWD/agent_houdini/tests/replay_proposer.py" \
  --proposer-arg --repo --proposer-arg "$PWD" \
  --proposer-arg --log --proposer-arg "$PWD/artifacts/replay-check/endpoints.jsonl" \
  --input Example0001,Example0013 --destination artifacts/replay-check \
  --workers 4 --search-limit 600 --certify never --retention all
```

`--log` is optional and writes one JSONL line per wire step per endpoint;
`--max-requests N` bounds how many times an answer replay submits one input's
answer (default 4: a right answer needs at most one round per launch allowance,
and there are three). Reaching it means the verifier would not accept the
recorded answer; the proposer then closes its connection, which ends the input
at once as not accepted. A transcript replay has no cap of its own: the
transcript says how many rounds there are.

**How to read the result.** The expected outcome over the solved corpus is that
every solved case is accepted: each `result.json` reads `valid_uncertified` or
`invalid_uncertified`, its `Accepted.json` sits beside a `Core.json` or
`Counterexample.json` equal to the repository's record, `summary.json` reports
`all_accepted`, and the command exits 4. Any rejection, any correction round
that never settles, and any input whose search reaches its limit is a **verifier
incompleteness defect**: the proposed answer was the published one, so the
proposal cannot be at fault. An input with neither record has nothing to replay;
the proposer says so on stderr, finishes the request as `source_exhausted` and
releases the endpoint, and B ends that input at once instead of holding the
search open to its deadline.

The tool's own unit tests — the recorded answers it reads and the wire it
speaks, against a fake host — are `tests/test_replay_proposer.py`.

**Transcript mode.** With `--transcript RUN_DIR` in place of the repository's
single recorded answer, the same tool replays a retained run directory's own
responses instead, consultation by consultation: consultation *N* submits
the content of that run's `agent/<ID>/request-N/submissions.jsonl`, re-bound
to the new run, including a response that was malformed in the original run,
so the verifier's handling of it is exercised again. A recorded drop
reference is re-found by the clause's own text and re-pointed at the live
push's drop reference for it; one that cannot be matched is left out and
reported on stderr rather than guessed at.

A consultation the original proposer never answered, and the end of the
transcript, both **end the search at once by closing the connection**,
instead of declining or holding the request open. Declining -- completing
the open request with `source_exhausted`, `no_response` or even `failure` --
used to spin: every one of those is a per-consultation outcome, so
completing it just invites the verifier to open a fresh consultation on the
same exhausted input, which this proposer would decline again, and again,
each one a retained consultation record under full retention, until the
search's own deadline -- or, on a long enough input, the workspace guard
first; measured directly against the real verifier, both `failure` and
`no_response` reproduce that spin, tens of thousands of consultations inside
a search limit of tens of seconds. Holding the request open instead of
answering it avoids the spin but does not end the input early: the search
just runs out its own deadline, which is correct but slow. Closing the
connection outright -- never completing the request, never answering another
`hello` -- is read differently: the verifier sees its endpoint having
exited before finishing, a transport-level fault rather than a proposal
outcome, and does not reopen a fresh consultation for it. Measured against
the real verifier this ends the input in on the order of ten milliseconds,
recorded as `incomplete`/`InfrastructureFailure`, and the campaign proceeds
to its next input exactly as it would after any other input's ordinary end.
That word reads differently from the original run's own ending
(`search_timeout` for a genuinely non-accepted input), which is expected and
is why [`compare-runs`](#comparing-an-original-and-a-replay) treats every
non-accepted status as one class rather than the exact word. A transcript
replay pays no model latency regardless of how a non-accepted input ends, so
give it a short search limit anyway, as a plain safety net --
[`experiments/transcript-replay-template.json`](experiments/transcript-replay-template.json)
uses 90 seconds, comfortably above what an *accepted* input's own real proof
search needs (the verifier's own share of a consultation round, typically
seconds) and far below the 600 seconds a real model's campaign uses. The
`experiment run` spec key is `transcript` (see
[experiments/README.md](experiments/README.md)); see the
[collaborator instructions](../docs/campaign-quickstart.md#replaying-a-transcript)
for exporting a run to replay and replaying one you received.

## Freezing a transcript for a collaborator

`python3 -m agent_houdini export-transcript RUN_DIR OUT.json` reads a harness
run directory and writes one small JSON file: the run's own recorded verifier
controls, its `provider`/`model`/`reasoning_effort`, and, per input, one
*round* per real consultation (with `dropped` resolved to clause text rather
than a run-local reference, and every `binding` removed) and the record the
three [`compare-runs`](#comparing-an-original-and-a-replay) checks compare a
replay against (verdict class and status, the accepted Core with levels or
the counterexample instance, and the attempt ledger reduced to `(clause,
check kind, level, outcome)`). A correction round is not a round: B's own
message says a refused response's clauses were never read, so only a
consultation's last, uncorrected request becomes its round -- replaying an
earlier, corrected-away attempt would hand the live verifier a freshly
rebound, no-longer-refused version of content the original never admitted.
A round the search's own deadline reached but never answered is marked
`cut_off` and excluded; `compare-runs` separately restricts both sides of
the 3rd fidelity check to rounds the original actually completed (an input
with no completed round at all has nothing to compare and never fails). See
[the analyst's guide](../docs/analysts-guide.md#7-checking-a-replay-against-its-transcript)
for the full rule and its known limitations. No path, prompt, MCP
exchange, provider stream or solver output survives into the file: after
writing, it is scanned with the same check `export-run` uses and deleted,
refusing to leave it in place, on any hit. This is the file to send a
collaborator: they run `--transcript OUT.json` (see
[transcript mode](#the-replay-proposer) above, which reads a frozen file
exactly the way it reads a retained run directory) and, once they have their
own replay, [`compare-runs`](#comparing-an-original-and-a-replay) against
the file you sent them.

`export-run` (above) still exists for the rare case a collaborator needs the
whole run directory -- every prompt, every MCP exchange, the clause ledger's
own artifact files -- rather than the small file most replay and review needs.

## Comparing an original and a replay

`python3 -m agent_houdini compare-runs ORIGINAL REPLAY` reads two record
trees -- each a harness run directory, a bare `campaign run --destination`
tree, or, for `ORIGINAL` only, an `export-transcript` file -- and reports
three named checks, PASS or FAIL with the specific differences listed:

- **1st replay fidelity check** -- every input present in both runs has the
  same verdict class (accepted valid / accepted invalid / not accepted; every
  status other than `valid[_uncertified]`/`invalid[_uncertified]` is "not
  accepted", so a replay ending `incomplete` still matches an original that
  ended `search_timeout`).
- **2nd replay fidelity check** -- for every input accepted valid in both, the
  same Core as a set of clauses, each committed at the same level; for every
  input accepted invalid in both, the same counterexample instance.
- **3rd replay fidelity check** -- the same set of `(clause, check kind,
  level, outcome)` entries in the two attempt ledgers, ignoring order, timing,
  attempt numbering and duplicates. An entry inconclusive on either side is
  excluded from this decision and reported separately as a timing difference,
  never as a fidelity failure -- replaying under identical conditions on an
  equivalently loaded machine should settle every check the original settled,
  but identical conditions cannot be fully reproduced, and a timing-sensitive
  check settling one way here and another there is exactly that, not a
  verifier change. A non-accepted input's ledger is reported as a plain
  difference without trying to guess whether the replay did more or less
  work than the original before it ended; see `compare_runs.py`'s own
  docstring.

An input present in only one run is listed and, by default, ignored -- a
replay may cover a subset; `--require-all` turns that into a failure.
`--expect-different ID[,ID...]` names inputs whose differences are reported
but do not fail a check, for a verifier change already known to affect them.
`--json PATH` additionally writes a machine-readable report. The command
exits 0 only if all three checks pass, and starts no campaign, proposer or
solver of its own: it only reads two already-finished record trees.

## Run diagnostics

C's per-input event log (`<agent-log-dir>/<ID>/events.jsonl`) always records the
consultation outcomes, the prompt digest, the CLI's own event counts and, for a
transport failure, a reason: which side closed the exchange, the exception class
and its bounded text, the phase and relay sequence, the MCP method and tool in
flight, whether a reply was still owed, the relay's own diagnostic line if it
left one, and the last event type the CLI reported.

The launcher's log directory is the `--agent-log-dir` it was given, created
fresh, or a `whiel-agent-*` directory made under `--agent-log-parent`. B starts
one C endpoint per input without telling it which input that is, so each input
directory is created as `input-*` and renamed, at the first push, to the task's
canonical id (`Example0001`; `Example0001-2` for a later endpoint of the same
input); the `input_identified` event records the rename, and a push that names
no task leaves the temporary name.

`--agent-retention all` additionally keeps, per consultation, the bytes a
post-mortem needs, in `<ID>/request-<n>/`:

| File | Contents |
| --- | --- |
| `prompt.txt` | The rendered prompt exactly as it was written to the CLI. |
| `native-stdout.jsonl` | The CLI's complete stream-JSON stdout. |
| `native-stderr.txt` | The CLI's stderr. |
| `native-debug.txt` | The Claude CLI's own debug log (`--debug-file`, passed only under this retention), which records what it did to its MCP server between stream events. |
| `mcp.jsonl` | Every MCP request and reply, with method, tool, sizes and timestamps. |
| `submissions.jsonl` | Each payload handed to B, with B's receipt or refusal. |

Each file has its own generous cap (8 MiB for the streams) and ends with a
truncation marker if it is reached; every line passes the same credential
redaction the argv provenance uses. The `request_outcome` event names the
directory and the retained sizes. These are C diagnostics, never evidence:
nothing retained is read back into a prompt, a query or a submission. Pair the
flag with B's own `--retention all` when you want both sides of a run.

Read a recorded run without opening JSON:

```
python3 -m agent_houdini show-run <agent-log-dir>
```

It accepts an agent log directory, a single input directory or one
`events.jsonl`, and prints per consultation the outcome, prompt size, CLI event
counts, tool calls with reply sizes, submissions with B's verdict and the
failure reason. It reads only C's own log directory and changes nothing.

## The prompt

C owns every word the agent reads; B never sees a rendered prompt. One
consultation's prompt is assembled here, in this order:

1. The reference, from `prompt_assets/00-framework.md`. This is plain
   Markdown, edited without a Rust or Lean rebuild. It is unconditional: the
   mission, the verification framework, the clause grammar, the push
   reference with verdict meanings and responses, the queries, and
   submission discipline are rendered on every consultation whatever the
   push costs. The reference explains the verifier and does not coach:
   strategy, clause patterns and the worked example are skills (below),
   absent unless a run enables them.
2. C's structured presentation of the push: the task in preprocessed and
   original form, the relation table relating the three spellings of a relation
   (push key `o:p::T`, display `T∞`, clause source `op_zT`), the Core, pending
   clauses, last round, the latest result, any correction, the remaining
   budget in plain seconds, the tool list with its descriptions, and, when a skill library is
   configured, the library's index under `# Skills`.
3. B's exact response example, delimited, then `IDENTITIES AND DROP
   REFERENCES`: every clause identity (`clause_id`, `record_digest`,
   `formula_digest`) and every pending clause's `drop_reference`, each copied
   out of the observation verbatim, plus the host limits in force. Those are
   the only values of the push an agent hands back exactly, so they are the
   only part of the observation repeated; its task text, schema and limits are
   rendered once, in step 2. C derives no fact and never reconstructs a
   binding, an identity or a digest. (Until 2026-09-17 the whole observation
   was appended instead, 6 KB on a first consultation and 15-20 KB later, most
   of it the task text and clauses a second time.)

Every clause identity B publishes carries the clause it names: `canonical_source`
is the source the verifier admitted and `display` its display spelling, in
`core[]`, `pending[]`, `last_round[]` and in every `history`, `ledger`,
`countermodel` and `strongest_refutations` row. C renders that text and keeps no
transcript of its own submissions. What an identity does not carry is the check
history — the level and role each attempt ran at, how it came out and which
attempt refuted it. C does not fetch that to render it: `00-framework.md`
sends the agent to `history` for one clause's record and `ledger` for the run's,
so rendering a consultation spends no query of C's own.

Render exactly what the agent would read, offline and without a provider:

```sh
python3 -m agent_houdini render-prompt agent_houdini/fixtures/example0001_consultation.json
python3 -m agent_houdini render-prompt /path/to/campaign/destination
```

The argument is a recorded observation JSON document, a
`{observation, response_example}` pair, or a directory searched for one. A bare
observation carries no response example, so a placeholder marked by its all-zero
digests is shown; it is for reading, never for submission.

`agent_houdini/fixtures/example0001_prompt.txt` is the golden prompt for the
recorded `Example0001` first consultation, `example2004_prompt.txt` the golden
for a recorded *populated later* consultation (a real second round with a Core
row, five pending clauses and last round's outcomes, its digests replaced by
synthetic ones), and `default_prompt.txt` the golden for the minimal synthetic
push. `tests/test_prompt.py` compares all three byte for byte, so any prompt
change — asset wording included — arrives as a reviewable diff. Regenerate them
by rendering the matching fixture; those three goldens are the pin. The
populated one is what pins what a real later round actually holds: the empty
recorded push is the smallest tail C ever renders and pinning only that hid an
asset budget that dropped everything but the role on real second rounds.
(`implementation_manifests/proposer-boundary.json` records a
`source_sha256` snapshot of the K3 checkpoint, including an older
`default_prompt.txt`; it is a record of that pass, not a live check.)

The entry point has separate `campaign run`, `endpoint` and `render-prompt` modes.
The campaign launcher starts B's public command; B starts the configured C
endpoint, which never launches a campaign recursively. C choices appear before
the first `--`; opaque B campaign arguments appear after it. C reserves only
the three conflicting B endpoint flags (`--proposer-executable`,
`--proposer-arg`, `--no-proposer`) and does not duplicate B's option registry.

The C campaign command is:

```sh
python3 -m agent_houdini campaign run \
  --verifier /absolute/path/to/whiel-symbolic \
  --provider codex --model <model> --reasoning-effort medium \
  -- --repo /absolute/path/to/whiel --input 1
```

`--model` is required, accepts any nonempty control-character-free string and is
passed to the provider CLI verbatim; there is no default model and no model table
in C. `--reasoning-effort` is optional and is passed through the same way.
`--provider-cli PATH` names an explicit CLI executable for either provider;
otherwise `claude`/`codex` is resolved from `PATH`. Use C's `--no-proposer` before
the delimiter for the explicit no-model diagnostic. Help, invalid arguments and
no-proposer configuration do not start native tools. Configuration validation is
pure; CLI resolution and joined interruption handling belong to C's native runtime.
Explicit installation remains a separate setup command. The standalone
`provider_config.py --json` helper retains its strict 16 KiB input/output
contract, but production C does not need a subprocess to call its own validator.

The launcher performs bounded verify-only setup before starting B, returns 2 on
configuration/setup failure, and joins a stopped setup probe before returning
130 for SIGINT. It then replaces itself with the public verifier process so B
owns its own signals and cleanup. `endpoint` mode only starts C's API/native
coordinator; it cannot recursively start a campaign.

Agent allowances use `--agent-*` options before the delimiter; B's independent
API/verifier options remain after it. Run the C command with `--help` for exact
defaults. Native time has no additional default limit; B's cancellation remains
authoritative. `--agent-thinking-tokens N` (Claude only, off by default) is
passed to the CLI as its per-turn thinking cap: with the consultation budgets a
campaign uses, an uncapped model can spend the whole consultation thinking and
never reach a tool call. The allowance is **advisory** — it caps the model's
thinking budget inside the CLI, and recorded runs have reported per-turn
thinking estimates above the configured value — so it is pressure toward acting,
not a bound. When C's own deadline for a turn (B's remaining request budget)
expires, C joins its MCP bridge first and only then stops the CLI, and records
the turn as `deadline` (event `native_deadline`): a CLI that is told to stop
shuts its MCP server down itself, and a bridge still open at that moment would
have recorded the relay's exit as a transport failure. A deadline reached with
nothing submitted completes the request with the wire's `no_response` — the
explicit "finished without a submission" — never a transport `failure`: C floors
B's budget to whole seconds, so C's timer can fire just before B's, and labelling
that a transport fault had B record the retryable class for a consultation whose
clock had merely run out. A deadline reached after a submission was attempted
stays a `failure`. `--agent-log-parent` chooses an existing parent for fresh private
C logs and `--agent-log-dir` names the fresh directory itself. The launcher
prints its campaign log directory; each input creates its own
`<ID>/events.jsonl` beneath it. The log's own size, event and record
bounds are fixed constants, independent of native traffic/workspace limits. Configured C budget exhaustion stays latched,
starts no further native work, and leaves B's consultation/termination policy
unchanged.

The six optional read queries are `countermodel`, `strongest_refutations`,
`history`, `ledger`, `validate_clauses` and `evaluate_clauses`. Each advertised
tool runs exactly one of them, and B authorizes every query it receives. C owns
the advertised names and descriptions. `submit` uses a separate bounded proposal
channel; its receipt does not establish admission or proof.

`WHIEL_AGENT_SKILLS_FILE` names the skill library, either a directory or a
JSON file. A directory holds `index.json`, `{"skills": [{"id", "description",
"applies", "file"}, ...]}`, and one Markdown file per skill; the index is what
the prompt lists under `# Skills` (id, description, what it applies to) and
the file is what `get_skill` returns, as `{"id", "content": {"description",
"applies", "text"}}`. `agent_houdini/skills/v1/` is the hand-written library:
the layered strategy, five clause patterns, how to read a countermodel, and
the worked example that used to be a prompt asset, each written as a
procedure (when it applies, what to inspect, how to construct, which query
tests it, how to read the next failure) and each with its provenance and the
program families it would leak into. A JSON file mapping IDs to guidance is
the older shape and still works. C reads the library once per consultation
into an immutable snapshot (16 KiB for the index or the JSON file, 32 KiB per
skill file, at most 64 skills), through nonblocking opens of regular files;
edits become visible in the next consultation. When the variable is unset,
skills are disabled, `get_skill` is not advertised and the prompt has no
`# Skills` section, which is the ablation baseline. `get_skill` is local to
C and is independent of B's query policy.

Optional bubblewrap keeps the exact selected CLI executable readonly. The Python
MCP relay adds only a canonical system `/usr/bin/python3[.N]` executable and an
executable standalone relay file. Existing system-library/CA/DNS mounts,
HTTPS_PROXY/NO_PROXY selection, private auth-file checks and locking remain
unchanged. Custom/virtualenv interpreters needing other runtime trees are
unsupported in this wrapper; no directory mount or local fallback is added.
The 16 existing wrapper tests and new construction tests are synthetic evidence,
not proof of real Linux namespace or TLS behavior.

C logs are bounded, redacted diagnostic data, never verified evidence. They
record prompt byte counts and SHA256 digests and a digest of the sanitized
native command arguments. The provider CLI is recorded by path, requested model
and the version string it reported, which is never compared with a pin. C does
not hash its own package tree: the checkout is whatever the operator ran, and a
digest of it attested nothing about the loaded code. Complete native MCP
configuration and environment arguments are withheld before command hashing, so
opaque transport tokens are never recorded or hashed, and foreign text passes
the bounded credential redactor before it reaches a record. Native stdout stays
a counter per reported event type, with bounded redacted stderr diagnostics.
Native traffic and the five logical agent accounting legs are measured by the
runtime, independently of log limits and B's generic API limits.

The provider launch approach is based on Fangzhu Shen's original agent setup.

## Python attribution

Every Python file in this package, including its tests and fixtures,
carries an `Author: Fangzhu Shen` header: the package adapts and extends her
original agent setup, and the credit applies to the whole of it.

Run the Python test suite from the repository root:

```bash
python3 -m unittest discover -s agent_houdini/tests -p 'test_*.py' -v
```

The runtime runs whichever provider CLI is selected, at whatever version it is,
and forwards the requested model and effort strings unchanged. Neither model
names nor CLI versions are enumerated or compared anywhere in C. The reported
version is recorded as provenance, and a CLI that does not answer `--version` is
recorded as an unknown version rather than refused. `setup_cli.py` remains an
optional pinned Codex installation used by the Linux confinement route; point
`--provider-cli` at its executable when you want it.


`tests/claude_offline_fixture.py` is the native Claude transport fixture driver.
It uses only synthetic authentication and an
owned loopback endpoint under a macOS network-denying profile. Native Claude
execution, exact command/environment checks and the stdio relay belong to C's
Python runtime. Native CLI login still works without reading or copying credentials.
See `whiel_runner/CAMPAIGNS.md` for account
limitations and optional smoke commands.
