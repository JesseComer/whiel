# Results and troubleshooting

A campaign records configuration before running its selected inputs:

| Path under the destination | Contents |
| --- | --- |
| `campaign-settings.json` | `schema_version: 3`, resolved canonical `inputs`, `controls`, and opaque `proposer` selection (or null). |
| `resource-limits.json` | `schema_version: 2` and `limits`, containing the nine configured API, artifact and workspace guard values. |
| `<ID>/result.json` | `schema_version: 3`, one result per started input, including `campaign_controls`, `proposer` and `search_seconds` (see below). A certified result also names `certificate`, `axioms` and the `certificate_module`/`certificate_theorem` a later re-check revalidates the tree with; an uncertified one names `record` and `accepted`. A result `campaign certify` rebuilds after its own was lost carries only what the acceptance envelope still proves. |
| `summary.json` | `schema_version: 3`, `interrupted`, `all_certified`, `all_accepted`, `resource_failure`, `selected_inputs`, `unrun_inputs`, `campaign_controls`, and `results`. |

`schema_version` stays 3 for both: members are only added, and a
reader pinned to 3 keeps reading the ones it knows. The version is bumped when
an existing member changes meaning, not when one is added. `controls` gained
`casc_portfolio`, `proof_casc_share` and `proof_casc_retry_share` this way; no
member it already carried means anything different.

### These records name no machine location

A run directory is meant to be copied to another machine and certified there,
so nothing in the small records names where this machine kept anything.

| Field | What it holds |
| --- | --- |
| `record`, `accepted`, `certificate`, `counterexample` in `<ID>/result.json` | a path relative to that input's own directory: `Core.json`, `Counterexample.json`, `Accepted.json`, `Certificate`. A reader resolves them against the directory it read the `result.json` from. |
| `record` in `<ID>/Accepted.json` | the same, and always has been. `Core.json` and `Counterexample.json` carry no paths at all. |
| `proposer.executable`, `proposer.arguments[]` in `campaign-settings.json` and `<ID>/result.json` | a value that lies inside `--repo` is named relative to the repository root (the root itself reads `.`); anything else is exactly what the operator typed, neither canonicalized nor resolved. B still resolves the executable it actually starts; that resolution is not what the record carries. |

`summary.json`'s `results` are these same result objects, so they inherit all of
it. The binary runtime traces under `<ID>/artifacts/` are outside this: they are
digest-bound evidence and are never rewritten.

### `search_seconds`: what it measures

`search_seconds` is **the** search time — the figure to quote — measured by the
campaign runner itself on a monotonic clock, in seconds as a JSON number.

- It **starts** when the search loop begins: after the proposer process has
  been started and has completed its handshake, immediately before the task is
  pushed to it.
- It **stops** when the search returns its result: after acceptance (or
  failure), including the proposer's own shutdown, and *before* any record
  (`Core.json`, `Counterexample.json`, `Accepted.json`) is written and before
  any certification begins.

It therefore **excludes** runner startup, Lean worker startup and build,
proposer startup and handshake, record writing, and certification of every
kind. It is written on every result whose search started — certified,
uncertified, failed and timed out alike — and on none whose search did not, so
an input that failed before the search loop has **no** `search_seconds` key
rather than a zero that would read as an instant search. `campaign certify`
preserves it unchanged and never measures its own; a result it rebuilds after
the original was lost takes the value from `Accepted.json`'s
`search.elapsed_seconds`, which is the same measurement.

The experiment harness reports this value as its `search` column and as
"search time" in each input's `summary.md`, and it reports no other per-input
time at all: it derives nothing from file timestamps, because a second figure
beside this one would be read as a rival measure of the same thing. An older
run directory with no `search_seconds` shows `?` rather than a substitute.

The controls object records search/certification/consultation seconds, transport
retries, certificate-solver seconds, counterexample-validation seconds, optional
iteration count, `workers` and resource limits. Absent optional values are
JSON null.

`controls.budgets` records every concurrency budget the run derived from
`--workers`: `checks`, `lanes`, `finite_model_lane`, `vampire_processes`,
`lean_workers`, `lean_worker_threads`, `lean_round_trip_timeout_seconds`,
`cpu_permits`, `runtime_worker_threads`, `certification_jobs`, and the
`host_parallelism`, `host_memory_bytes`, `vampire_memory_limit_mb`,
`vampire_planned_footprint_mb`, `memory_estimate_checks`,
`exceeds_memory_estimate` and `exceeds_host_parallelism` recorded alongside
them. The limit is what a Vampire process is launched under; the planned
footprint is what the memory estimate divides by. Neither the memory estimate
nor the core count narrows `checks`, default or explicit; `exceeds_*` only
reports when one of them is exceeded. These records expose differences in
resource controls; they do not establish timing comparability across machines.
Compare search times on the same machine under similar load, as described in
the [analyst's guide](analysts-guide.md#4-settings-and-comparability). Schema 3 adds
this object and is the reason for the bump; `workers` itself is unchanged and
still means N concurrent clause checks. See
[derived concurrency budgets](cli-reference.md#derived-concurrency-budgets).
Every check races a proof lane against a finite-model lane (`lanes` 2), so a
clause that is not inductive is reported as refuted with a Lean-validated
countermodel rather than as unproved within the budget. The lane is not
configurable: a production check configuration cannot be built without it, and
proof-only exists only as an explicitly named test configuration. Because a
campaign now produces search-phase countermodels, `--countermodel-retention-tuples`
matters: it is unset by default, so every validated countermodel is retained in
full and served to the proposer through the `countermodel` tool. Finite-model
search starts at size one, so models are normally tiny; pass an explicit bound
if a run should not retain a large one.

`proposer` contains the executable path and opaque argument array,
not a verified native identity. Settings are not themselves proof evidence.
Keep the command/source revision as well: the controls object is not a complete
serialization of every CLI argument.

If a workspace or authoritative API allowance stops the campaign, later inputs
have no result directory; `unrun_inputs` lists them. The started input can report `resource_exhausted` with
the diagnostic, and summary `resource_failure` records the resource failure.
That stop returns exit code 3 with `interrupted: false`, distinct from an external
interrupt (130). API exhaustion during startup or final shutdown also stops
later inputs. If cleanup fails at the same time, its primary failure retains priority while the
summary still records the resource cause. Artifact failures remain nonsemantic.
C-local native limits are recorded in C logs: the latch prevents further native
work in that endpoint, while B retains its iteration, time and API policies.

Each started input also keeps its own artifact backend under
`<ID>/artifacts/run-<backend>/`: `run-configuration.json` written the moment
the run's policy is bound, `manifest.json` frozen at settlement, and the
retained payloads under `required/`. Every manifest record names an `id`,
`kind`, `relative_path`, `byte_len`, `scope` and whether the payload is still
`retained`; a record survives even where its payload was swept, so a report can
still say what existed.

Under `--retention all` two of those records are the run's account of its own
conduct, and both are published for every settlement outcome — valid, invalid,
`search_timeout`, iteration exhaustion, resource failure and interruption:

| Manifest record | Contents |
| --- | --- |
| `runtime_trace` with scope `["root", "consultation-records"]` | The [consultation records](proposer-host-protocol.md#recorded-consultations): one hash-linked frame per artifact, opening with a `header` and closing with a `closed` record. |
| `runtime_trace` with scope `["root", "attempt-history"]` | One `whiel_framework_ii_attempt_history` object: the outcome, the run and task identity, the ledger rows with clause, level, role, verdict, refutation and invalidation, the transport attempts against the proposer, and the failure classification where there was one. |

Each record has a scope of its own, so a manifest reader selects exactly one of
them without parsing payloads. Other root-scoped `runtime_trace` records — the
protected-theorem selection receipts, for one — are neither of these, and solver
payloads are published under their own solver and verification-stage scopes.

`result.json` then names what it published rather than only how much of it there
is:

- `consultation_records` carries the sealed frame count, the chain head, the
  `kind` and `scope` that select the frames, and `artifact_ids`: the manifest
  record ids of the frames in chain order. Read them in that order to walk the
  chain. Where the recording could not be sealed or published the field carries
  an `error` and `published_frames` instead, the latter being the number of
  frames promoted before the refusal — `0` for every refusal raised while the
  set was being staged.
- `attempt_history` carries the `kind`, `scope` and `artifact_id` of that one
  record, or an `error` where its publication was refused.

The default `certificate-only` retention publishes neither record and omits both
fields.

Paths and identifiers should be retained with their run; different inputs,
retries and provider configurations are not interchangeable.

Certificate writers reserve their output destinations, and invalid publication
also reserves the shared `Counterexample.json` record. A competing writer fails
without taking over another writer's staging. Existing output entries are never
replaced by final promotion. Public destinations can have hidden
`.whiel-output-<digest>.lock` siblings: these small files persist, but their OS
locks release when the owning process closes or exits. Do not unlink a lock file
to clear a busy destination while writers may still be running. A conflicting
durable counterexample record requires inspection; it is not silently replaced.

## Read statuses before logs

| Status | Interpretation |
| --- | --- |
| `valid` | Published proof certificate for the exact input target with checked axioms; `Core.json` beside it records the certified Core (level and canonical source per clause), from which `certificate build --core` regenerates the tree. |
| `invalid` | Published checked concrete counterexample; `Counterexample.json` identifies it. |
| `valid_uncertified` | The untrusted search proved its Core and the run stopped there (`--certify deferred` or `never`). `Core.json` and `Accepted.json` are on disk; **nothing is proved in Lean yet**. `campaign certify --run DIR` builds the certificate from the record. |
| `invalid_uncertified` | The search's counterexample was validated by Lean during the search and the run stopped there. `Counterexample.json` and `Accepted.json` are on disk; no certificate tree exists yet. `campaign certify --run DIR` builds the certificate from the record. |
| `input_changed` | `campaign certify` found that the input's declarations, or its scope, differ from the identity recorded at acceptance. Nothing is built for it: a certificate rebuilt from another input's record would close a theorem about something else. Re-run the search for that input. |
| `certification_unchecked` | A `Certificate/` tree stands beside the record but `campaign certify` could not let its claim stand: the tree did not revalidate, or its own `result.json` names no certificate module and theorem, so nothing can be revalidated. The tree is never replaced or removed; inspect it, or remove it to have the record rebuilt. |
| `search_timeout` | Search allowance exhausted; no proof verdict. |
| `certification_timeout` | Certification/publication allowance exhausted; no published success claimed. |
| `certification_failed` | Search result did not complete checked publication. |
| `incomplete` | Search ended without a certificate, such as after no response, an exhausted guard or inconclusive work. Inspect `failure_kind`/`detail`. |
| `resource_exhausted` | An authoritative API allowance or campaign workspace/resource observation failed; the input is stopped without a semantic verdict. Inspect summary `resource_failure` and `unrun_inputs`. |
| `interrupted` | External cancellation, followed by owned cleanup. |
| `failed` | Per-input setup/execution failure reported by the outer campaign driver. |

### What a run leaves per input

| File | Written | Meaning |
| --- | --- | --- |
| `Accepted.json` | the moment the untrusted verifier accepts, in every mode | `kind` `whiel_search_acceptance` and `version`; names the record beside it, the verdict, the search's elapsed and allowed seconds, the input's task identity, and for a valid result the frozen Core's own payload (digests and per-clause profiles). It is what `campaign certify` checks the input's identity against. |
| `Core.json` | at acceptance for a valid result | The certified Core's rows: one level and canonical source per committed clause, in canonical order, protected precondition rows excluded because re-admission installs them from the input again. `certificate build --core` regenerates the tree from it. It is rendered by the same function the certificate build uses, so a later publication finds the record it would have written itself rather than a differing one. |
| `Counterexample.json` | at acceptance for an invalid result | The durable counterexample record, byte-identical to the one the invalidity publication writes. |
| `Certificate/` | only after a checked publication | The kernel-checked tree. This, and nothing beside it, is what says the result holds. |
| `CertificateEvidence/` | under `--retention all`, after a valid certification | The per-job `problem.p` and normalized `leancheck.lean`. It cannot exist at the end of an uncertified `campaign run`; `campaign certify --retention all` is what keeps it. |

`summary.json` answers two separate questions: `all_accepted`, whether every
selected input left an `Accepted.json` — read from the records themselves, so
an input whose certification later failed still counts as accepted — and
`all_certified`, whether every verdict was published as a checked certificate.
A run that only searched answers the first yes and the second no, and exits 4.

B results contain no native `provider_identity` or `provider_diagnostic` fields.
The C launcher prints its separate private log directory. `launcher.jsonl` records
C configuration/preflight identity; each `<ID>/events.jsonl` records native
identity, prompt length/hash, bounded C-source snapshot, sanitized command digest,
resource settings, fixed stdout event counters and redacted stderr diagnostics.
Snapshots may explicitly be incomplete and log limits may drop events. They are
C's diagnostic claims, not verifier attestations or proof evidence.

A submission acknowledgment is not clause admission, and a tool response is not
a certificate. An exit code or closing prose alone cannot establish submission.
Do not infer dictionary reuse from missing solver timings.

## Common failures

| Symptom | Next check |
| --- | --- |
| Toolchain hash/version failure | Run `LEAN_NUM_THREADS=2 scripts/watchdog.sh 4194304 python3 scripts/check_toolchain.py`; use reviewed target-platform pins, never a convenient system solver. |
| Missing registered input / task mismatch | Check the canonical current ID, registry `--check`, worker provenance and whether the worker was rebuilt after an input change. |
| C provider executable/catalog missing | Run the selected Codex model setup and `--verify-only --json`, or install the exact supported native Claude version. |
| An input ends `incomplete` within seconds and C's log has `provider_unusable` | The provider CLI failed three consultations in a row with nothing submitted (a bad install, a CLI version the adapter's configuration overrides do not match, an expired login, an outage), so C stopped serving that input rather than let the verifier relaunch it until the search limit. Read that consultation's `native-stderr.txt`; the next input starts a fresh endpoint and tries again. |
| Authentication or access failure | Check native CLI login status in your own terminal. Confirm selected model access; never paste auth files or keys into an issue. |
| Claude managed configuration rejected | This adapter supports personal/unmanaged hosts/accounts only. Do not bypass policy; use a supported environment. |
| Wrong response binding | Use the new response skeleton/binding from the latest correction, not a previous consultation. |
| `unknown_skill` | The name is absent from C's current skill snapshot; the default set is empty. No legacy skill database is loaded. |
| `found_not_retained` / skipped model | Data was intentionally omitted or unavailable to the conversion; it is not a fabricated negative Boolean. |
| Explicit host limit | Inspect the named optional limit. A limit refusal is not semantic invalidity. |
| Transport/frame/space failure | Inspect the nonsemantic resource diagnostic and stop/reconfigure; do not retry indefinitely or infer an invariant is false. |
| Search succeeds, certificate fails | Retain reconstruction/axiom/publication evidence. Increase only the relevant allowance if appropriate; never skip Lean checks. |
| C `--isolation bwrap` failure | Verify Linux namespace/mount prerequisites with `agent_houdini/preflight.py`; there is no local fallback. |

## Keep and share useful evidence

Keep the command/configuration, source revision, exact input ID/hash, result and
summary, C native/provenance logs, failure classification and bounded diagnostics.
Preserve failed receipts when comparing changes. Retention `all` retains more
run artifacts and adds the consultation records and attempt history above; it
does not alter the checker or make every file provider-visible. It also keeps
a `Valid` certification's solver evidence (each job's `problem.p` and
normalized `leancheck.lean`) under the input's own run directory,
`CertificateEvidence/`; under `certificate-only` it is dropped. Either way the
published certificate tree itself never carries it, and nothing the kernel
checks reads it — it is retained only so a reviewer can rerun a job.
Request scratch directories are local host diagnostics, not stable proof APIs.
Remove only owned inactive outputs after the run has joined; do not delete a
running worker's evidence or a retained published certificate.

For a report to collaborators, redact credentials and private account details.
Do not upload raw home-directory CLI logs or authentication files. Read the
[tool semantics](tools-and-skills.md) when interpreting observations. There is
no hard whole-process RSS quota in the current command; watched builds cap
individual Lean workers, and sampled workspace guards are not a filesystem
quota or general memory limit.
