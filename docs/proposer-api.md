# The read-only proposer API

Contract revision **3.2.0**. The generic process contract is frozen at
[`proposer_api/wire/README.md`](../whiel_runner/src/proposer_api/wire/README.md),
with the [versioned record migration](../whiel_runner/src/proposer_api/wire/MIGRATION.md).
The only production process path is the generic endpoint. Native provider
execution and MCP belong to C.
The API directory is [`whiel_runner/src/proposer_api/`](../whiel_runner/src/proposer_api/mod.rs).
Authoritative Houdini and Lean backends remain outside that directory; the
bounded provider adapter is versioned with its public declarations.

## Ownership and one consultation

A defines semantics; B owns the worker and all authoritative runtime state;
C produces proposals. Every proposer may use any subset of permitted queries.
A deterministic proposer requires no LLM, MCP, skills or native CLI.

B supplies an immutable typed observation, a scoped query surface, a bounded
proposal writer and cancellation. The Rust trait's legacy names `AgentProvider`,
`AgentPush`, `AgentToolSurface` remain compatible aliases where useful. C gets
no mutable catalog/state/checker or raw worker object. C can render observations;
B alone constructs their facts, digests and exact response binding.

The observation retains the existing push information: the task specification
(the wire field is still named `presentation`), binding, iteration/budget, Core,
pending and last-round clause entries, latest result, enabled queries, state
revision, optional truncation and correction. Every clause entry names its clause and carries the clause's own
admitted text. The typed API makes those fields accessible without parsing prompt
text. B also supplies an exact candidate-response example. Nullable references
mean unavailable data; absent truncation means no announced truncation. The
full ledger is obtained through its query, not a hidden push field.

The push carries data, not explanation. The task specification is the task
identity, both triples, the relation table with its prophecy map, every host
limit in force with its value, the resource allowances and the presentation
digest. The rules of the procedure — what a clause may say, how the two checks
and the levels work, when a clause dies, which proposals exist — are stated in
the paper and enforced by B; B does not also ship them as prose for an agent
to read. Explaining them to a model is the
proposer's own work.

No query changes Houdini's clauses, levels, Core/Pending/Dead, semantic dictionary,
history, ledger, verification results or proposal epochs, including on failure.
Queries may consume resources, emit diagnostics and use isolated operational
worker caches. Supplied instance data has no guaranteed semantic significance.
Only the separately validated proposal path can advance synthesis state.

## Layer A API: semantic services

See [the Lean semantic contract](lean-runtime-api.md) for exact inputs, outputs,
finite-instance codec and the complete internal-worker inventory.

| Query | Arguments | Meaning |
| --- | --- | --- |
| `validate_clauses` | `{clauses: string[]}` | Lean admissibility and canonical source, without instance evaluation |
| `evaluate_clauses` | `{clauses: string[], instances: EvaluationSource[] or "all_retained"}` | Exact formula truth on retained or caller-supplied finite instances |

## Layer B API: observations and runtime reads

| Query | Arguments | Result |
| --- | --- | --- |
| `countermodel` | `{attempt: u64}` | Saved refutation tables or explicit retention omission, attempt and role; clause/level for a clause check |
| `strongest_refutations` | `{clause: ClauseRef}` | Inclusion-maximal tagged-premise refutations by role, with attempts, levels, premise counts and retained models/omissions; optional explicit truncation |
| `history` | `{clause: ClauseRef}` | Exact clause identity with its admitted text, origin, protected flag, status, minimum/current level and every clause-check row oldest first, including invalidated rows |
| `ledger` | `{}` or `{cursor: decimal-string}` | Newest page first, rows chronological within a page, metadata and continuation toward older pages |

There are six semantic queries. Unknown fields or wrong argument types are
rejected, not ignored. `history` is unpaged. Ledger metadata has `total_items`,
`first_index`, `returned_items` and nullable `continuation`; `items` contains
check/invalidation rows. No next page is represented by `continuation: null`.
Current levels and physical attempts may be null where no such value exists.
A catalog record retained only as provenance after rollback has required
`status: null` and `current_level: null`; its minimum level and recorded checks
remain readable. This represents absence from the current three partitions,
not a fourth partition or a newly accepted clause.
Strongest-refutation replies give counts, not complete premise sets.

All replies contain `tool` and `state_revision`, and exactly one of `result` or
`error`. Error payloads contain `code`, `message`, and, only for `host_limit`,
`host_limit: {limit, value, observed}`. Codes are `unknown_tool`, `tool_disabled`,
`stale_surface`, `invalid_arguments`, `invalid_instance`, `unknown_clause`,
`no_refutation`, `host_limit`, `malformed_args` (arithmetic overflow), or
`tool_failed` (real infrastructure/protocol failure). Diagnostic prose is not a
machine discriminator and is bounded before crossing the transport.

## References and scope

`ClauseRef` is `{clause_id: u64, record_digest: string, formula_digest: string,
canonical_source: string|null, display: string|null}`. Copy the whole identity
from `core[].clause`, `pending[].clause`, `last_round[].clause`, or a scoped
query result. A valid exact catalog identity is readable even if it was not in
the first displayed subset. Read eligibility never grants a drop authorization.

The three digest fields name the clause; `canonical_source` and `display` are
the text the verifier admitted for that exact record, so a clause the API shows
can be read as well as named. `canonical_source` is the parseable source in the
clause grammar a submission is written in, and `display` the record's display
spelling; either is null only where the text itself is unsafe to present. On
submission or in a query argument both text fields are optional: a reference
copied whole out of the push is accepted unchanged, one carrying only the three
digests names the same clause, and text that disagrees with the named record is
rejected as `unknown_clause` or an unauthorized drop. Both forms are recorded
exactly as they were sent: an omitted text field stays omitted, and a null one
stays null. The text is a rendering of
the record `record_digest` already fixes, never a separate authority, and it
takes no part in identity comparison.

An attempt ID is a run-local physical checker attempt, not a clause ID,
entailment identity or ledger row ordinal. Retrieve it from
`latest.postcondition_open.attempt`, check-row `result.attempt_id` in history or
ledger, or `strongest_refutations.refutations[].attempt`. Copy a non-null
refuted-check ID into `countermodel({attempt: id})` or a retained evaluation
source. Follow `ledger.result.metadata.continuation` to older pages and reuse
those pages' clause/attempt references in the same consultation.

The query surface/envelope binds run, task, consultation and snapshot. Ended
surfaces and mismatched envelopes fail before argument resolution. IDs alone do
not encode origin: number 7 means the bound run's attempt 7. A number copied
from another run is indistinguishable if 7 is valid here. An unchanged clause
triple may remain valid in a later snapshot; old drop authorizations do not.

## Proposal channel

The proposal schema remains **4**, independent of API revision. Exactly one
bounded UTF-8 JSON response is returned; duplicate keys/unknown fields fail.
The two variants are:

```text
{schema_version: 4, kind: "candidate_clauses", binding: Binding,
 clauses: string[], dropped: DropReference[]}
{schema_version: 4, kind: "candidate_counterexample", binding: Binding, input: JSON}
```

`Binding` has `task_digest`, `scope_digest`, `run_digest`,
`consultation_digest`, `state_snapshot_digest`, `validation_manifest_digest`,
`request_digest`, and integer `validation_ordinal`. Copy the exact B-issued
response example; C never reconstructs hashes. The observation binding identifies
the query snapshot and includes `policy_digest`; the submission binding comes
from the response example and includes `request_digest`. These JSON shapes are
not interchangeable. `DropReference` contains `clause`,
`consultation_digest` and `authorization_digest` issued for that pending clause;
echo it exactly as the push carried it, clause text included.
There are no separate mutable add/drop/check/publish APIs. Refutation-dead
clauses cannot revive; dropped clauses can revive through exact resubmission.

A counterexample is the one place where `clauses` and `dropped` are tolerated
beside another variant's fields. Written as **empty arrays** they place no
clause and drop none, which is what the counterexample already says, so they
are ignored and the instance is judged on its own; written with any content
they are refused as `malformed_response` at `path: "$"` with the offending
members in `details.unexpected`, because a counterexample round runs no clause
epoch and can place nothing. Transcript replay reads a recorded response by the
same rule, so a submission the envelope admitted rebinds like any other. Both
members are still omitted by a proposer that writes the variant as it is
documented above.

B admits proposals and validates counterexamples. A receipt proves only byte
delivery. Correctable proposals receive a freshly bound correction; stale
responses fail.

A correction diagnostic carries `code`, `message`, `item_index` and `path`;
where the fault is inside a clause and admission located it, an `offset`; and
where the controller can say exactly which keys were wrong, a `details` object
`{missing, unexpected, changed}` listing key names at that `path`. Both
optional members are absent on a diagnostic that has nothing to put in them. A submission
whose binding is not the response example's is refused as
`wrong_response_binding` with `path: "$.binding"` and those three lists — so a
proposer that echoed the observation's shorter `feedback.binding` is told that
`request_digest` is missing rather than that its response is malformed. A
`binding` that is present but is not an object is refused at the same path with
every binding key listed as missing. A wrong `schema_version` is a separate
`wrong_response_binding` diagnostic at `path: "$.schema_version"`, because that
key is a top-level key of the response and not a member of `binding`; a
submission that gets both wrong receives both diagnostics. A
document that does not decode at all is refused as `malformed_response`, with
`path: "$"` and the variant's missing or unexpected top-level fields, or
`path: "$.kind"` when the kind itself is absent or unknown. `host_limit` keeps
its own separate `{limit, value, observed}` payload. Cancellation and resource faults take precedence over response
bytes and cleanup joins owned work before completion.

### Counterexample instance

Counterexample submission uses the raw task input schema, which differs from
evaluation's prophecy schema. The `input` value is
`{relations: [{name, rows}]}` and carries no other field. Each `name` is an
input relation of the task's source schema, spelled either as its canonical
schema name or with the ordinary-lift prefix `o:` the presentation's relation
table uses; both spellings resolve to the same relation, and a name outside the
source schema is refused as `unknown_relation`. `rows` is an array of tuples of
the relation's arity, and **every cell is a JSON string in the codec's
canonical domain-value spelling**: `num:<n>` for a natural number, `str:<text>`
for a string, and `bool:0` or `bool:1` for a Boolean. A bare JSON number,
boolean or non-canonical key is not a domain value and is refused as
`counterexample_rejected` with code `malformed` and the reason
`relation cell is not a valid domain value at /instance/relations/<i>/rows/<j>/<k>`.
The same spelling is what the `model` of a refutation answer already uses, and
the codec is `Whiel/Synthesis/Runtime/Task.lean`'s `SolverKey` key form, decoded
by `Whiel/Synthesis/FrameworkII/CounterexampleInstance.lean`. One example row,
for a binary edge relation `E`:

```json
{"relations": [{"name": "o:p::E", "rows": [["num:1", "num:2"], ["num:2", "num:1"]]}]}
```

Every other structural refusal — an omitted required relation, a repeated
relation or tuple, a tuple of the wrong arity, an unsupported field — comes back
as `malformed` with its own reason and the path of the offending member; only an
unrecognized relation name gets the separate `unknown_relation` code.

## C-local skills and native inventory

Skills, their files, enablement, retrieval and MCP presentation belong wholly to
C. The default catalog is empty. C's local `get_skill` returns `{id, content}`
or a local `unknown_skill` error; it carries no B state/evidence envelope.
Configure local skills in C using `WHIEL_AGENT_SKILLS_FILE`,
with a skill library directory (`index.json` and one Markdown file per skill)
or a JSON object mapping nonempty IDs to JSON guidance; omission disables
local skills. The index or JSON file is limited to 16 KiB and each skill file
to 32 KiB; the snapshot is frozen once per consultation. Skill contents remain in C and
are not included in B/native launch configuration. Changing this file requires
neither a Lean nor a Rust rebuild.
This loader adds no cross-task memory, folds or automatic solved-case storage.

B rejects an explicit semantic-query list containing `get_skill` with a
migration diagnostic. Other selected semantic queries retain their meanings.
C may advertise local skills with every B query disabled, or disable skills
while B queries remain enabled. Each wrapper/composition still passes each
constituent B query through B's permissions and accounting.

API 3 carries no model-facing tool inventory or native launch policy. C builds
its own MCP inventory and checks it against its native provider at launch.
Local skill traffic consumes C MCP budgets without a fabricated semantic query.
A generic proposer needs none of this native inventory machinery.

## Completeness of the read surface

As of 3.1.0 every fact the controller keeps per run that a proposer may see is reachable from
the push or from a single read query:

| Fact | Where |
| --- | --- |
| Clause text (the admitted canonical source, and the display spelling) | Every `ClauseRef`: `core[]`, `pending[]`, `last_round[]`, and the `clause`/`target`/`cause` of a `history`, `ledger`, `countermodel` or `strongest_refutations` row |
| Level | `core[].level`, `pending[].current_level`, `last_round[].outcome.level`, `history.current_level`, each check row's `level` |
| Minimum level | `pending[].minimum_level`, `history.minimum_level` (for a committed or dead clause, `history` is the one read that gives it) |
| Status: committed, pending, dead with its cause | `core[]`/`pending[]` membership, `last_round[].outcome`, `history.status` |
| Origin and the protected system-row flag | `core[].source`, `pending[].source`, `last_round[].source`; `history.origin` and `history.protected` |
| Epoch and placement history | `history.attempts` and `ledger` rows: ordinal, level, role, request and partition digests, whether the row was invalidated, and separate invalidation rows naming target, cause and reason |
| Check outcome with its role | Each check row's `role`, `result.outcome`, `result.attempt_id`, evidence route and profile, `solver_time_nanos` and `preparation_time_nanos` |
| Refutation detail | `strongest_refutations` (the inclusion-maximal antichain, with attempt, level, role and premise count) and `countermodel` (the validated finite instance, or the named retention limit that kept it out) |
| Drop authority | `pending[].drop_reference`, issued only for a clause this consultation may drop |
| Budgets and limits | `feedback.remaining_search_budget_ns`; `presentation.host_limits`, every limit in force with its value, empty when none is set; `presentation.resource_limits` |
| Task, schema, prophecy map | `presentation.task`, `presentation.ambient_schema` |
| Latest event | `feedback.latest`, including the refuted termination check's attempt |

Deliberately not exposed. Proof text and artifact paths are never published; a
successful check gives status and provenance only. The semantic dictionary, the
retry schedule and the controller's private validation manifest are internal;
the push publishes the digests that identify them, not their contents. A
catalog record no partition holds — provenance left by a rolled-back epoch — is
not shown as clause state, and reads of it return `status: null`. The
presentation carries no explanatory prose (see the 3.1.0 entry below).

Deferred, not missing by accident: there is no operation for
evaluating a program or an expression on an instance, no way to ask what would
follow from a hypothetical level assignment, no dictionary lookup, and no
dry-run of a check. `validate_clauses` and `evaluate_clauses` cover admissibility
and formula truth on retained or supplied instances; anything beyond them is a
new operation, and new operations are out of scope for this contract revision.

## Versioning and compatibility

### 3.2.0 — a correction that locates the fault, and two tool errors that name the shape

One compatible addition and three message repairs, in one checkpoint. No
accept, reject or drop decision changes, and nothing is computed differently.

A correction diagnostic may now carry `offset`, the position inside the named
clause at which admission failed. Lean has always computed it for every
lexical and syntax failure and the `validate_clauses` answer has always shown
it; the submission path dropped it, so a refusal named the clause's
`item_index` — of a list the proposer keeps no copy of — and nothing about
where in it to look. The field is additive, absent on every diagnostic that
cannot locate a fault, and a consumer that does not read it is unaffected.
`dead_clause_rejected` additionally names the dead formula in its message,
bounded to 512 bytes: the text is the proposer's own submission, so echoing
it leaks nothing, and without it "propose different content" names no content.

Two tool errors were dead ends and are now sentences a caller can act on.
`evaluate_clauses` answered an `instances` it could not decode with
`serde_json`'s untagged-enum text, which names a Rust type and no accepted
shape; it now states the two accepted forms. `countermodel`'s `no_refutation`
said the attempt had no recorded refutation, which is false of a check that
was refuted and reached by passing a ledger row's `row_ordinal` where its
`result.attempt_id` belongs; it now says which number to use.

Wire 3, proposal schema 4, feedback schema 10, presentation schema 16 and
worker format 11 are all unchanged, and a 3.0.0 or 3.1.0 client negotiates and
works exactly as before.

### 3.1.0 — clause text on every identity, and a presentation without prose

Two compatible additions and one removal, in one checkpoint.

Every clause identity the API exposes now carries the clause it names:
`canonical_source`, the exact source the verifier admitted in the clause
grammar, and `display`, the record's display spelling, either null only where
that text is unsafe to present. They appear in `core[]`, `pending[]`,
`last_round[]` and in every `history`, `ledger`, `countermodel` and
`strongest_refutations` clause reference, so a proposer can read every clause
the verifier shows it instead of keeping a private transcript of its own
submissions. Both fields are optional on ingress: a reference echoed whole out
of the push is accepted, one carrying the three digests alone names the same
clause, and text that disagrees with the named record is refused. `history`
additionally answers with the clause's `origin` and `protected` flag, which
completes the read surface against the controller state (above).

The task specification loses its ten tutorial strings — `clause_grammar`,
`system_clauses`, `prophecy_semantics`, `checks`, `core`, `pending_retry`,
`host_limits_note`, `death_rules`, `proposal_kinds` and the free-text `note`
inside `resource_limits`. Its structured content is unchanged: task, scope
digest, relation table, prophecy map, the host limits in force with their
values, the resource allowances and the presentation digest. Explanatory text
is the proposer's responsibility; B publishes the run's data, the paper
states the rules, and B enforces them. The rules those sentences carried
remain enforced and documented: an inadmissible clause comes back as a
correctable admission diagnostic; a drop of a Core or protected clause as
`core_clause_not_droppable` or `unauthorized_drop`, and a protected row is never
pending so never carries a drop authorization; a limit refusal as `host_limit`
with `{limit, value, observed}`; a quantified task's instance as
`not_quantifier_free`; and the two proposal kinds are the proposal schema's own
two variants.

Corrections also became actionable: a diagnostic may now carry a `details`
object naming the missing, unexpected and changed keys at its `path`, which is
what a binding refusal returns (see "Proposal channel"). The field is additive
and absent on a diagnostic that has nothing to name. Each disagreement is named
at the path it actually lives at: a wrong `schema_version` at
`$.schema_version` rather than inside `$.binding`, and a `binding` that is not
an object at `$.binding` with every binding key missing, instead of the generic
`malformed_response` sentence. This is the same revision's `details`, stated
exactly; no code, field or wire version changed with it, so a 3.1.0 client is
unaffected.

The counterexample instance's own spelling — the `{relations: [{name, rows}]}`
object, the two accepted relation namings and the canonical `num:`/`str:`/
`bool:` cell keys — is now stated on the API side under "Counterexample
instance". It documents the codec the verifier has
always enforced; nothing about what B accepts changed.

Feedback schema moves 9 → 10 and presentation schema 15 → 16; those push wire
versions are versioned separately from this semantic revision, and a strict
consumer of the old presentation must move with them. Wire 3, proposal schema
4 and worker format 11 are unchanged, and negotiation with a 3.0 client is
unaffected.

### 3.0.1 — retire native host compatibility

Removes the private native `host_support` exports and obsolete v2/MCP adapter
test coupling, while preserving the canonical B checks for every query. Native
execution/configuration/transport is Python C; B accepts only explicit generic
or no-proposer selection and emits schema 2 campaign records. This mechanical
patch changes no public query, wire 3 field, proposal 4 meaning or worker 11
operation. Existing 3.0.0 proposers negotiate and work unchanged. The API source
checkpoint includes its documentation and real-worker regression coverage.

### 3.0.0 — generic proposer communication boundary

Introduces incompatible process wire 3 under `src/proposer_api/wire/`: one
input-scoped endpoint, separately identified requests, optional queries, bounded
proposal receipts and provider-neutral completion/cancellation. It carries no
native provider/model configuration, prompts, conversation mode or MCP traffic.
All packet lengths, required-nullable fields, directions, bootstrap identities
and lifecycle rules are specified in the API directory. The coherent record
migration removes conversation policy from B and versions affected configuration,
feedback, transcript and replay identities.
The concrete dispatcher is physically `src/proposer_api/adapters/dispatch.rs`;
`framework2/mod.rs` loads that exact path without widening engine visibility.
The mechanical API source gate covers this adapter and its public declarations.
Legacy Rust tests used a finite v2 Python fixture under B;
that fixture and host are retired in 3.0.1.
The two A semantic queries, four B runtime reads plus observation, proposal 4 and
worker 11 retain their verification meanings. The old native host is explicitly
temporary and cannot accept wire 3 by falling back to its private v2 protocol.
The lifecycle prerequisite separates request quiescence from terminal
shutdown, propagates typed cleanup failures before admission/certification, and
exposes the controller's actual remaining local request budget. Its read-only
cancellation observer preserves the owner's first cancellation timestamp and
effective deadline, so delayed cleanup cannot relabel an external stop. Started endpoint
setup uses joined cleanup even when search construction fails. The revision
also removes conversation declarations and migrates the request/feedback policy domains,
run configuration 3, transcript 3, replay envelopes/projections 2, feedback 9 and
presentation 15 with strict rejection of incompatible historical records.
`proposer_observation` carries the same semantic information. B records only API
traffic and request lifecycle; C owns native conversation records. The artifact
`session_digest` remains an immutable provenance identity, not conversation state.
Typed terminal endpoint faults stop the run after joined cleanup; ordinary
source exhaustion remains lane-local, and resource failures keep their separate
classification. The generic host is the production path as of 3.0.1.

### 2.0.3 — retire the crate-private Rust C transport exports

Removes the temporary v1 transport re-exports from the crate-private
`host_support` module when C moves to Python and B uses process protocol 2.
This patch changes no public semantic declaration, query schema, observation,
proposal meaning or negotiation behavior. The six read queries remain optional.
Python AgentHoudini talks to B through v2; the generic direct proposer profile
remains independent of MCP/native CLI. Old Rust C module paths are retired.
The campaign request enum now stores unresolved optional model/effort choices;
its old Rust literals and direct C imports require deliberate source migration.
CLI selections/defaults remain unchanged and are checked by the bounded Python
configuration helper before output; B checks explicit returned choices.


### 2.0.2 — relocate native process host enforcement to B

The crate-private `host_support` compatibility exports now refer to B-owned
native supervision, identity/startup restrictions, v1 wire declarations and
bounded name-inventory validation in `src/proposer_host/`. The temporary Rust C
client retains its imports; no query, observation, proposal or capability wire
meaning changes. C still owns prompts, catalogs, aliases and skill content.
This patch records an internal API-source relocation; the separately versioned
process protocol 2 is introduced and verified on its own.

### 2.0.1 — complete the versioned public source boundary

The provider trait, immutable push, cancellation observer, bounded response sink
and strict proposal DTOs are now declared in `src/proposer_api/`, alongside the
query and observation contracts. Engine construction, checking and transcript
authority remain private to B. The public signatures and wire formats are
unchanged; this compatible source relocation is a patch. Engine paths keep
compatibility re-exports for existing B callers. The provider source module is
nested under B to retain compiler-enforced private push/sink assembly while its
file and public declarations remain in the gated directory. Raw ingress schemas
and wire-version/host-limit-name vocabulary also live in that directory.

### 2.0.0 — separate semantic queries and local skills

The supported major is 2; API 1 clients fail negotiation before consultation.
Validation accepts only clauses; evaluation requires explicit retained, supplied
or all-retained sources. `get_skill` is C-local and absent from B's schema and
replay. History's required status/current-level fields may be null for catalog
provenance retained after rollback. These changes are incompatible with strict
API 1 decoders and are intentionally a major migration. Worker format 11,
proposal format 4 and bridge format 1 are unchanged.

Within a supported major the current schema remains fixed. Compatible future operation
additions are exposed only when the client declares them; new fields/enum
variants cannot be emitted to strict older clients without explicit projection
or another major migration. Version negotiation alone does not perform arbitrary
schema conversion.

### 1.0.1 — typed observation and scoped-reference implementation

Moved strict observation DTOs into the API directory; B now supplies their
immutable typed snapshot. Added optional capability negotiation, independent
read-reference resolution and the mechanical version/documentation gate.
This implements the 1.0.0 contract without changing verification semantics.

### 1.0.0 — explicit API contract

Initial maintained contract. Every API-directory change requires a strictly
newer semantic version and a matching version entry here, with corresponding
changed Layer A/schema examples. Incompatible contracts
bump major, compatible optional additions minor, compatible fixes/internal
source or fixture changes patch. One coherent checkpoint needs one bump.
`scripts/check_proposer_api_version.py --base REF` checks tracked and working
changes against the explicit base, including addition, rename and deletion.
Public-interface tests through real Lean complement this mechanical gate.

Startup negotiation selects a common API major/minimum supported version and
operation intersection. C declares supported and required operations; required
unsupported/forbidden operations and incompatible major versions fail clearly.
A compatible minor/patch update never forces old C to consume new fields, enum
variants or tool names. The operation inventory projects only supported operations; existing schemas
remain fixed within this compatibility boundary.
Capabilities never increase B authorization. Queries remain optional.

These checks do not prove semantic equivalence of the entire Lean dependency
graph. The internal worker format stays 11 and proposal JSON stays 4. Generic
process wire 3 is versioned separately from the semantic API; native MCP
transport is private to C.

## Trust boundary

B owns the semantic checks and generic process boundary; C owns native agent
execution. This source/API separation is not an OS sandbox against deliberately
hostile Python. See [collaborator boundaries](collaborator-boundaries.md).
