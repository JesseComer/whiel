# K1 record migration freeze

This inventory is frozen with API 3.0.0/wire 3 in K1a.1. K1a.2 changes the
controller producers, strict decoders and comparison code coherently. K1b uses
the new records; K3 switches campaign production and deletes temporary native
paths. No migration code may silently reinterpret old persisted evidence.

| Record | Old | New fields/identity | Producers and consumers |
|---|---|---|---|
| Public process frame | host wire 2 | wire 3; exact `README.md` schema, one endpoint and request identity | `proposer_api/wire`, generic host; C client after reviewed K1 |
| Request policy | `whiel-agent-consultation-policy-v4` | `whiel-proposer-request-policy-v1`; retain `max_request_bytes`, `max_correction_diagnostics`, `max_correction_bytes`, `max_attempt_history_records`, `max_transport_retries_per_request`, nullable `max_consultations`; remove `session_mode` | `framework2/agent.rs`; `ReplayRequestPolicyFields` capture/verify in `replay_correspondence.rs`; request/policy digests |
| Feedback policy | `whiel-agent-feedback-policy-v4` | `whiel-proposer-feedback-policy-v1`; same limits/host-limit fields, newly named API resource fields and B-only accounting meaning | `feedback.rs::policy_fields`, `ReplayPolicyFields` capture/verify in `replay_correspondence.rs` |
| RunConfiguration | kind `whiel_framework_ii_run_configuration`, version 2 | same kind, version 3; retain `compress_core`, nullable `level_bound`, `retry_policy`, `casc_portfolio`, `tools`, `retention`; remove `session_mode` | `publication.rs`, `search.rs`, campaign results and replay owner capture |
| ReplayRunConfiguration | version 2 and `ReplaySessionMode` | version 3; exact new RunConfiguration fields; remove `ReplaySessionMode` | strict capture/round-trip verification in `replay_correspondence.rs` |
| B transcript header/frame | version 2 | version 3; header `provider_identity` becomes `proposer_identity` (opaque endpoint label, never authenticated agent provenance), `agent_protocol` becomes `proposal_schema`; other source-run and B pin fields retained; frame layout retained | `transcript.rs`, `replay_audit.rs`, recording integration and transcript fixtures |
| B transcript streams | Push/Response/Correction plus native Child* | retain Push/Response/Correction only; native prompt/argv/stdout/stderr/closing prose belong to C logs | `transcript.rs`, replay byte comparison, legacy native call sites isolated until K3 |
| B transcript lifecycle | fresh/continuous/continuing plus request lifecycle | `request_started`, `request_cancelled`, `request_panicked`, `cleanup_joined`; remove conversation lifecycle; child-start/exit records removed from the B schema | `agent.rs`, `transcript.rs`, `replay_audit.rs`, replay comparisons |
| ReplayPushProjection | version 1 | version 2; `agent_policy` -> `request_policy`, `agent_policy_digest` -> `request_policy_digest`; new request policy domain | capture/bounded capture, strict decode, digest reconstruction and compare in `replay_correspondence.rs` |
| ReplayFinalStateProjection | version 1 | version 2; same policy field rename/domain; nested v3 run configuration | `replay_correspondence.rs`, `replay_audit.rs`, final-owner comparisons |
| ReplayOwnerProjection | version 1 | version 2 because nested run configuration and feedback resource meaning change; no provider metadata | `replay_correspondence.rs` capture/verify and wire/replay comparators |
| State/catalog/backend/evidence projections | unversioned structural types and existing component version 1 | unchanged fields/semantic identity; no new provider information or altered proof evidence | `replay_correspondence.rs`, `replay_production_compare.rs` |
| Replay comparison envelope | version 1 | version 2; compares new B-only API/evidence transcript identities | `replay_audit.rs` writer/reader and fixtures |
| Feedback/presentation | feedback 8, presentation 14 | feedback 9, presentation 15; observation operation `proposer_observation` replaces `agent_houdini_push`; same semantic data, `provider_frame_bytes` -> `api_packet_bytes`, `provider_traffic_bytes` -> `api_traffic_bytes`, `provider_messages` -> `api_messages`; resource description states API transport/verifier resources only | `proposer_api/version.rs`, `observation.rs`, `feedback.rs`, strict replay header/DTO checks |
| Campaign settings/summary and input results/resource file | settings/summary schema 1; input result/resource files unversioned | schema 2; generic verifier configuration, endpoint label and API diagnostic only; native settings/results in C-owned output | exact old/new producer objects and reader mappings frozen below, production switch K3 |
| Proposal/worker/certificate | proposal 4, worker 11, checked-in supported certificates/Core/Counterexample | unchanged semantics and supported input consumption; new requests derive fresh bindings | proposal, encoding and certificate gates |

The exact generic campaign schema-2 field inventory is:

| File/object | Fields and production point |
|---|---|
| `campaign-settings.json` | `schema_version:2`, `inputs:string[]`, `controls:Controls`, `proposer:EndpointSelection|null`; `execute_campaign_run_cli` |
| `resource-limits.json` | `schema_version:2`, `limits:ApiResourceLimits`; replaces the unversioned resource object in `execute_campaign_run_cli` |
| `summary.json` | `schema_version:2`, `interrupted:bool`, `all_certified:bool`, `resource_failure:string|null`, `selected_inputs:string[]`, `unrun_inputs:string[]`, `campaign_controls:Controls`, `results:InputResult[]`; `run_selected` |
| each `result.json` | `schema_version:2`, `input:string`, `status:string`, `campaign_controls:Controls`, `proposer:EndpointSelection|null`; status-dependent payloads listed below; `run_one`/`run_selected` |
| `Controls` | existing `search_limit_seconds`, `certification_limit_seconds`, nullable `consultation_limit_seconds`, `transport_retries`, `certificate_solver_limit_seconds`, `counterexample_validation_limit_seconds`, nullable `iteration_limit`, `workers`, `resource_limits:ApiResourceLimits`; `campaign_controls` |
| `ApiResourceLimits` | `api_traffic_bytes`, `api_messages`, `artifact_bytes`, `artifact_files`, `workspace_bytes`, `workspace_files`, `minimum_free_bytes`, `workspace_entries`, `workspace_directories`; same integer types/defaults, B-owned accounting only |
| `EndpointSelection` | `executable:string`, `arguments:string[]`; null for the generic exhausted/no-proposer diagnostic; opaque caller-selected launch metadata, never inspected agent provenance |

InputResult keeps the current checked status vocabulary and payloads: `valid`
has `certificate` and `axioms`; `invalid` additionally has `counterexample`;
`search_timeout`, `interrupted` or `incomplete` may carry the existing engine
`failure_kind` and `detail`; `certification_timeout`, `certification_failed`,
`resource_exhausted` and `failed` carry the existing `detail`. Generic endpoint
failures use these engine failure paths, not a new native diagnostic object.
There is no `provider_identity`, `provider_diagnostic`, model/effort/CLI/isolation,
session setting or bridge path in these new B records. C records its own such
settings and logs independently. Certificate paths/axioms and engine failure
classification preserve their prior meanings.

K3 updates the producers in `campaign_run.rs`, the corresponding CLI/config
types in `campaign_cli.rs`, their library tests, `framework2_campaign_cli.rs`
and `framework2_fixed_ambient.rs` consumers together. Searches at the K1a.1
baseline found no current Python consumer of these schema/identity fields;
that search is repeated at cutover to catch newly introduced readers. New
schema-2 examples and negative old schema/unversioned fixtures are mandatory.
Do not merely delete fields under an old identity. Use fresh isolated output
directories; no original experiment or benchmark artifact is rewritten.

Feedback's `presentation_digest` and request bindings are freshly computed after
their changed data is constructed. B's verifier identity must not contain a C
source-file inventory, golden prompt or model pin. The generic selected endpoint
may have a separately recorded opaque label; it cannot authorize evidence.
The existing `session_digest` in feedback/replay identifies an artifact backend
via `whiel-agent-feedback-session-v2`; it never encoded conversation state.
Its fields/domain and related artifact-reference identities remain unchanged.

Changed objects reject their previous version/domain before use. Unsupported
old experiment/replay artifacts stay intact and can be inspected with the old
recorded repository revision. The implementation adds negative old-version
fixtures and new producer/decode/compare round trips for every changed row.
Historical source names containing `Agent` are not permission to preserve native
agent semantics. No mathematical or checked-certificate format change is in
scope; an unavoidable certificate contradiction requires owner escalation.

The temporary v2 native frontend's explicit `2.0.3` query declaration in
`proposer_host/native_process.rs` exists only to keep the old default runnable
while the generic endpoint is built. Its six queries remain unchanged. It is
not capability negotiation or a compatibility fallback for wire 3. K3 removes
the entire legacy native host, rather than leaving it as an alternate path.

The lifecycle prerequisite also exposes a defaulted typed terminal endpoint
status, separate from resource and cleanup failures; the controller checks it
before admission to prevent retrying a dead endpoint indefinitely. Legal packet
receipt remains `submitted` when the bounded proposal writer hits `reply_bytes`;
that overflow follows its existing controller `host_limit` correction after
request close. Neither case adds a semantic operation or changes a proof verdict.
