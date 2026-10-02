# Tools, feedback and synthesis skills

This guide follows the maintained [proposer API](proposer-api.md).
B publishes an immutable observation containing task/schema and clause grammar,
current Core and pending/dead information, latest result, previous-round outcomes,
identities, limits and enabled queries. C chooses what API-exposed information
to show its agents and how to format it. The API does not prescribe a model
prompt. Corrections carry a newly bound request.

## Semantic queries and local tools

Six optional queries comprise two Lean-backed semantic operations and four
runtime reads; the pushed observation is the fifth B information facility.
`submit` is the separate response channel. C may additionally expose its local
`get_skill` tool. C owns MCP names, descriptions, aliases and presentation; each
underlying API query retains its own permission and argument contract.
Query replies contain `tool`, `state_revision`
and either `result` or `error`. Inspect the inner error even when the outer MCP
transport succeeded. Queries never commit clauses or reveal proof files.

| Tool | Arguments | What it does |
| --- | --- | --- |
| `countermodel` | `{"attempt": a}` | Retrieve the Lean-validated relation tables for one saved refutation, or an explicit retention omission. No new solver run. |
| `strongest_refutations` | `{"clause": C}` | Return initialization/maintenance refutations whose full tagged premise sets are inclusion-maximal, separately by role. |
| `history` | `{"clause": C}` | Status, minimum/current level and all clause-check rows, oldest first, including invalidated history. Not paged. |
| `ledger` | `{}` or `{"cursor": s}` | Newest page of the run's clause-check/invalidation chronology, then older pages using the returned continuation. Rows in each page are oldest first. |
| `validate_clauses` | `{"clauses": [source,...]}` | Lean-admit drafts and return canonical source or diagnostics, without instance evaluation. |
| `evaluate_clauses` | `{"clauses": [source,...], "instances": selection}` | Evaluate exact formulas on explicit tagged retained/supplied instances or `"all_retained"`. |
| `get_skill` | `{"id": s}` | C-local procedural guidance; only advertised when configured. No B state envelope or evidence authority. |
| `submit` | `{"payload": "complete response JSON"}` | Deliver exactly one bound clause/drop proposal or concrete program-input proposal to the controller. Receipt is not acceptance. |

`C` is the complete identity supplied by feedback: `clause_id`, `record_digest`,
and `formula_digest`. Do not reconstruct it from source text or invent its hashes.
An attempt ID identifies a physical check/refutation, not a ledger row ordinal:
semantic dictionary reuse can produce later rows using the same attempt.

## Interpret countermodels correctly

If a check refutes `T ⊨ q`, its model satisfies the complete antecedent `T` and
falsifies `q`. For initialization, `q` is the clause; for maintenance it is the
clause's weakest precondition under the body; for termination it is the lifted
postcondition. Such a model need not be a reachable program state. It is not
by itself a counterexample to the original Hoare triple. A concrete input
submitted through the counterexample response goes to the separate Lean checker.

Strongest means maximal **premise-set inclusion**, not newest attempt, highest
level, largest model or most difficult solver case. Tags distinguish ordinary
and prophecy clauses and fixed premises. Equal premise sets contribute one
entry; incomparable sets can all survive. Current replies expose premise counts,
not the full sets. A configured result/retention limit is explicitly reported.

The ledger records requested clause checks, including dictionary reuse. It is
not a raw process log or complete dump of the semantic dictionary. Missing solver
timing does not prove a cache hit; there is no explicit hit flag in this wire.
The dictionary is run-local across epochs. Termination is in the latest pushed
event, not synthesized into clause ledger rows; its refutation attempt can still
be queried through `countermodel`.

## Interpret draft evaluation

`evaluate_clauses` requires `instances`: either `"all_retained"` (newest first)
or an explicit array of `{"kind":"retained","attempt":17}` and/or
`{"kind":"supplied","instance":...}`. Order and duplicates are preserved;
`[]` evaluates no instances. Omitted/null selection is rejected. Use
`validate_clauses` for admissibility alone. Unknown/non-refuting retained IDs
reject the call. Supplied data must cover the complete prophecy schema; its
well-formedness implies no reachability or correctness. See the
[finite-instance contract](lean-runtime-api.md). There is no implicit relevance
or role filter.

Lean evaluates each admitted draft exactly as written. It does not automatically
apply weakest preconditions, prophecy lifting or collapse, or recheck the saved
check's hypotheses. A maintenance countermodel can satisfy the original clause
while falsifying its weakest precondition. A supporting ordinary clause false
on that model might exclude it in the relevant hypothesis set; checking a lower
level's terminal fact instead requires the appropriate prophecy formula.

`holds` vectors align with returned `instances`. Failed admissions have correction
diagnostics. `skipped` names models unavailable for evaluation, including retained
models whose row values do not provide enough carrier information for the
current conversion. Omitted data is not fabricated truth. Boolean observations
neither add a draft to Core nor prove inductiveness.

## Core, pending clauses and output authority

Committed clauses belong to Core at their recorded levels. Pending clauses have
not passed all required checks; an inconclusive result is not a refutation or a
proof, and pending clauses do not gain Core authority by being shown in feedback.
The displayed pending level describes the completed scan; the next clause epoch
resets pending clauses to their minimum level. It does not mean every lower
level was refuted: checks can be inconclusive or suspended. A dead clause is
dropped or refuted, with its historical reason retained.

Copy the response skeleton and exact current binding from the prompt. A clause
response contains protocol version, `kind: candidate_clauses`, `binding`,
`clauses`, and authorized `dropped` references. The input variant uses
`kind: candidate_counterexample` and `input`, and omits `clauses` and
`dropped`; left in empty they are ignored, and carrying content they are
refused. Do not send solver proof text or
construct certificate paths. A bad envelope or correctable proposal receives
feedback; a new binding must be used for the correction. Closing prose never
substitutes for `submit`, and an MCP acknowledgment means only that bytes arrived.
The current concrete-input route requires quantifier-free pre/postconditions;
unsupported grammar yields explicit feedback, not a guessed verdict.

## What a skill should contain

A skill is a procedure: when it applies, which task features to inspect, how to
construct a candidate, which query tests it, and how to interpret the next
failure. It is not just a cached solved clause, an executable hook, or a proof.
C's catalog in `agent_houdini/skills.py` is empty by default. Set
`WHIEL_AGENT_SKILLS_FILE` to a skill library directory (`index.json` plus one
Markdown file per skill; `agent_houdini/skills/v1/` is the hand-written one)
or to a JSON object mapping IDs to guidance. C freezes the catalog per
consultation, lists its index in the prompt under `# Skills` and serves local
`get_skill` without B semantic calls. This does not port a legacy solved-skill
database, cross-task memory or folds.

The following ideas are adapted from Fangzhu Shen's legacy synthesis guidance.
They are heuristics whose instantiations still require ordinary Lean admission
and unchanged Houdini checks:

| Template | Procedure and caution |
| --- | --- |
| Bounds | Try a postcondition containment `X ⊆ Bound` at loop heads; inspect initialization and preservation, and look for a supporting frame fact. It is not automatically invariant. |
| Lagged closure | When closure holds only at exit, replace the relevant left-side accumulator with its declared previous-iterate snapshot. Use the actual guard to justify the exit connection. |
| Frame | Consider facts only over retained-input relations that the loop never assigns. The fixed-ambient framework already protects preconditions as assumptions; do not resubmit those facts as candidate invariants merely to preserve them. Use the protected assumptions when designing support for changing accumulators. |
| Delta/frontier coupling | Relate one-step extensions of the accumulator to the accumulator plus frontier extensions; test how an empty frontier yields closure. Add appropriate seed/frontier containment candidates. |
| Mutual simulation | For synchronized programs, propose containments linking their two step shapes. Equality alone may not be inductive; consider declared snapshots and both directions. |

Do not copy task-specific successful clauses into an evaluation intended to test
transfer. Label hand-written templates, learned procedures and solved-case data
separately in any future experiment. Procedural content can be added within the
[agent harness](proposer-api.md#c-local-skills-and-native-inventory), retaining
the engine's policy and request-scope checks for every API query. The semantic dictionary, evaluator and certificate checker remain
outside that editable boundary.
