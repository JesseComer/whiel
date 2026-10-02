# Code and trust boundaries

The editable agent harness is `agent_houdini/`. Houdini exposes a proposer API
from `whiel_runner/src/proposer_api/`. The harness requests information and
submits proposals through that API; Houdini retains authority over what enters
its state and what passes checking.

## Three components

| Component | Source | Responsibility |
| --- | --- | --- |
| A — Lean | `Databases/`, `Whiel/` | Definitions, formula transformations, worker operations, semantic theorems and proof checking. |
| B — verifier/certifier | `whiel_runner/` | Houdini, clause admission, Core/Pending/Dead, dictionary/countermodel retention, API authorization and queries, worker scheduling, generic endpoint lifecycle, API/verifier resource limits, certification and publication. |
| C — proposer | `agent_houdini/` | Python provider execution and identity checks, agents/models, auth, conversations, prompts, MCP, sandbox, skills, experiment controls, agent-specific pins and logs. |

The API is the entire communication boundary, including process messages,
observations, query results, proposal receipts and lifecycle. B accepts a generic
executable/argument vector and never assumes AgentHoudini, Python or an LLM.
C's launcher owns agent-facing command options and may invoke B's documented
public command. Its endpoint mode is separate, avoiding recursive launches.
The implementations need not be separately published packages to obey this rule.

`whiel_runner/src/proposer_api/` owns the public contract, including `wire/`
framing/lifecycle and `adapters/` for scoped requests and result conversion.
Private generic process I/O can stay in `proposer_host/`. That host must not
inspect model identities, credentials, prompts, MCP or conversation state.
C owns its native children and ordinary cleanup; B retains bounded endpoint
shutdown and provider-neutral process-tree fallback if C fails.

## What collaborators can improve

- Change instructions, examples and feedback presentation in C. Keep the exact
  current response binding and use the bounded submission channel.
- Change C's agent lifecycle, model selection, native checks, authentication,
  MCP translation, prompts, sandbox or response handling. C owns the native
  launch and its agent-facing information selection. These changes must need
  no Rust rebuild or edit outside C when they use existing API capabilities.
- Add, remove or combine MCP wrappers over the existing engine queries. Every
  constituent query still passes the engine's policy and scope checks. A wrapper
  cannot create a new semantic operation by inventing a backend tool name.
- Add procedural synthesis guidance to C's local skill catalog, configured with
  `WHIEL_AGENT_SKILLS_FILE`. C serves `get_skill` without a B query or evidence
  envelope. The catalog is an immutable snapshot read once per consultation,
  with nonblocking open, regular-file checks and fixed byte bounds. The default
  catalog is empty; no solved-case database is loaded.
- Add or reorganize C modules, helpers and its own runtime dependencies. C's
  source tree is discovered rather than pinned in a B-owned module list.

Use [the API and customization guide](proposer-api.md) for the exact module map
and extension points, and [tools and skills](tools-and-skills.md) for query
semantics. If evidence selection, clause admission or a Houdini transition looks
wrong, retain a minimal reproducer and request an engine fix. Do not compensate
by altering trusted evidence or pretending a query succeeded.

## What the API protects

A proposer gets an immutable observation, a request-scoped query capability,
cancellation and a bounded response channel. It does not get the Houdini object,
a mutable catalog, a checker or an admission service. Queries can invoke Lean
and affect worker/cache/resource bookkeeping; they do not install clauses or
advance Core/Pending/Dead or the semantic dictionary. Houdini processes a
submitted proposal after receipt and completion. A transport receipt confirms
complete bytes, not semantic admission or certification.

One endpoint spans the input's successive requests/corrections. Request closure
revokes its capability and joins in-flight verifier work without terminating
the endpoint. C can reuse or replace its internal agent conversations; neither
choice extends a closed request. Terminal shutdown retains generic failed-C
cleanup, including detached descendants. Old requests cannot regain authority.

The six optional read queries are `countermodel`, `strongest_refutations`,
`history`, `ledger`, `validate_clauses` and `evaluate_clauses`. A proposer may
ignore any available query. C's `get_skill` is local guidance, not an additional
Lean or B query, and does not depend on enabling B's optional queries.

B constructs canonical feedback, identities, digests and bindings. C selects
and formats available information for its agents and delivers their prompts
directly. It must echo authoritative bindings exactly in submitted proposals.
Saved countermodels remain bound to their original checks, and draft evaluation
remains an observation rather than an inductiveness or proof verdict.

B accounts for API traffic and verifier work and records API/evidence history.
C separately accounts for agent/MCP work and records prompt digests, bounded
C source and sanitized command identities, stdout event counts and redacted
diagnostics. These C records are not certified evidence.

## Auditing the partition

`scripts/check_proposer_boundary.py` checks the supported C Python source
style and rejects recognized private engine/source-loading bypasses. It allows
ordinary C subprocesses, sockets, files, helpers and dependencies. The product
path and API-version checks protect A/B compatibility; changing C alone must
not require updating B-owned inventories or golden agent outputs.

These checks are review controls. They are not a code security proof, OS
sandbox, filesystem ACL or GitHub permission setting. Running C as a host
Python process does not isolate it from deliberately hostile source edits.
The harness also performs real I/O work and owns the isolation that prevents
its agents reading certificates or other forbidden experiment data. Computing
denied paths for sandbox diagnostics is different from reading those sources.
These static conventions cannot prove arbitrary Python harmless.

For a stronger runtime boundary, use an immutable engine deployment and OS
isolation. See [provider limitations](providers-and-auth.md).

## Third-party dependencies

Vampire's [BSD 3-Clause license](https://github.com/vprover/vampire/blob/master/LICENCE)
permits source/binary redistribution with modifications, subject to retaining
copyright, conditions and disclaimer and respecting its non-endorsement clause.
Preserve notices and provenance for patches and included third-party components.

[VampLean](https://github.com/vprover/vamplean) is a separate upstream Lake
dependency, pinned in `lakefile.toml`, `lake-manifest.json` and
`toolchain.lock.json`. Whiel does not vendor or modify its source. Preserve
upstream attribution and applicable notices when packaging dependencies;
Vampire and VampLean remain distinct projects. See the
[setup notes](../README.md#linux-setup-and-builds) for the compatible Lean version and
the retained local Vampire patches.
