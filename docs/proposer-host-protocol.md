# Proposer process protocol

The proposer boundary uses **API 3.1.0 / wire 3**. Its complete process
contract, strict packet declarations and migration rules live together under
[`proposer_api/wire/`](../whiel_runner/src/proposer_api/wire/README.md). The
generic endpoint is the only production path; native execution and the
standalone MCP relay are Python C.

B starts an explicitly configured proposer executable and argument vector.
One endpoint handles successive requests for one input. B supplies immutable
observations, serves permitted read-only queries, receives proposals and joins
request work before closing each request. Endpoint shutdown is separate, with
generic process-tree cleanup on failure. All these messages belong to the API.

C owns agent execution, prompts, MCP, configuration, sandbox, conversations and
native traffic. It formats the observation and communicates with its agents
directly. No rendered prompt or raw MCP traffic returns through B. Wire 3 has
no provider-specific operations and no fallback to the old native protocol.
The semantic meanings remain in [proposer-api.md](proposer-api.md).

As of API 3.1.0 the observation carries the data of the run and none of its
explanation: every clause identity B shows carries the admitted clause text,
and the standing presentation no longer ships tutorial sentences about the
grammar, the checks, the host limits or the proposal kinds. Those rules are
stated in the paper and enforced by B; wording them for an agent is C's work,
as every other word of the prompt already was. The wire, its packet framing
and its lifecycle are unchanged by that revision.

## Recorded consultations

Under `--retention all` B records the traffic it exchanges with C and publishes
that recording as run artifacts. Recording is owner-held and provider-neutral:
it copies the bytes that crossed this boundary and the host's own projection of
each push, and it names no model, vendor or endpoint. The proposer identity in
the header is a digest of the endpoint selection the campaign already wrote to
`campaign-settings.json`, never a command line.

Each record is one `runtime_trace` artifact, published under the scope
`["root", "consultation-records"]` so a manifest reader selects the chain and
nothing else, and holding a frame
`{version, ordinal, previous_digest, payload}`, with `payload` the bytes of a
JSON record: the opening `header`, one `event` per frame after it, and a final
`closed` record giving the event count and any replay ineligibility. Every
frame carries the SHA-256 of the previous frame, so the chain is checkable from
the run's own files. The header pins the run's task, source, scope and
consultation policy alongside the verifier, worker, Lean, Vampire and
certification-profile digests the host verified. Events carry the push and
response byte chunks with their accounting, tool calls and their replies,
request lifecycle, the controller's attempt outcome, the provider's own
outcome, and the final owner projection of the run's state.

A fixed deny-list redacts credential-shaped bytes before any digest or
publication, length-preserving, and a redacted recording is marked ineligible
for replay rather than silently altered. Recording is bounded by the run's API
traffic allowance; exhausting it ends the consultation with a recording
failure, so no partial recording is published. Publication is equally all or
nothing where it can be: every frame is written into staging before any of them
is promoted, so an artifact byte or file budget that refuses the set promotes no
frame. Only a failure during promotion itself can leave a chain-valid prefix
with no `closed` frame, and then `result.json` reports the error together with
the number of frames that were promoted. The default retention records nothing
at all.
