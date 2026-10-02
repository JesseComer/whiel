# Generic proposer process contract, wire 3

This is the API 3.0.0 contract frozen in K1a.1. K1a.2 migrates the controller
records and K1b implements its production host. The old private v2 native host
is temporary migration code, not a v3 fallback. Worker 11 and proposal 4 retain
their semantics. `mod.rs` is the strict Rust wire declaration; this document
defines lifecycle behavior which the generic host must enforce.

## Bootstrap and lifetimes

B starts the caller's explicit executable/argument vector without a shell. It
passes two environment variables: `WHIEL_PROPOSER_SOCKET`, an absolute path to
an input-scoped Unix socket, and `WHIEL_PROPOSER_TOKEN`, 64 lowercase hexadecimal
characters freshly chosen by B for this endpoint. The socket directory is owned
by B and inaccessible to unrelated users. These values are API capabilities,
not credentials for any model. C connects once. Neither path nor token comes
from a repository/provider-specific convention. There is no provider registry,
hardcoded Python script, model selection or native-agent argument in B.

The full-duplex connection and C process persist for one verifier input. A new
endpoint, including a restart, gets a new token. Each new B request gets a new
strictly increasing `request_id`, starting at 1; request IDs never recur in that
endpoint. An endpoint can complete many requests without restarting C. No agent
conversation or native process lifetime is implied by a request boundary.

C owns its native descendants and ordinarily stops their request-specific work
on cancellation, then joins them at endpoint shutdown. It may retain idle
descendants and internal conversations between requests. B revokes and joins
its request-owned API/worker work at each request boundary; B does not kill the
endpoint on normal request closure. B retains a generic process-tree fallback
on endpoint crash, ignored cancellation/shutdown or incomplete cleanup, including
detached descendants. Endpoint cleanup failure cannot be reported as success.

## Packet format

Every packet is a 4-byte big-endian unsigned header length, that many UTF-8 JSON
bytes, and binary attachments in the order declared by its operation. There is
no newline delimiter and no base64 expansion. The header is exactly:

```text
{wire_version: 3, endpoint_token: string, sequence: u64,
 request_id: u64|null, operation: Operation}
```

`request_id` must be present. It is null only for endpoint-scoped messages. All
other messages carry the positive ID of the one active request. B and C each
start their own send sequence at 0 and advance by exactly one per packet across
the entire connection, including request boundaries. A receiver checks identity,
direction, scope, sequence and phase before using the message. Increment overflow
ends the endpoint; counters never wrap. No role/native-relay channel exists.

All headers are bounded to 16 KiB before allocation. The small control messages
listed below have a stricter 1 KiB header bound. Prefix, actual encoded header
and **all** attachments together must fit within 64 MiB. This aggregate bound
is checked before allocating or reading attachments; two 64 MiB attachments are
not permitted. Attachments have exact declared lengths, and truncated input is
a failed endpoint. An oversized header is never read into an unbounded buffer.

Header JSON is strict: valid UTF-8, one complete value, exact types, required
fields, no duplicate or unknown keys at any nesting level. Query arguments are
bounded bytes interpreted by the selected public query's strict decoder;
malformed arguments receive its normal error when transport framing is valid.
Proposal attachments are exact bytes, including empty or malformed bytes. Only
B's proposal validator interprets them: a transport receipt never asserts that
they are well-formed JSON, an admissible proposal or a valid certificate.
Observations, proposal examples and query results produced by B are UTF-8 JSON.

These bounds describe B–C API transport, not C's MCP lines or native-agent
traffic. B accounts for actual API traffic. Only bounded lifecycle controls
needed to cancel/close after a resource fault may bypass the exhausted traffic
allowance; that exception cannot carry data or sustain an unbounded conversation.
C separately accounts for its internal traffic, files and native resources.

## Operations

An operation is a strict tagged JSON object using `kind` and the fields below.
`u32` byte lengths must also satisfy the aggregate packet bound. Endpoint-scope
operations use null request ID; all others require the active ID.

| Direction | Kind and fields | Attachments | Scope/control |
|---|---|---|---|
| C to B | `hello {capabilities: ApiCapabilities}` | none | endpoint |
| B to C | `ready {api: NegotiatedApi}` | none | endpoint |
| B to C | `request {observation_bytes:u32, response_example_bytes:u32, remaining_request_budget_ns:string|null}` | observation, exact proposal example | request |
| C to B | `query {query_id:u64, name:string, args_bytes:u32}` | arguments | request |
| B to C | `query_result {query_id:u64, result_bytes:u32}` | public query result/error | request |
| C to B | `submit {bytes:u32}` | exact proposal bytes | request |
| B to C | `submitted {}` | none | request/control |
| B to C | `rejected {code:"too_large"|"duplicate_submission"}` | none | request/control |
| C to B | `complete {outcome:"response"|"source_exhausted"|"no_response"|"failure"}` | none | request/control |
| B to C | `request_closed {}` | none | request/control |
| B to C | `cancel {reason:"deadline"|"cancelled"|"failure"}` | none | request/control |
| B to C | `shutdown {reason:"complete"|"cancelled"|"failure"}` | none | endpoint/control |
| C to B | `closed {}` | none | endpoint/control |

`ApiCapabilities` and `NegotiatedApi` use the declarations in `negotiation.rs`.
Handshake starts with C's hello at C sequence 0, then B's ready at B sequence 0.
Unsupported major, invalid declarations or unavailable required queries fail
before a request. Negotiation only narrows B's permitted six-query set. Optional
future queries need not be used or advertised by C; C-local tools never enter
this inventory. No request, query, submission or second hello precedes ready.

The request budget field is required and nullable: null means no separate
request deadline; a non-null value is canonical decimal nanoseconds in `u64`
range (`"0"` is valid, leading zeros/signs/whitespace are not). It is the remaining
budget when B constructs the request, not a new clock or a deadline C can extend.
The observation still carries the search budget. B remains the timing authority.

## Request state and receipts

1. B sends request only while no request is active, after handshake. C may inspect
   the observation and make any permitted queries. Query IDs start at 1 for each
   request, increase strictly by exactly one and are never reused, even after
   error. Replies name their query ID; concurrent replies may arrive out of order.
   A reply must match an outstanding call. The API has no new semantic query-count
   limit; operational traffic/resource bounds still apply.
2. The first submit frame latches the request's submission slot. B receives its
   complete bounded bytes and writes/flushes `submitted` before recording a
   completed receipt. A second submit gets `duplicate_submission` and cannot
   replace or append to the first. A byte-limit refusal may send `too_large`
   before terminating the failed endpoint; B does not drain an unbounded body
   or admit any prefix. Invalid identity/phase/framing is terminal, not a semantic
   proposal correction and not a retry on the same connection.
3. C sends `complete(response)` only after receiving the completed receipt and
   finishing its request-specific activity. B rejects that completion if no
   completed receipt exists, even when bytes or a first-submit latch exist.
   `source_exhausted` and `no_response` explicitly finish without a submission;
   neither may coexist with a latched submission. `failure` can abort either
   state and discards candidate bytes. B resource/cancellation failures dominate
   all outcomes. C stops issuing queries when it completes; outstanding calls
   must have returned before an ordinary successful completion.
4. B revokes the request capability and joins every in-flight semantic query,
   then sends `request_closed`. C must await this before accepting another
   request as continuation. Closure says nothing about semantic acceptance.
   B validates the received proposal independently. A correctable proposal
   produces a new request with a new ID and semantic binding/correction; an
   accepted proposal may advance Houdini and produce the next observation.

Cancellation immediately revokes the request's API authority. After `cancel`,
C stops using that request, abandons outstanding local query waiters and sends
`complete(failure)` after stopping request-owned work. B cancels/joins its API
work; outstanding query replies need not be delivered after cancellation.
Bounded graceful cleanup may be followed by endpoint termination/fallback if C
does not complete. A cancelled or failed request cannot be revived by late
query/submit/complete traffic. Successful request closure leaves the endpoint
and any C-managed idle native processes alive.

After input completion, external cancellation or terminal endpoint failure,
B shuts the endpoint down. It revokes active request work, sends `shutdown`
when the channel remains usable, and C returns `closed` after joining its owned
tree. Only this endpoint-level shutdown implies all C descendants are gone.
B independently completes its generic fallback/join before publication or final
success. EOF before the required receipt/completion is not a response; partial
frames never become a proposal. Reconnecting with an old token is forbidden.

The Rust provider lifecycle contract frozen for the K1a.2 controller migration
retains `api_capabilities`, `resource_failure` and `consult(push, tools, response,
cancellation)`. It removes `begin_consultation`/conversation mode and replaces
the old all-purpose `wait_for_houdini_idle` hook with these required methods:

```rust
fn quiesce_request(&mut self) -> ProposerCleanupFuture<'_>;
fn shutdown(&mut self, reason: ShutdownReason) -> ProposerCleanupFuture<'_>;
```

`ProposerCleanupFuture` resolves to `Result<(), ProposerCleanupError>`; its errors
are the provider-neutral `Failed` and `TimedOut`. Construction, polling and drop
must not panic. A completed response is released only after successful request
quiescence; final search/certification handoff requires successful shutdown.
An error is terminal operational failure, not a successful cleanup or a semantic
proposal correction. K1a.2's lifecycle prerequisite migrates the old unit-output
cleanup alias and all implementations/call sites. Conversation policy and record
migration were completed in K1a.2.

`AgentPush::remaining_request_budget_ns() -> io::Result<Option<u64>>` reads the
same local deadline enforced by B's consultation controller. It returns `None`
when no distinct earlier consultation deadline applies, zero after expiration,
and an error if the exact duration cannot fit in the wire's u64 range. The host
serializes a present value as its canonical decimal string. This metadata does
not alter immutable observation bytes or bindings and never starts another timer.
A started endpoint enters search through `new_with_joined_cleanup`, which joins
it even if search setup fails before a request. Synchronous `new` is reserved for
process-free/stateless sources.

The implementation gates must test these transitions through real processes;
the K1a.1 DTO tests alone do not establish host enforcement or child cleanup.
`fixtures/generic-flow.json` is a portable two-request packet/sequence example.
Its `{}` attachments intentionally exercise only framing, not valid semantic
observations, queries or proposals; real-worker acceptance uses separate fixtures.

### Independent terminal fault and reply limit handling

`AgentProvider::terminal_failure() -> Option<ProposerTerminalFailure>` defaults
to `None`. A generic endpoint latches `ProtocolViolation`, `EndpointExited` or
`EndpointFailure` only when it cannot serve further requests. After joined
request cleanup B checks resource failure and this terminal status before any
proposal admission. Terminal faults become nonretryable run-global operational
failures; ordinary `source_exhausted`/request failure keeps its existing policy.
A fault followed by successful fallback cleanup does not claim cleanup failed.

A legal complete API packet receives `submitted` even when its proposal exceeds
B's separate `reply_bytes` limit. The bounded writer retains its overflow flag,
then `complete`/`request_closed` precede the controller's existing `host_limit`
correction in a fresh request on the same endpoint. `too_large` is reserved for
an illegal transport packet; it does not encode that proposal correction. The
aggregate packet maximum includes the prefix, header and every attachment.

Cancellation reason metadata comes from B's exact owner timestamp and effective
request deadline. An external cancellation strictly before that deadline remains
`cancelled` even when C observes it after the deadline or cleanup is slow. Local
and overall expiry are `deadline`; this metadata does not change B's existing
priority among final run outcomes or add a semantic query.
