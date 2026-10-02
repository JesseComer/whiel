# API-owned fixtures

`observation.json` and `response-example.json` pin B's complete public observation
and proposal binding for the existing synthetic DefaultPromptCompatibility task.
They contain no C-rendered prompt. The Rust observation test compares all fields,
normalizing only fresh consultation/manifest/request digests, and independently
checks their live binding consistency.

Migration from the historical `proposer_host/fixtures/c1-*` changes only the
operation name, request-policy digest, feedback/presentation versions, API resource
field/name/description, and dependent presentation/consultation/manifest/request
digests. Task, language, prophecy, checks, Core/pending, death rules, proposal and
other semantic content remains exact. Those historical native prompt fixtures
remain temporary legacy data until K3; they do not pin current B presentation.

API 3.1.0 regenerated `observation.json` from the same task: the standing
presentation lost its ten tutorial strings and the feedback/presentation schema
versions moved to 10 and 16. This task carries no committed or pending clause,
so the fixture shows no clause entry and therefore no clause text; the identity
fields `canonical_source` and `display` are pinned by the feedback and replay
tests instead.

`generic-flow.json` covers framing and sequencing only; its empty JSON attachments
are deliberately not a real semantic observation or a certificate acceptance test.
