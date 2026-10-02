# Example5040 — invalid

certificate: `../../verifier/Example5040/Certificate/Invalid.lean`
counterexample: `../../verifier/Example5040/Counterexample.json`

the checked counterexample instance:

    a::View: ∅
    a::ViewC: ∅
    p::Banned: {(str:u, str:c)}
    p::Filtered: ∅
    p::ParentRel: {(str:p, str:c)}
    p::Reader: {(str:u, str:c)}
    p::View: ∅
    p::ViewC: {(str:u, str:c)}

verifier consultations: 1
timing: first prompt 2026-09-17 19:00:13, result 2026-09-17 19:01:01, 48 s

## Consultations

### Request 1 — consultation 1

outcome: response; started 2026-09-17 19:00:13, took 32 s; prompt 28018 bytes; files in `../../agent/Example5040/request-1`
push: Core 0, pending 0, last round 0, latest: initial — no round has run yet

the agent said:

> I’m checking the semantic shape before spending a verifier round. This one has a suspicious “filter during closure” versus “closure then filter” pattern, so I’m testing whether the triple itself may be false rather than merely missing an invariant.
>
> I found a small concrete run that looks like a real counterexample: a banned reader row can still seed an unfiltered ancestor in `ViewC`, while `View` filters it out before propagation. I’m going to submit that as a candidate instance rather than propose invariants for a false triple.

tool calls: `submit`

submission 1: `candidate_counterexample`, verifier reply: receipt

    o:p::Banned: {(str:u, str:c)}
    o:p::Filtered: ∅
    o:p::ParentRel: {(str:p, str:c)}
    o:p::Reader: {(str:u, str:c)}
    o:p::View: ∅
    o:p::ViewC: {(str:u, str:c)}
    o:a::View: ∅
    o:a::ViewC: ∅

## Clauses, as the verifier recorded them

The ledger is empty: no clause check ran.

## Countermodels

No check was refuted by the prover in this run, so no countermodel exists; failed checks, if any, were inconclusive (see the ledger column).

## Files

- verifier output: `../../verifier/Example5040` (result.json, Certificate/, artifacts/run-*/manifest.json)
- agent logs: `../../agent/Example5040` (events.jsonl, request-N/prompt.txt, native-stdout.jsonl, submissions.jsonl, mcp.jsonl)
