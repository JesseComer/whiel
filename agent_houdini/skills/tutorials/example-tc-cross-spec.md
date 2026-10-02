---
id: example-tc-cross-spec
program_type: example-cross-spec
description: Two body/spec-mismatch cases. Both succeed, via two *different* bridging techniques — dual def-eq for linear-vs-linear, and a mixed closure `proj(S × R) ⊆ R` for nonlinear-body-vs-linear-spec.
source: postfix_high_20260422_031956/cegis_nomcp/logs/tc_right__spec_left__naive.log + postfix_high_20260422_031956/cegis_nomcp_retry_high/logs/tc_nonlin__spec_left__naive.log
---

# Example: Cross-spec bridging — two techniques

Two benchmarks where the program body uses one RA shape and Q asks for a different shape (`_metadata.cross_spec: true`). Both succeed — but via *different* bridging techniques. Contrast teaches which technique fits which body/spec combination.

## Case A — `tc_right__spec_left__naive` (4 iter, 392 s)

### Program

```
body uses:      S := E ∪ (π[0, 3] σ[#1 = #2] (T × E))         -- right-linear body
P's closure:    (E ∪ (π[0, 3] σ[#1 = #2] (E × R))) ⊆ R       -- left-linear closure
Q asks for:     (E ∪ (π[0, 3] σ[#1 = #2] (E × T))) ⊆ T       -- left-linear spec
```

### Verified invariant — *dual def-eq bridge*

```
((E ∪ (π[0, 3] σ[#1 = #2] (E × R))) ⊆ R)
& (S = (E ∪ (π[0, 3] σ[#1 = #2] (T × E))))         -- def-eq in BODY shape
& (S = (E ∪ (π[0, 3] σ[#1 = #2] (E × T))))         -- def-eq in SPEC shape
& ((T ⊆ R) ∧ (S ⊆ R))
```

Five clauses. **Two def-eqs on the same S** — one per shape.

### Why it works

The clauses together say: `S = E ∪ proj(T × E) = E ∪ proj(E × T)`, which reduces to `proj(T × E) = proj(E × T)`. This equality **does not hold for arbitrary relations T**, but it **does hold incrementally** for the specific sequence of T values this loop produces — because at each iteration T is the k-step closure-prefix of E, and right-step and left-step composition of E with its own closure-prefix produce the same relation.

Vampire proves this by induction through the body: if the equality holds for old-T, the body makes it hold for new-T (because new-T = old-S = E + proj(old-T * E), and similar reasoning on the spec side).

### Iteration trace

```
Iter 1: direct equality proj(T*E) = proj(E*T)                         → maint 1/1 fail
Iter 2: direct equality with closure                                   → maint 0/1 fail
Iter 3: direct equality stripped down                                  → maint 0/1 fail
Iter 4: dual def-eq (S = body-shape AND S = spec-shape) ∪ bounds       → ✓ success
```

The direct equality `proj(T*E) = proj(E*T)` as a standalone clause is not inductive — Vampire can't prove it without the intermediate step of equating both sides to the aux `S`. Making `S` the "witness" of the equivalence is what unlocks the inductive argument.

### Term discharge

Under `¬G`, `S = T`. The spec-shape def-eq collapses to `T = E ∪ proj(E × T)`, which directly gives Q's first conjunct (`E ∪ proj(E × T) ⊆ T` is immediate from `=`). The `T ⊆ R` clause gives Q's second conjunct.

## Case B — `tc_nonlin__spec_left__naive` (1 iter, 53 s, retry-high mode)

### Program

```
body uses:      S := E ∪ (π[0, 3] σ[#1 = #2] (T × T))     -- NONLINEAR body
P's closure:    (E ∪ (π[0, 3] σ[#1 = #2] (E × R))) ⊆ R   -- LINEAR closure
Q asks for:     (E ∪ (π[0, 3] σ[#1 = #2] (E × T))) ⊆ T   -- LINEAR spec
```

Nonlinear body, linear closure, linear spec.

### Verified invariant — *mixed-closure bridge*

```
((E ∪ (π[0, 3] σ[#1 = #2] (E × R))) ⊆ R)
& (S = (E ∪ (π[0, 3] σ[#1 = #2] (T × T))))
& (T ⊆ S)
& (S ⊆ R)
& ((π[0, 3] σ[#1 = #2] (S × R)) ⊆ R)                      -- mixed closure
```

Five clauses. **Crucially, no dual def-eq** — the def-eq is in the program's nonlinear shape only. The bridge is instead a fifth clause `proj(S × R) ⊆ R` — a derived "mixed" closure that combines `S` (with its self-join content) and `R` in one composition step.

### Why it works

The mixed-closure clause `proj(S × R) ⊆ R` says: *any single composition of S with R lands inside R.*

Why is this stable under the body? `new-S = E ∪ proj(S × S)`. Evaluate `proj(new-S × R)`:

```
proj(new-S × R) = proj((E ∪ proj(S × S)) × R)
                = proj(E × R) ∪ proj(proj(S × S) × R)           — distributivity
                = proj(E × R) ∪ proj(S × proj(S × R))           — associativity of composition
                ⊆ R ∪ proj(S × R)                               — E-closure ∪ monotonicity
                ⊆ R ∪ R = R                                     — mixed closure applied once
```

So the mixed closure is self-supporting via composition associativity — you apply clause 5 once inside the derivation of clause 5 after the body, and it closes.

### Why clause 5 is needed for Maint on clause 4 (`S ⊆ R`)

After body, `new-S = E ∪ proj(new-T × new-T) = E ∪ proj(S_old × S_old)`. Need `⊆ R`. Chain:

```
proj(S_old × S_old) ⊆ proj(S_old × R)      — monotonicity with S_old ⊆ R
                     ⊆ R                     — clause 5 at old state
E ⊆ R                                        — from linear closure (clause 1)
so E ∪ proj(S_old × S_old) ⊆ R               — union bound
```

Without clause 5, Vampire would need `proj(R × R) ⊆ R` (a closure P doesn't provide) to bound `proj(S_old × S_old)`. Clause 5 stands in for the missing `R*R` closure, derivable from the linear closure + self-supporting through the body.

### Term discharge

Under `¬G`, `S = T`. From clause 2 + `S = T`: `T = E ∪ proj(T × T)` — the nonlinear fixpoint. Need to derive Q's conjunct 1: `E ∪ proj(E × T) ⊆ T`.

```
E ⊆ T                    — directly from T = E ∪ (something)
proj(E × T) ⊆ proj(T × T) — monotonicity with E ⊆ T
              ⊆ T          — from T = E ∪ proj(T × T), proj(T × T) is a summand of T
E ∪ proj(E × T) ⊆ T       — union
```

Q's conjunct 2 `T ⊆ R` follows from clause 4 + `S = T`. ✓

Clause 5 is not used at Term — its job was Maint. Clause 3 (`T ⊆ S`) is redundant at Term (collapses to `T ⊆ T`) but its job was maintaining `T ⊆ S` inductively across the body.

## Side-by-side contrast

| | Case A — dual def-eq | Case B — mixed closure |
|---|---|---|
| Body shape | right-linear `T × E` | nonlinear `T × T` |
| Spec shape | left-linear `E × T` | left-linear `E × T` |
| Bridging clause | `S = BODY_spec(T)` alongside `S = BODY_prog(T)` | `proj(S × R) ⊆ R` |
| Why inductive | Both body and spec are linear; the operand-order symmetry holds incrementally. | Composition associativity: `proj((X ∪ Y) × R) = proj(X × R) ∪ proj(Y × proj(...))` lets the clause self-support. |
| Why Term succeeds | Spec-shape def-eq collapses to Q directly. | Nonlinear fixpoint implies linear subset via monotonicity. |
| Iterations | 4 | 1 |

## When to pick which technique

**Both body and spec are linear (possibly different operand orders):** dual def-eq.

**Body is nonlinear (self-join), spec is linear:** mixed closure. The dual def-eq technique **does not work** here — `proj(T × T)` and `proj(E × T)` produce different relations at every intermediate iteration, not just a reversed composition.

**Body is linear, spec is nonlinear:** the spec is weaker than the program guarantees, so a direct `BODY_spec(T) ⊆ S` subset clause (no dual, no mixed closure) should suffice. Not tested in this source set.

## Historical note on this benchmark

The `tc_nonlin__spec_left__naive` benchmark was previously reported as **infeasible** under the standard CEGIS setup (10 iterations exhausted, no invariant found). The successful 1-iteration result here comes from the `cegis_nomcp_retry_high` variant — presumably with a different temperature / higher reasoning budget for the LLM, which let it land directly on the mixed-closure invariant instead of cycling through dual-def-eq attempts.

Takeaway: the invariant *exists*; finding it is a search-budget issue, not a fundamental expressibility issue. The mixed-closure technique generalises to any nonlinear-body + linear-closure situation and is worth trying first when the cross-spec flag is set and the body is nonlinear.
