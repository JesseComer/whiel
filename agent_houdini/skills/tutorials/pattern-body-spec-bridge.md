---
id: pattern-body-spec-bridge
program_type: pattern-bridging
description: Two techniques for bridging a body/spec shape mismatch — dual definitional equality (for linear-vs-linear), and a derived mixed closure (for nonlinear-body-vs-linear-spec).
source: postfix_high_20260422_031956/cegis_nomcp/logs/tc_right__spec_left__naive.log + postfix_high_20260422_031956/cegis_nomcp_retry_high/logs/tc_nonlin__spec_left__naive.log
---

# Pattern: Body/spec bridging

Use this when the input has `_metadata.cross_spec: true` — the program body is in one RA shape and Q asks for a different shape.

Two bridging techniques, each for a different kind of mismatch.

## Technique 1 — Dual definitional equality

Use when **both body and spec are linear**, differing only in operand order (e.g. body `(T × E)`, spec `(E × T)`).

### Template

```
(closure on R, in whichever shape P provides)
& (S = BODY_prog(E, T))              -- def-eq in body shape
& (S = BODY_spec(E, T))              -- def-eq in spec shape (same S)
& (T ⊆ R)
& (S ⊆ R)
```

Five clauses. The trick: **both equalities assert the same `S` equals two different RA expressions**. This is inductive when the two expressions compute the same relation for every intermediate `T` the loop produces.

### Why inductive

For linear bodies, after each iteration `T` is a closure-prefix of `E`. For any closure-prefix `T`:

```
π[..] σ[..] (T × E) = π[..] σ[..] (E × T)
```

because composition of `E` with its own closure-prefix is symmetric in operand order. This symmetry holds **incrementally**, not just at the fixpoint — which is what makes the dual def-eq a valid invariant.

### When the program and spec are both right-linear, or both left-linear, skip this pattern

No bridge is needed — see `pattern-postfix-naive.md`. Bridging is only for *different* linear shapes.

### Confirmed case

`tc_right__spec_left__naive` — 4 iterations, 392 s. See `example-tc-cross-spec.md` Case A.

## Technique 2 — Mixed closure `proj(S × R) ⊆ R`

Use when the **program body is nonlinear** (self-join like `T × T`) but **the closure from P is linear** (`proj(E × R) ⊆ R`). Dual def-eq does **not** work here — `proj(T × T)` and `proj(E × T)` are genuinely different relations at every intermediate iteration.

### Template

```
(closure on R, linear shape from P)
& (S = BODY_prog(E, T))              -- def-eq in the (nonlinear) body shape
& (T ⊆ S)                           -- growth ordering
& (S ⊆ R)
& (π[..] σ[..] (S × R)) ⊆ R    -- MIXED closure (S with R)
```

Five clauses. The last is the bridging clause: *composing `S` once with `R` stays under `R`*.

### Why the mixed closure is inductive

Maint for clause 5 after body (`new-S = E ∪ proj(S × S)`):

```
proj(new-S × R) = proj((E ∪ proj(S × S)) × R)
                = proj(E × R) ∪ proj(proj(S × S) × R)    — distributivity over union
                = proj(E × R) ∪ proj(S × proj(S × R))     — associativity of composition
                ⊆ R ∪ proj(S × R)                         — linear closure on left
                ⊆ R ∪ R                                    — mixed closure applied ONCE more
                = R
```

The clause supports its own inductive step: applying it once inside the derivation of itself after the body. This is why it's a single clause rather than needing `proj(R × R) ⊆ R` (which P doesn't provide).

### Why the mixed closure replaces `R × R` closure

A nonlinear body `proj(T × T)` after `T := S` becomes `proj(S × S)`. To bound `proj(S × S) ⊆ R`:

```
proj(S × S) ⊆ proj(S × R)     — monotonicity using S ⊆ R
            ⊆ R                — clause 5
```

Without clause 5, Vampire would need `proj(R × R) ⊆ R` — which isn't in P (P only gives linear `proj(E × R) ⊆ R`). Clause 5 is the derived version that's actually provable inductively, and it's strong enough to discharge the nonlinear Maint obligation.

### Why Term closes

Under `¬G`, `S = T`. The nonlinear def-eq becomes `T = E ∪ proj(T × T)` — the nonlinear fixpoint. Then Q's first conjunct `E ∪ proj(E × T) ⊆ T` follows by monotonicity:

```
E ⊆ T                   — from T = E ∪ (something)
proj(E × T) ⊆ proj(T × T) — E ⊆ T monotonicity
            ⊆ T           — proj(T × T) is a summand of T via the fixpoint eq
```

The linear spec is a **consequence** of the nonlinear fixpoint, provable at Term without needing a dual def-eq during the loop.

### Confirmed case

`tc_nonlin__spec_left__naive` in `cegis_nomcp_retry_high` — **1 iteration**, 53 s. See `example-tc-cross-spec.md` Case B.

Note: in the standard `cegis_nomcp` run this benchmark took 10 iterations and *still* failed, because the LLM kept cycling through dual-def-eq attempts. The retry run with higher reasoning budget landed directly on the mixed-closure form in iter 1. The invariant always existed; the search budget mattered.

## Decision table

| Body shape | Spec shape | Technique |
|---|---|---|
| Left-linear | Left-linear | No bridge (`pattern-postfix-naive.md`). |
| Right-linear | Right-linear | No bridge (`pattern-postfix-naive.md`). |
| Right-linear | Left-linear | **Technique 1** — dual def-eq. ✓ |
| Left-linear | Right-linear | **Technique 1** — dual def-eq (symmetric). Not in source set. |
| Nonlinear | Nonlinear | No bridge (`pattern-postfix-subset.md` — subset def-eq). |
| Nonlinear | Left-linear | **Technique 2** — mixed closure. ✓ |
| Nonlinear | Right-linear | **Technique 2** — mixed closure (symmetric). Not in source set. |
| Linear | Nonlinear | No bridge — spec is weaker; direct `BODY_spec(T) ⊆ S` should work. Not in source set. |

## Which RA shape for the closure and spec def-eq?

Whatever **P** gives you, copy verbatim. Q's spec shape tells you what Term needs to conclude, but the closure clause in I is the one from P — not from Q. Sometimes these coincide (linear body + linear P + linear Q); sometimes they diverge.

Transcription rule: literally copy the closure in P into I's clause 1. Don't "simplify" or re-express.

## Common traps

1. **Attempting Technique 1 when the body is nonlinear.** Dual def-eq is not inductive for nonlinear-vs-linear shape mismatches — see `example-tc-cross-spec.md` for why. Switch to Technique 2.
2. **Writing `proj(R × R) ⊆ R` as an additional clause hoping it'll bridge.** P doesn't give you this, so it's not derivable at Init — the clause will fail Init VC.
3. **Forgetting the `T ⊆ S` ordering clause in Technique 2.** Without it, the Maint chain `new-T = S, proj(S × R) ⊆ R → new-T ⊆ R → new-T ⊆ S_next` may fail.
