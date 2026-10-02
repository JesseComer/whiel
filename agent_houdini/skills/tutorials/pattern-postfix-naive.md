---
id: pattern-postfix-naive
program_type: pattern-naive
description: Standard 4-clause post-fixed-point template — closure, def-eq, T-bound, S-bound. Default template for 1-IDB naive loops.
source: postfix_high_20260422_031956/cegis_nomcp/logs/{tc_left,tc_right}__spec_*__naive.log
---

# Pattern: Postfix 4-clause template (naive)

Use this when the program has the standard 1-IDB naive shape:

```
pre:   T := ∅;
       S := BODY(EDB, T)
body:  T := S;
       S := BODY(EDB, T)
guard: S ≠ T
P:     (closure-on-R) ∧ (T = ∅) ∧ (S = ∅)
Q:     (BODY_spec(EDB, T) ⊆ T) ∧ (T ⊆ R)
```

## Template

```
(closure on R, copied from P)
& (S = BODY(EDB, T))
& (T ⊆ R)
& (S ⊆ R)
```

Four clauses. Right-nested for the Lean `#Assert[]` / `qf[]`:

```
(closure) ∧ ((S = BODY(EDB, T)) ∧ ((T ⊆ R) ∧ (S ⊆ R)))
```

## Why each clause

| # | Clause | Role at Init | Role at Maint | Role at Term |
|---|---|---|---|---|
| 1 | closure on R | from P | no body vars — trivially inductive | spectator |
| 2 | `S = BODY(EDB, T)` | `S = BODY(E, ∅)` matches pre's `S := BODY(E, T)` | body re-assigns S | collapses to `T = BODY(E, T)` under `S = T`, which implies Q's subset form |
| 3 | `T ⊆ R` | `∅ ⊆ R` | needs `S ⊆ R` as supporter | directly gives `T ⊆ R` in Q |
| 4 | `S ⊆ R` | requires closure to give `E ⊆ R` in post-pre state | needs closure + `T ⊆ R` + monotonicity of BODY | redundant with (3) at Term, but critical supporter at Maint |

## Variants seen in the 6 logs

### Variant A — 4-clause standard (`tc_right__spec_right__naive`, 2 iter, 117 s)

```
((E ∪ (π[0,3] σ[#1 = #2] (R × E))) ⊆ R)
& (S = (E ∪ (π[0,3] σ[#1 = #2] (T × E))))
& (T ⊆ R)
& (S ⊆ R)
```

The cleanest, fastest convergence in the set. Standard template, body-matches-spec (right-linear body + right-linear Q).

### Variant B — 3-clause without `T ⊆ R` (`tc_left__spec_left__naive`, 3 iter, 126 s)

```
(S = (E ∪ (π[0,3] σ[#1 = #2] (E × T))))
& (((E ∪ (π[0,3] σ[#1 = #2] (E × R))) ⊆ R) ∧ (S ⊆ R))
```

Dropped `T ⊆ R` — Vampire derives it from `S ⊆ R` via the body update `T := S`. Three clauses total. Reached after two dead-ends: iter 1 had no closure, iter 2 had no closure and no `S ⊆ R`.

**Lesson:** the closure clause is load-bearing, and `S ⊆ R` is the primary supporter. `T ⊆ R` can sometimes be omitted, but never the closure.

## Required supporters

For Maint to close on `T ⊆ R` (or `S ⊆ R` when `T ⊆ R` is dropped), the LLM must include **all three** of:

1. The closure on R — copied from P, mentioning every R read by BODY.
2. A def-eq tying S to BODY(E, T).
3. At least one explicit `_ ⊆ R` clause (either `T ⊆ R` or `S ⊆ R`).

Missing any of these three makes Maint unprovable. The CEGIS iteration count in the logs is almost entirely the LLM rediscovering these three facts from CEX feedback.

## When to escalate

If this template fails after 2–3 iterations, consider:

- **Subset def-eq variant** — replace `S = BODY(E, T)` with `BODY(E, T) ⊆ S`. See `pattern-postfix-subset.md`.
- **Dual def-eq bridge** — when body ≠ spec. See `pattern-body-spec-bridge.md`.
- **Seminaive variant** — when the program has a `D` delta. See `pattern-seminaive-coupling.md`.

## Common transcription errors

1. Writing `E` when the program uses `base` (or vice versa). The verifier treats them as distinct symbols.
2. Copying the closure from P with operand order reversed (`(R × E)` instead of `(E × R)` when P specifies the latter). The closure must match P literally.
3. Writing `T ⊆ BODY(E, R)` instead of `T ⊆ R`. The tighter form works for some benchmarks, but it's strictly stronger and harder to prove inductive.
