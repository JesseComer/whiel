---
id: pattern-seminaive-coupling
program_type: pattern-seminaive
description: Semi-naive 3-clause template — subset coupling `BODY(E, T) ⊆ (T ∪ D)`, combined bound `(T ∪ D) ⊆ R`, and closure from P.
source: postfix_high_20260422_031956/cegis_nomcp/logs/tc_left__spec_left__seminaive.log
---

# Pattern: Semi-naive subset coupling

Use this when the program has an accumulator `T` and a delta frontier `D` (sometimes called `DT`, `Delta`, `S`, etc.):

```
pre:   T := ∅;
       D := E                         -- frontier starts with the base case
body:  T := T ∪ D;
       D := (π[..] σ[..] (E × D)) ∖ T    -- or analogous delta recurrence
guard: D ≠ ∅
P:     (closure-on-R) ∧ (T = ∅) ∧ (D = ∅)
Q:     (BODY_spec(EDB, T) ⊆ T) ∧ (T ⊆ R)
```

## Template

```
(BODY(EDB, T) ⊆ (T ∪ D))           -- frontier inclusion (CORE)
& (closure on R from P)
& ((T ∪ D) ⊆ R)
```

**Three clauses.** The coupling is subset, not equality. The bound is on the combined `T ∪ D`, not split into separate `T ⊆ R` and `D ⊆ R`.

## The successful case: `tc_left__spec_left__seminaive` (4 iter, 133 s)

Verified invariant:

```
((E ∪ (π[0,3] σ[#1 = #2] (E × T))) ⊆ (T ∪ D))
& (((E ∪ (π[0,3] σ[#1 = #2] (E × R))) ⊆ R))
& ((T ∪ D) ⊆ R)
```

Body shape: `BODY(E, X) = E ∪ (π[0,3] σ[#1 = #2] (E × X))`.

### Why each clause

**Clause 1 — coupling `BODY(E, T) ⊆ (T ∪ D)`.**

Read: "the accumulator plus its frontier is large enough to cover one naive step from the accumulator."

- Init: `T = ∅`, `D = E`. Coupling becomes `BODY(E, ∅) ⊆ E`, i.e. `E ∪ proj(∅) ⊆ E`, i.e. `E ⊆ E`. ✓
- Maint: after body, new-T = old-T + old-D; new-D = BODY(E, new-T) - new-T. Union: `new-T ∪ new-D = new-T ∪ BODY(E, new-T) ∖ new-T`. This equals `BODY(E, new-T)` because `new-T ⊆ BODY(E, new-T)` (by base-inclusion: BODY includes `E` which covers `new-T`'s base tuples — subject to closure on R bounding `new-T`). So the new coupling becomes `BODY(E, new-T) ⊆ BODY(E, new-T)`. ✓
- Term: under `¬G`, `D = ∅`, so `T ∪ D = T`. Coupling becomes `BODY(E, T) ⊆ T` — **Q conjunct (i) directly**.

**Clause 2 — closure on R.** Copied from P. Required so Maint can bound the new frontier.

**Clause 3 — combined bound `(T ∪ D) ⊆ R`.**

- Init: `T ∪ D = ∅ ∪ E = E ⊆ R`. ✓ (via closure).
- Maint: `new-(T+D) = BODY(E, new-T)`. Need this `⊆ R`. Use new-T `⊆ (T ∪ D) ⊆ R` (from this clause before update) + closure. ✓
- Term: `D = ∅` collapses this to `T ⊆ R` — **Q conjunct (ii) directly**.

## Iteration trace (4 iterations)

```
Iter 1: (coupling) ∧ (T ⊆ R) ∧ (D ⊆ R)              → maint 1/1 fail
Iter 2: (coupling) ∧ (T ⊆ R) ∧ ((T ∪ D) ⊆ R)        → maint 1/1 fail  (no closure)
Iter 3: (coupling) ∧ (T ⊆ R)                         → maint 1/1 fail  (no closure, no D bound)
Iter 4: (coupling) ∧ (closure) ∧ ((T ∪ D) ⊆ R)       → ✓ success
```

The LLM tried three bound-variations before realising the closure was the missing ingredient. Once closure was in, combined `(T ∪ D) ⊆ R` worked — split `T ⊆ R ∪ D ⊆ R` was rejected.

## The three critical choices

1. **Subset, not equality.** `BODY(E, T) ⊆ (T ∪ D)` succeeds where `(T ∪ D) = BODY(E, T)` does not. The old equality form is too strong and causes Maint to fail on the reverse direction `(T ∪ D) ⊆ BODY(E, T)`, which isn't needed for Q anyway.
2. **Combined bound, not split.** `(T ∪ D) ⊆ R` as one clause, not `T ⊆ R ∧ D ⊆ R` as two. Split-bound succeeds for some programs but failed for this one — Vampire apparently prefers the combined form here.
3. **Keep the closure.** Non-negotiable. Without `BODY(E, R) ⊆ R`, Maint cannot bound the new frontier.

## Degenerate case

If the program's pre initialises `D := ∅` rather than `D := E`, the loop never enters. The invariant `(T = ∅) ∧ (D = ∅)` passes all three VCs trivially. Try this first if you suspect the program is degenerate.

## Multi-IDB semi-naive

Apply the same subset-coupling per IDB:

```
BODY_i(EDB, T_1, ..., T_n) ⊆ (T_i ∪ D_i)       -- per-IDB coupling
(T_i ∪ D_i) ⊆ R_i                               -- per-IDB combined bound
BODY_i(EDB, R_1, ..., R_n) ⊆ R_i                -- per-IDB joint closure
```

(Not covered by this rerun's benchmark set — see pattern-postfix-naive.md or write out manually for multi-IDB programs.)

## Common traps

1. Writing `=` instead of `⊆` in the coupling — fails Maint.
2. Splitting the bound into `T ⊆ R ∧ D ⊆ R` when combined works — wastes iterations.
3. Dropping the closure — makes Maint unprovable.
4. Using a body shape that doesn't match the program's delta assignment — transcription error.
