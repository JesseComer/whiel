---
id: example-tc-seminaive
program_type: example-seminaive
description: Seminaive left-linear TC — 4 iterations to find the minimal 3-clause coupling template. `tc_left__spec_left__seminaive`.
source: postfix_high_20260422_031956/cegis_nomcp/logs/tc_left__spec_left__seminaive.log
---

# Example: `tc_left__spec_left__seminaive` (4 iter, 133 s)

Semi-naive left-linear TC. The successful invariant is 3 clauses: coupling subset, closure, combined bound. The delta `D` replaces the auxiliary `S` of the naive form.

## Program

```
namespace: Gen_left_spec_left_seminaive
edb:   E (arity 2), R (arity 2)
idb:   T (arity 2), D (arity 2)        -- D is the delta/frontier

pre:   T := ∅;
       D := E                           -- frontier starts as the edge relation

body:  T := (T ∪ D);
       D := (π[0, 3] σ[#1 = #2] (E × D)) ∖ T

guard: D ≠ ∅

P:  (((E ∪ (π[0, 3] σ[#1 = #2] (E × R)))) ⊆ R) ∧ ((T = ∅) ∧ (D = ∅))
Q:  (((E ∪ (π[0, 3] σ[#1 = #2] (E × T)))) ⊆ T) ∧ (T ⊆ R)
```

Note: the delta update `D := (π[0,3] σ[#1 = #2] (E × D)) ∖ T` uses the **prior frontier** `D` (not `E`) on the inside of the join — semi-naive optimisation. But the *effective* body expression that we want to reason about is the full naive body `BODY(E, T) = E ∪ proj(E × T)`.

## Verified invariant

```
((E ∪ (π[0, 3] σ[#1 = #2] (E × T))) ⊆ (T ∪ D))
& (((E ∪ (π[0, 3] σ[#1 = #2] (E × R))) ⊆ R))
& ((T ∪ D) ⊆ R)
```

Three clauses. Subset coupling, closure from P, combined bound `(T ∪ D) ⊆ R`.

## Iteration trace

```
Iter 1: (coupling) ∧ (T ⊆ R) ∧ (D ⊆ R)                   → maint 1/1 fail
Iter 2: (coupling) ∧ (T ⊆ R) ∧ ((T ∪ D) ⊆ R)             → maint 1/1 fail
Iter 3: (coupling) ∧ (T ⊆ R)                              → maint 1/1 fail
Iter 4: (coupling) ∧ (closure) ∧ ((T ∪ D) ⊆ R)            → ✓ success
```

Four iterations to discover the closure was the missing supporter. Split-bound (`T ⊆ R` and `D ⊆ R`) didn't work; the combined bound did. `T ⊆ R` alone without closure didn't work either.

## Clause roles

### (1) Coupling `BODY(E, T) ⊆ (T ∪ D)`

Expanded: `E ∪ proj(E × T) ⊆ T ∪ D`.

- Init: `T = ∅`, `D = E`. Coupling becomes `E ∪ proj(E × ∅) ⊆ ∅ ∪ E`, i.e. `E ∪ ∅ ⊆ E`, i.e. `E ⊆ E`. ✓
- Maint: after body, `new-T = T ∪ D`, `new-D = proj(E × D) ∖ new-T`. New union: `new-T ∪ new-D = (T ∪ D) ∪ (proj(E × D) ∖ (T ∪ D))`. By set algebra, `new-T ∪ new-D = (T ∪ D) ∪ proj(E × D)`.
  
  We need `BODY(E, new-T) ⊆ new-T ∪ new-D`, i.e. `E ∪ proj(E × (T ∪ D)) ⊆ (T ∪ D) ∪ proj(E × D)`. 

  Expand the LHS: `proj(E × (T ∪ D)) = proj(E × T) ∪ proj(E × D)` (distributivity of join over union). So LHS = `E ∪ proj(E × T) ∪ proj(E × D)`.

  Decompose the goal:
  - `E ⊆ (T ∪ D)`: because `D` initially held `E`, and `D ∖ T` tuples get absorbed into T at each step — so the tuples of `E` are always in `T ∪ D` (by monotonicity + Init). Vampire derives this from the coupling at earlier iterations + inductive saturation, but the key fact is that `E ∪ proj(E × T) ⊆ T ∪ D` held before the body, so `E ⊆ T ∪ D`. After the body, `E ⊆ new-T ∪ new-D` follows from monotonic growth of `T ∪ D`.
  - `proj(E × T) ⊆ T ∪ D`: from the pre-body coupling.
  - `proj(E × D) ⊆ new-T ∪ new-D`: trivially, because `new-T ∪ new-D` contains `proj(E × D)` as shown above.
  
  Vampire chains these arguments via the closure on R bounding things tightly.
- Term: under `D = ∅`, `T ∪ D = T`. Coupling becomes `E ∪ proj(E × T) ⊆ T` — **Q conjunct 1 directly**.

### (2) Closure `(E ∪ proj(E × R)) ⊆ R`

From P, verbatim. Left-linear shape.

- Init: from P.
- Maint: spectator (no body vars on either side).
- Term: spectator.

### (3) Combined bound `(T ∪ D) ⊆ R`

- Init: `T ∪ D = ∅ ∪ E = E`. Need `E ⊆ R`. From clause 2, `E ∪ proj(E × R) ⊆ R` implies `E ⊆ R`. ✓
- Maint: new-(T+D) = `(T+D) ∪ proj(E × D)` (from the derivation above). Need `⊆ R`. Use `T ∪ D ⊆ R` (this clause before update) + `D ⊆ R` (implied) + closure to show `proj(E × D) ⊆ proj(E × R) ⊆ R`. Then union is `⊆ R`. ✓
- Term: under `D = ∅`, collapses to `T ⊆ R` — **Q conjunct 2 directly**.

## Why the split bound failed

Iter 1 had `T ⊆ R ∧ D ⊆ R` as two separate clauses. This gives Vampire two separate induction obligations for basically the same fact. The combined `(T ∪ D) ⊆ R` is strictly weaker (in terms of proof complexity) and sufficient — one clause, one obligation.

Also, the combined form collapses cleanly at Term (`D = ∅` gives `T ⊆ R`); the split form collapses too, but with redundancy.

## Why the closure was missed in iter 1–3

The LLM proposed various bound-shape variations without including the closure from P. Without closure, Vampire cannot show the new frontier stays under R after `proj(E × D)` adds new tuples. Iter 4 finally included the closure, and everything worked.

**Takeaway:** for seminaive, the closure-from-P is not optional. Include it in every candidate.

## When this template transfers

Any seminaive program of the form:

```
pre:   T := ∅; D := base-relation
body:  T := T ∪ D; D := (one-step-body over D) ∖ T
guard: D ≠ ∅
```

with P giving a closure on R in some shape and Q asking for a subset-form post-condition, should use this 3-clause template:

```
(full-BODY(EDB, T) ⊆ (T ∪ D))
& (closure on R from P)
& ((T ∪ D) ⊆ R)
```

The `full-BODY` is the effective naive body, not the delta-only recurrence. If the program's pre/body uses a different delta structure (e.g. `D := BODY(E, D)` without `-T`), the coupling still holds but may require a slightly different form.

## Common mistakes

1. Writing `=` instead of `⊆` in the coupling.
2. Splitting the bound into `T ⊆ R ∧ D ⊆ R` when combined form is cleaner.
3. Forgetting the closure from P.
4. Writing the coupling against the delta-recurrence `proj(E × D)` instead of the full body `E ∪ proj(E × T)`. The coupling must be against the full body, not just the delta step.
