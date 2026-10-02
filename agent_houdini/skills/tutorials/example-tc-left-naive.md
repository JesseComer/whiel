---
id: example-tc-left-naive
program_type: example-naive-linear
description: Left-linear TC with matching spec — 3 iterations, 3-clause success that drops `T ⊆ R`. `tc_left__spec_left__naive`.
source: postfix_high_20260422_031956/cegis_nomcp/logs/tc_left__spec_left__naive.log
---

# Example: `tc_left__spec_left__naive` (3 iter, 126 s)

Structurally symmetric to the right-linear case — same body shape, different operand order — but the synthesiser converged in 3 iterations rather than 2, and the successful invariant has only 3 clauses (dropping `T ⊆ R` explicitly).

## Program

```
namespace: Gen_left_spec_left_naive
edb:   E (arity 2), R (arity 2)
idb:   T (arity 2), S (arity 2)

pre:   T := ∅;
       S := (E ∪ (π[0, 3] σ[#1 = #2] (E × T)))

body:  T := S;
       S := (E ∪ (π[0, 3] σ[#1 = #2] (E × T)))

guard: S ≠ T

P:  (((E ∪ (π[0, 3] σ[#1 = #2] (E × R)))) ⊆ R) ∧ ((T = ∅) ∧ (S = ∅))
Q:  (((E ∪ (π[0, 3] σ[#1 = #2] (E × T)))) ⊆ T) ∧ (T ⊆ R)
```

`BODY(E, X) = E ∪ (π[0, 3] σ[#1 = #2] (E × X))` — left-linear (the `X` is on the right operand of the join).

## Verified invariant

```
(S = (E ∪ (π[0, 3] σ[#1 = #2] (E × T))))
& (((E ∪ (π[0, 3] σ[#1 = #2] (E × R))) ⊆ R) ∧ (S ⊆ R))
```

**Three clauses.** The `T ⊆ R` clause is absent — Vampire derives it on its own from `S ⊆ R` + the body update `T := S`.

## Iteration trace

```
Iter 1: (S = BODY(T)) ∧ (T ⊆ R) ∧ (S ⊆ R)                    → maint 2/1 fail (no closure)
Iter 2: (S = BODY(T)) ∧ (T ⊆ R)                               → maint 1/1 fail (no closure, no S-bound)
Iter 3: (S = BODY(T)) ∧ (closure) ∧ (S ⊆ R)                   → ✓ success
```

### What iter 1 and iter 2 tell us

- **Iter 1** failed because without the closure, Vampire can't show `new-S ⊆ R`. It had `T ⊆ R` and `S ⊆ R` but no link from those facts to the post-body values via BODY.
- **Iter 2** *dropped* `S ⊆ R` from iter 1 — a regression. Also fails, even worse than iter 1 (now no `_ ⊆ R` supporter at all).
- **Iter 3** added the closure and restored `S ⊆ R`. Keeps `S = BODY(T)`. Notably **also dropped `T ⊆ R`** — the LLM discovered that 3 clauses suffice.

**Lesson:** the CEGIS loop is not always monotone. The LLM sometimes weakens before re-strengthening. The trajectory `(T⊆R, S⊆R)` → `(T⊆R)` → `(closure, S⊆R)` is strictly guided by which clauses were rejected by CEX-replay, and the minimal successful form can drop clauses that previous iterations kept.

## Clause roles

### (1) Def-eq `S = E ∪ proj(E × T)`

- Init: `T = ∅`, `S = E ∪ proj(∅)`... `π[0,3] σ[#1 = #2] (E × ∅)`: `E × ∅` is empty (product with empty), so proj/sel of empty is empty. `S = E ∪ ∅ = E`. Clause: `E = E ∪ proj(∅)` = `E = E`. ✓
- Maint: trivially inductive.
- Term: under `S = T`, gives `T = E ∪ proj(E × T)`. Directly satisfies Q conjunct 1 (subset direction trivially from `=`).

### (2) Closure `(E ∪ proj(E × R)) ⊆ R`

From P, copied verbatim. Left-linear shape matches both the body and Q.

### (3) `S ⊆ R`

- Init: `S = E`. Need `E ⊆ R`. Closure gives `E ∪ proj(E × R) ⊆ R`, so `E ⊆ R`. ✓
- Maint: new-S = `E ∪ proj(E × new-T)`. Need `⊆ R`. This needs `new-T ⊆ R` and the closure.
  - Where does `new-T ⊆ R` come from inductively? From `new-T := S`, so `new-T ⊆ R` iff the *previous* `S ⊆ R`. That's exactly clause 3 applied to the pre-body state. Vampire uses it.
  - Then by closure + monotonicity, `E ∪ proj(E × new-T) ⊆ E ∪ proj(E × R) ⊆ R`. ✓
- Term: `S = T` gives `T ⊆ R` — Q conjunct 2. ✓

### Why `T ⊆ R` is omitted

The update `T := S` means at any mid-loop state, `T` equals some *previous* `S`. If `S ⊆ R` held one step back, `T ⊆ R` holds now. Vampire's saturation prover handles this chaining implicitly via the inductive step, so you don't need to spell it out.

This simplification saves one clause but costs one iteration of convergence — the LLM had to discover it through CEX-replay.

## Compare with right-linear

Right-linear converged in 2 iterations with 4 clauses (kept `T ⊆ R`). Left-linear converged in 3 iterations with 3 clauses (dropped `T ⊆ R`). The difference isn't structural — both are correct minimal forms. The LLM's trajectory is what varied.

**Takeaway:** aim for minimal, but don't penalise yourself if you include a redundant `T ⊆ R` clause. Having one extra clause doesn't break anything; missing a necessary clause does.

## When this template transfers

Any 1-IDB naive left-linear TC (body `E ∪ proj(E × idb)`) with P's closure in left-linear shape should use this template. The `right-linear` and `left-linear` choice matters only for operand order inside `proj(_ × _)`; the 4 (or 3) clause roles are identical.
