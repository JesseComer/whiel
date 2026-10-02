---
id: example-tc-right-naive
program_type: example-naive-linear
description: Easiest case in the source set — standard 4-clause postfix template succeeded in 2 iterations. `tc_right__spec_right__naive`.
source: postfix_high_20260422_031956/cegis_nomcp/logs/tc_right__spec_right__naive.log
---

# Example: `tc_right__spec_right__naive` (2 iter, 117 s)

The **fastest converging** benchmark in the source set. Body and spec match (both right-linear TC), and the standard 4-clause postfix template works immediately once the closure clause is copied in.

## Program

```
namespace: Gen_right_spec_right_naive
edb:   E (arity 2), R (arity 2)
idb:   T (arity 2), S (arity 2)

pre:   T := ∅;
       S := (E ∪ (π[0, 3] σ[#1 = #2] (T × E)))

body:  T := S;
       S := (E ∪ (π[0, 3] σ[#1 = #2] (T × E)))

guard: S ≠ T

P:  (((E ∪ (π[0, 3] σ[#1 = #2] (R × E)))) ⊆ R) ∧ ((T = ∅) ∧ (S = ∅))
Q:  (((E ∪ (π[0, 3] σ[#1 = #2] (T × E)))) ⊆ T) ∧ (T ⊆ R)
```

`BODY(E, X) = E ∪ (π[0, 3] σ[#1 = #2] (X × E))` — right-linear (the `X` is on the left operand of the join, but the join *result* feeds a right-recursive TC when `X = E^{⊆k}`).

## Verified invariant

```
((E ∪ (π[0, 3] σ[#1 = #2] (R × E))) ⊆ R)
& (S = (E ∪ (π[0, 3] σ[#1 = #2] (T × E))))
& (T ⊆ R)
& (S ⊆ R)
```

Four clauses. Standard postfix template.

## Iteration trace

```
Iter 1: (closure) ∧ (S = BODY(T)) ∧ (T ⊆ R) ∧ (... — attempt without S ⊆ R)    → maint 0/1 fail
Iter 2: (closure) ∧ (S = BODY(T)) ∧ (T ⊆ R) ∧ (S ⊆ R)                          → ✓ success
```

Only one CEX-feedback cycle needed. The iter-1 failure was the bound `T ⊆ R` lacking its supporter `S ⊆ R`.

## Clause roles

### (1) Closure on R — `(E ∪ proj(R × E)) ⊆ R`

Copied from P. Mentions `R × E` (body-shape operand order) because P's closure is in the body-shape here.

- Init: from P.
- Maint: spectator.
- Term: spectator.

### (2) Def-eq — `S = (E ∪ proj(T × E))`

Mirrors the pre and body assignment.

- Init: `T = ∅`, `S = E`. Clause becomes `E = E ∪ proj(∅ × E) = E ∪ ∅ = E`. ✓
- Maint: new-S is literally re-assigned to this expression. ✓
- Term: under `S = T`, clause becomes `T = E ∪ proj(T × E)`. Together with Q's subset direction (`E ∪ proj(T × E) ⊆ T`), gives the fixpoint equality; Q only needs the `⊆` direction, which follows from the reverse `T ⊆ E ∪ proj(T × E)` (via the base `E` plus trivial `T = T` — actually no: Q's first conjunct is `E ∪ proj(T*E) ⊆ T`, which comes from the other direction, see below). Let me recheck:

Actually Q is `(E ∪ proj(T*E)) ⊆ T`. From our def-eq and `S = T`:
`T = S = E ∪ proj(T × E)` — so `E ∪ proj(T × E) = T ⊆ T`. ✓

### (3) `T ⊆ R`

- Init: `∅ ⊆ R`. ✓
- Maint: after `T := S`, need new-T = old-S <= R. Covered by clause 4. ✓
- Term: directly Q conjunct 2.

### (4) `S ⊆ R`

- Init: `S = E`. Need `E ⊆ R`. From clause 1, `E ∪ proj(R × E) ⊆ R` implies `E ⊆ R`. ✓
- Maint: new-S = E + proj(new-T * E). Need `⊆ R`. Use new-T `⊆ R` (from clause 3) + closure `E ∪ proj(R × E) ⊆ R` + monotonicity of `proj`. ✓
- Term: `S = T` gives `T ⊆ R` — same as clause 3.

## Why this benchmark is easy

Three reasons:

1. **Body matches spec.** No bridging needed.
2. **Linear body.** No self-joins — the `R × E` closure is tight enough.
3. **Clean pre-state.** `T = ∅` makes every Init check trivial.

Result: a 4-clause invariant that the LLM produces almost immediately, and Vampire closes in under 10 seconds per verify-call.

## What transfers to similar programs

Any 1-IDB naive program with body `idb := base ∪ π[..] σ[..] (idb op EDB_relation)` (or `(EDB_relation op idb)`) should try this 4-clause template **first**. If P gives a closure on R in the body shape and Q uses the same shape, you're likely 1–2 iterations from success.

## When this template doesn't work

- Body shape ≠ Q shape → see `pattern-body-spec-bridge.md`.
- Body has a self-join `(idb × idb)` → see `pattern-postfix-subset.md`.
- Program is seminaive (has delta `D`) → see `pattern-seminaive-coupling.md`.
