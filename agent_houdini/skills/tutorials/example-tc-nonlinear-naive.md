---
id: example-tc-nonlinear-naive
program_type: example-naive-nonlinear
description: Nonlinear TC with matching nonlinear spec — 6 iterations to discover that `BODY(T) ⊆ S` (subset def-eq) works where `S = BODY(T)` (equality) fails. `tc_nonlin__spec_nonlin__naive`.
source: postfix_high_20260422_031956/cegis_nomcp/logs/tc_nonlin__spec_nonlin__naive.log
---

# Example: `tc_nonlin__spec_nonlin__naive` (6 iter, 303 s)

The hardest successful case in the source set. The self-join `T × T` in the body defeats the standard equality-form def-eq, and the LLM needs 6 iterations to discover that replacing equality with a subset works.

## Program

```
namespace: Gen_nonlin_spec_nonlin_naive
edb:   E (arity 2), R (arity 2)
idb:   T (arity 2), S (arity 2)

pre:   T := ∅;
       S := (E ∪ (π[0, 3] σ[#1 = #2] (T × T)))

body:  T := S;
       S := (E ∪ (π[0, 3] σ[#1 = #2] (T × T)))

guard: S ≠ T

P:  (((E ∪ (π[0, 3] σ[#1 = #2] (R × R)))) ⊆ R) ∧ ((T = ∅) ∧ (S = ∅))
Q:  (((E ∪ (π[0, 3] σ[#1 = #2] (T × T)))) ⊆ T) ∧ (T ⊆ R)
```

`BODY(E, X) = E ∪ (π[0, 3] σ[#1 = #2] (X × X))` — nonlinear self-join.

## Verified invariant

```
((E ∪ ((π[0, 3] σ[#1 = #2] (R × R)))) ⊆ R)
& ((E ∪ ((π[0, 3] σ[#1 = #2] (T × T)))) ⊆ S)
& (S ⊆ R)
```

**Three clauses.** Notice: **no `S = BODY(E, T)`** equality. Instead `BODY(E, T) ⊆ S` — the subset direction only.

## Iteration trace

```
Iter 1: (closure) ∧ (T ⊆ R) ∧ (S = BODY(T)) ∧ ...             → maint 0/1 fail
Iter 2: (closure) ∧ (T ⊆ R) ∧ (BODY(T) ⊆ S) ∧ (S ⊆ R)       → maint 0/1 fail
Iter 3: (closure) ∧ (T ⊆ R) ∧ (S ⊆ R) ∧ (BODY(T) ⊆ S)       → maint 0/1 fail
Iter 4: (closure) ∧ (T ⊆ S) ∧ (S = BODY(T)) ∧ ...             → maint 0/1 fail  (regression to equality)
Iter 5: (closure) ∧ (S = BODY(T)) ∧ (S ⊆ R)                   → maint 0/1 fail
Iter 6: (closure) ∧ (BODY(T) ⊆ S) ∧ (S ⊆ R)                  → ✓ success
```

Six iterations. Iter 2 already had the right shape `BODY(T) ⊆ S`, but together with `T ⊆ R` and `S ⊆ R` Vampire still couldn't close Maint — redundant bounds confused the proof search. Iter 6 stripped down to exactly 3 clauses and succeeded.

## Why equality fails and subset succeeds

### Equality `S = BODY(E, T)` in Maint

After body: `T := S; S := BODY(E, new-T)`. The equation `new-S = BODY(E, new-T)` holds by construction. For `new-T ⊆ R` the Maint step needs:

```
new-T = old-S = BODY(E, old-T)
        = E ∪ proj(old-T × old-T)
```

So we need `E ∪ proj(old-T × old-T) ⊆ R`. Use old `T ⊆ R` → `old-T × old-T ⊆ R × R` → `proj(old-T × old-T) ⊆ proj(R × R) ⊆ R` (closure). Add `E ⊆ R` (from closure). ✓

This argument works on paper, but in practice Vampire gets bogged down expanding the self-join and chaining monotonicity. With 4+ clauses and a self-join, the saturation proof search exhausts the time budget.

### Subset `BODY(E, T) ⊆ S` in Maint

The clause says: `E ∪ proj(T × T) ⊆ S`. After body:

- `new-T := S`.
- `new-S := E ∪ proj(new-T × new-T) = E ∪ proj(S × S)`.

Substitute to find the new clause-statement: `E ∪ proj(new-T × new-T) ⊆ new-S`. This is `E ∪ proj(S × S) ⊆ new-S = E ∪ proj(S × S)`. ✓ trivially — both sides of the subset are syntactically the same expression, namely the just-assigned new-S.

Then Maint for `S ⊆ R`:

- `new-S = E ∪ proj(S × S)`. Need `⊆ R`. Use `S ⊆ R` (this clause) → `S × S ⊆ R × R` → `proj(S × S) ⊆ proj(R × R) ⊆ R` (closure) → `E ∪ proj(S × S) ⊆ R` (`E` also `⊆ R`). ✓

The chain is shorter: we work directly with the inclusion `BODY ⊆ S ⊆ R` rather than needing to re-derive new-T <= R and chain through equality.

### Why drop `T ⊆ R`

`T ⊆ R` is derivable from `S ⊆ R` (old-T becomes S which is <= R; new-T = S is <= R). Keeping it explicit **adds a redundant obligation** to Maint; the saturation prover sometimes times out trying to prove a redundant fact. Dropping it sped the search up enough that iter 6 closed within the time budget.

## Term discharge

Under `¬G`, `S = T`.

- Clause 2: `E ∪ proj(T × T) ⊆ S` becomes `E ∪ proj(T × T) ⊆ T` — **Q conjunct 1 directly** (the subset form).
- Clause 3: `S ⊆ R` becomes `T ⊆ R` — **Q conjunct 2 directly**.

Both Q conjuncts match without any bridging or additional reasoning.

## Why this case is instructive

It proves that **the subset-def-eq pattern is not just an optimisation — sometimes it's the only way to close Maint** in the verifier's time budget. Linear programs don't require it (equality works there), but nonlinear self-join programs benefit from the shorter proof chain.

It also demonstrates that **stripping clauses can be necessary**. The iter-6 invariant is strictly weaker than the iter-2 candidate (which had all of closure, `T ⊆ R`, `S ⊆ R`, `BODY(T) ⊆ S`), but the weaker form closes Maint faster in Vampire.

## When to use this template

Decision rule:

1. Default to `pattern-postfix-naive.md` (equality form).
2. If Maint fails after 3 iterations and the program body has a self-join, switch to this template.
3. Keep exactly three clauses: closure + `BODY(T) ⊆ S` + `S ⊆ R`.

## What transfers

Any 1-IDB naive program with body `idb := EDB-base ∪ π[..] σ[..] (idb × idb)` (or deeper self-joins) should try this template when equality-form fails. The structure is the same regardless of what `proj/sel` indices the program uses.
