---
id: method-init-vc
program_type: general-method
description: Init VC — trace the pre-block concretely, check each clause against the post-pre state. P may already specify empty IDBs.
---

# method-init-vc

**Key insight:** Init = *concrete tracing* of the pre-block, then check each clause against the post-pre state. Read `P` carefully — it often pre-declares the IDBs to be empty.

**Final invariant (template):** `(clause_1) ∧ (clause_2) ∧ ...`

## Walkthrough

### What Init actually proves

```
{ P } pre-block { I }
```

i.e. `sp(pre, P) |= I`. Starting from any state satisfying `P` and executing the pre-block, `I` must hold.

### Read P first

In practice, `P` for these benchmarks doesn't just bound `R` — it often pins the IDBs:

```
P = (closure-on-R) ∧ (T = ∅) ∧ (S = ∅)
```

So *before* the pre-block runs, `T = ∅` and `S = ∅` are already given. The pre-block then either keeps them empty (`T := ∅`) or initialises them (`D := E` in seminaive).

### Concrete tracing procedure

1. Read the pre-block top to bottom.
2. Substitute each assignment into what follows.
3. Record the final value of every variable.

#### Naive pre (1-IDB)

```
pre: T := ∅;
     S := (E ∪ (π[0, 3] σ[#1 = #2] (E × T)))
```

With `T = ∅` (from P and `T := ∅`):
- `π[0, 3] σ[#1 = #2] (E × ∅)` = `∅` (product with empty is empty).
- `S = E ∪ ∅ = E`.

Post-pre state: `T = ∅`, `S = E`.

#### Seminaive pre (tc_left__spec_left__seminaive)

```
pre: T := ∅;
     D := E
```

Post-pre state: `T = ∅`, `D = E`.

### Init-check each clause

Use the post-pre state to literally evaluate each candidate clause.

| Candidate clause | Init check (naive post-pre `T=∅, S=E`) |
|---|---|
| `S = (E ∪ π[..] (E × T))` | `E = E ∪ ∅` = `E = E`. ✓ |
| `T ⊆ R` | `∅ ⊆ R`. ✓ |
| `S ⊆ R` | `E ⊆ R`. Requires the closure from P to include `E ⊆ R`, which `(E ∪ proj(E*R)) ⊆ R` does imply (`E ⊆ E ∪ proj(E*R) ⊆ R`). ✓ |
| `(E ∪ π[..] (E × R)) ⊆ R` | Spectator — comes from P. ✓ |
| `T = BODY(E, T)` | `∅ = E ∪ ...` — **false at Init**, too strong. ✗ |
| `(T ∪ D) = BODY(E, T)` (seminaive) | `(∅ ∪ E) = (E ∪ ∅)` — actually true at Init, but fails Maint. Use `⊆` not `=`. |

### Common Init failures

**Failure 1 — asserting the fixpoint too early.** `T = BODY(E, T)` is Q, not I. Use `S = BODY(E, T)` instead — it's true at Init and collapses to the fixpoint only at Term.

**Failure 2 — forgetting that `P` is a *precondition*.** If you want a P-fact (like the closure on R) to survive into the loop, **copy it into I**. P is assumed at Init, not at Maint.

**Failure 3 — over-tight seminaive coupling.** Writing `(T ∪ D) = BODY(E, T ∪ D)` instead of `BODY(E, T) ⊆ (T ∪ D)`. At Init, `T = ∅, D = E`, so `T ∪ D = E` and `BODY(E, T ∪ D) = BODY(E, E) = E ∪ proj(E*E)`. Unless `proj(E*E) ⊆ E`, this equality is false at Init.

### Reading an Init counterexample

Vampire's model shows a finite database satisfying P where, after pre, some clause of I is false. Procedure:

1. Identify which clause failed.
2. Substitute post-pre values (use the concrete-tracing procedure).
3. Evaluate the clause in the model. Where is it false?
4. Weaken the clause or add a supporter.

Common repair: convert an overtight `=` to `⊆`, or replace a fixpoint-style clause with a subset-form one that holds at `∅`.
