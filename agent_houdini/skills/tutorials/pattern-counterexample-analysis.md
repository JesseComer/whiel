---
id: pattern-counterexample-analysis
program_type: pattern-debugging
description: Reading Vampire counterexamples and choosing the minimal repair. Specialised to the postfix 1-IDB TC setting.
source: postfix_high_20260422_031956/cegis_nomcp/logs/*.log (iteration traces)
---

# Pattern: Counterexample analysis

Use when Vampire reports `CounterSatisfiable` on Init, Maint, or Term. The counterexample is a finite database where the VC is violated. Read it, localise the failing clause, pick the smallest repair.

## The per-iteration feedback loop

Every failed iteration in the logs shows:

```
Agent proposed: <candidate>
Verify failed: init=pass, maint=Xpass/Yfail, term=<status>
```

The counterexample model is fed back into the next LLM call (CEX-replay). The synthesiser's job is to read this feedback and pick a new candidate that *doesn't* fail on the same model.

The CEX-filter rejection seen in some logs (`Candidate is falsified by a prior maint counterexample`) means the LLM kept proposing semantically-equivalent candidates without addressing the root cause.

## Maint failures

### `T ⊆ R` fails

**Model shape:** T has some tuple `t` that isn't in R.

**How did `t` get into T?** Via `T := S`. So the previous iteration had `t ∈ S`.

**Why isn't `S ⊆ R` derivable?** Usually one of:

1. No explicit `S ⊆ R` clause. **Repair:** add `S ⊆ R`.
2. No closure on R. Even with `S ⊆ R`, the Maint step needs closure to reason about `new-S = BODY(E, new-T)`. **Repair:** add the closure from P.

### `S ⊆ R` fails

**Model:** new-S contains a tuple beyond R.

**Why?** new-S = BODY(E, new-T). One of:

1. `new-T` has tuples beyond R (so `T ⊆ R` is not yet strong enough). **Repair:** strengthen `T ⊆ R` to `T ⊆ BODY(R)` or add a tighter bound.
2. Closure on R is missing. **Repair:** add it.
3. Closure is in the wrong shape (operand order). E.g. P has `proj(E*R) ⊆ R` but I has `proj(R*E) ⊆ R`. **Repair:** copy literally from P.

### `S = BODY(E, T)` fails

This clause is *trivially* inductive because the body re-assigns S. If it fails, you transcribed the RHS wrong. Open the program, copy the RHS of the `S := ...` assignment verbatim.

### Seminaive coupling `BODY(E, T) ⊆ (T ∪ D)` fails

Model: the accumulator-plus-frontier doesn't cover one BODY step.

**Usually:** missing closure. **Repair:** add closure on R. Combined with the bound `(T ∪ D) ⊆ R`, Vampire can show the new frontier stays under R and the coupling is maintained.

Secondary cause: you wrote equality instead of subset.

## Init failures

### Clause involves `T` or `S` directly

Trace the pre-block:

```
pre: T := ∅; S := BODY(E, T)
```

Post-pre state: `T = ∅`, `S = BODY(E, ∅)` = base-part of BODY.

Check the failing clause against this concrete state.

- If the clause has `T = BODY(E, T)` — false at Init (empty ≠ base).
- If the clause has `S = BODY(E, T)` — **evaluate carefully**: after pre, `S = BODY(E, ∅) = base`, and `BODY(E, ∅) = base` (by the body definition), so the clause holds.

### Clause involves `R`

Usually a copy from P. Confirm it matches P syntactically.

## Term failures

### Init/Maint pass, Term fails

Under `¬G`, `I` must imply Q. Diagnosis procedure:

1. Write down `¬G`. For naive: `S = T`. For seminaive: `D = ∅`.
2. Apply the substitution to every clause of I.
3. List the resulting facts — this is what Term has to work with.
4. List Q's conjuncts.
5. For each Q conjunct, is it among the facts from step 3? If not, **add the clause** whose post-substitution form is the missing Q conjunct.

**Example: Q needs `BODY_spec(E, T) ⊆ T` but I doesn't have a clause that collapses to this.** Add `BODY_spec(E, T) ⊆ S`. Under `S = T`, it becomes `BODY_spec(E, T) ⊆ T`. ✓

**Example: Q needs `T ⊆ R` but I has no `_ ⊆ R` clause.** Add `T ⊆ R` (or `S ⊆ R`, which collapses to `T ⊆ R` under `S = T`).

## Repair selection heuristic

Faced with a failing candidate, the minimal repair is usually **add one clause**, not rewrite an existing one. The CEGIS iteration traces show that the LLM often wastes iterations by rewriting; the successful iteration is almost always the one that adds the *missing* supporter.

### Supporter quick reference

| Failing VC | Failing clause | Minimal supporter to add |
|---|---|---|
| Init | `T = BODY(E, T)` | Replace with `S = BODY(E, T)`. |
| Init | `(T ∪ D) = BODY(E, T)` | Replace `=` with `⊆`. |
| Maint | `T ⊆ R` | Add `S ⊆ R` or closure on R. |
| Maint | `S ⊆ R` | Add closure on R or strengthen T-bound. |
| Maint | `S = BODY(E, T)` | Re-transcribe RHS; don't "fix" the clause. |
| Maint | seminaive coupling | Add closure on R; switch `=` to `⊆`. |
| Term | Q conjunct not implied | Add a clause whose post-`¬G` form is that conjunct. |

## Case study: `tc_nonlin__spec_nonlin__naive` (6 iterations)

Why 6 iterations to find a 3-clause invariant?

- Iter 1–3: LLM tries various 4-clause postfix shapes with `S = BODY(E, T)`. All fail Maint because nonlinear self-join resists the equality form.
- Iter 4: LLM tries ordering `T ⊆ S`. Fails.
- Iter 5: LLM drops `T ⊆ R`, keeps `S = BODY(E, T)`. Fails.
- Iter 6: LLM replaces equality with subset `BODY(E, T) ⊆ S`. ✓

**Lesson:** when a clause-level change (adding/removing clauses) doesn't work, try a *shape* change (equality → subset). This is a last resort, not a first move.

## Case study: `tc_nonlin__spec_left__naive` — apparent failure, then 1-iter success

Standard `cegis_nomcp` run: the LLM went through the full search space and **exhausted 10 iterations without success**. Trajectory:

- Iter 1–3: dual def-eq variants (borrowed from `tc_right__spec_left` — wrong technique for nonlinear body).
- Iter 4–6: tighter `T`-bounds, subset def-eq variants — all failed or got CEX-filter-rejected for semantically-equivalent candidates.
- Iter 7, 9: LLM produced no parseable output (timed out).
- Iter 8, 10: more dual-def-eq / subset-def-eq cycles — all failed.

At this point, a reasonable conclusion would be "the benchmark is infeasible." **That conclusion would be wrong.**

The `cegis_nomcp_retry_high` variant — same problem, higher reasoning budget for the LLM — closed the same benchmark in **1 iteration, 53 seconds**. The invariant it landed on uses a **mixed closure** `proj(S × R) ⊆ R` that neither of the standard bridging techniques the iter-1–10 trajectory explored could discover. See `example-tc-cross-spec.md` Case B for the full invariant and analysis.

**Lesson:** CEGIS iteration cycling (many iterations, CEX-filter rejections, LLM timeouts) is a signal the *current search trajectory* isn't working — not that no invariant exists. Before giving up on a benchmark:

1. Try a different technique class (dual def-eq → mixed closure → subset def-eq → ...).
2. Raise the agent's reasoning budget / temperature if the framework supports it.
3. Check whether the benchmark has a published "high-budget" success that uses a structurally different invariant form.

A failure trace still carries information — read *which* candidates got rejected to narrow the search. But don't promote a failure trace to an existence claim.
