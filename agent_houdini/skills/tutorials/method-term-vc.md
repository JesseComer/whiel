---
id: method-term-vc
program_type: general-method
description: Term VC — under the negated guard, I must imply Q. Since Q is typically subset form, a subset-style clause that collapses under ~G is enough.
---

# method-term-vc

**Key insight:** Term fails when I is inductive but too weak to imply Q after the guard fires. Look at Q conjunct-by-conjunct: for each conjunct, identify the clause of I that "collapses" into it under `¬G`.

**Final invariant (template, Term-ready minimal form):**

```
(closure-on-R from P)
& (S = BODY(E, T))        -- collapses to T = BODY(E, T) under S = T; since Q uses ⊆, BODY(E, T) ⊆ S works too
& (S ⊆ R)                -- directly gives T ⊆ R when S = T
```

## Walkthrough

### What Term proves

```
I ∧ ¬G |= Q
```

`¬G` is the guard negation — the post-loop condition.

| Loop style | Guard `G` | Negated guard `¬G` |
|---|---|---|
| Naive 1-IDB | `S ≠ T` | `S = T` |
| Seminaive | `D ≠ ∅` | `D = ∅` |
| Multi-IDB naive | `¬((Sa = Ta) ∧ (Sb = Tb))` | `(Sa = Ta) ∧ (Sb = Tb)` |

### Q is subset form in these benchmarks

For the six source runs, every `Q` has the shape:

```
(BODY_spec(E, T) ⊆ T) ∧ (T ⊆ R)
```

**Not** `T = BODY(E, T)`. So Term only needs:

1. **Part (i):** `BODY_spec(E, T) ⊆ T` — easy, because the invariant has either `S = BODY(E, T)` or `BODY(E, T) ⊆ S`, and under `¬G`, `S = T`, so the clause collapses to `BODY(E, T) ⊆ T`. ✓ (if body = spec)
2. **Part (ii):** `T ⊆ R` — either directly in I, or derived from `S ⊆ R` + `S = T` at Term.

### The guard-collapse habit

For every clause of `I`, write down what it becomes under `¬G`. If no clause "does work" (i.e. collapses into a Q conjunct), Term will fail.

| Clause (naive postfix) | Under `¬G` (`S = T`) |
|---|---|
| `S = BODY(E, T)` | `T = BODY(E, T)` — stronger than Q needs, but implies the subset form. |
| `BODY(E, T) ⊆ S` | `BODY(E, T) ⊆ T` — directly the Q conjunct (i). |
| `T ⊆ R` | unchanged — Q conjunct (ii). |
| `S ⊆ R` | `T ⊆ R` — Q conjunct (ii). |
| `closure on R` | unchanged — spectator at Term. |

Every clause in a successful invariant either (a) collapses into a Q conjunct at Term or (b) is a supporter for Maint. A clause that does neither should be dropped.

### When body != spec: Term is the hard step

If the program's body uses shape `BODY_prog(E, T)` but Q asks for `BODY_spec(E, T) ⊆ T` with `spec ≠ prog`, Term needs a bridge.

The simplest bridge: carry **both** `S = BODY_prog(E, T)` and `S = BODY_spec(E, T)` as invariant clauses. Under `¬G`, both collapse:

- `T = BODY_prog(E, T)` (used to close Maint)
- `T = BODY_spec(E, T)` (used to close Term)

This is exactly what `tc_right__spec_left__naive` did — see `pattern-body-spec-bridge.md`.

The dual def-eq is only inductive when **both** body and spec are linear (operand-order variants of each other). For a nonlinear body against a linear spec, dual def-eq is not inductive — instead, add a *mixed closure* clause like `proj(S × R) ⊆ R`. `tc_nonlin__spec_left__naive` uses exactly this mixed-closure form (see `pattern-body-spec-bridge.md` Technique 2).

### Seminaive Term

Under `¬G`, `D = ∅`, so `T ∪ D = T`. Apply that substitution:

| Clause | Under `D = ∅` |
|---|---|
| `BODY(E, T) ⊆ (T ∪ D)` | `BODY(E, T) ⊆ T` — directly Q conjunct (i). |
| `(T ∪ D) ⊆ R` | `T ⊆ R` — directly Q conjunct (ii). |
| `T ⊆ R` | unchanged. |
| `D ⊆ R` | `∅ ⊆ R` — trivial, useless at Term. |
| `closure on R` | unchanged. |

The three clauses `coupling ∪ combined-bound ∪ closure` are Term-ready on their own. `tc_left__spec_left__seminaive` converged to exactly this 3-clause shape in 4 iterations.

### Init/Maint pass, Term fails — diagnosis

Almost always one of:

1. **Missing collapse clause.** Q needs a fact, and no clause of I becomes that fact under `¬G`. Fix: add a subset-style clause that collapses. E.g. if Q has `rel(T) ⊆ T`, add `rel(T) ⊆ S` (or `=`) to I.
2. **Wrong BODY shape.** The def-eq uses a body shape that doesn't match Q's spec shape. See `pattern-body-spec-bridge.md` for the dual-def-eq remedy; if that doesn't work, Q and body are genuinely incompatible for this proof technique.
3. **Missing `T ⊆ R` or analogue.** Q has `T ⊆ R` but no clause of I implies it at Term. Fix: add `T ⊆ R` or `S ⊆ R` (which collapses to `T ⊆ R`).
