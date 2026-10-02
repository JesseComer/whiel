---
id: pattern-postfix-subset
program_type: pattern-naive
description: When the definitional equality `S = BODY(E, T)` resists Maint, replace it with the subset `BODY(E, T) ⊆ S`. Tighter bound on S, Q still proved.
source: postfix_high_20260422_031956/cegis_nomcp/logs/tc_nonlin__spec_nonlin__naive.log
---

# Pattern: Subset def-equality (postfix-subset)

Use this when:

- The standard postfix template (see `pattern-postfix-naive.md`) fails Maint repeatedly.
- The body has a non-trivial self-join (`T × T`, nested compositions).
- Q is subset form — `BODY_spec(E, T) ⊆ T`, **not** equality.

Replace `S = BODY(E, T)` with `BODY(E, T) ⊆ S` and drop clauses that are no longer needed.

## Template

```
(closure on R from P)
& (BODY(E, T) ⊆ S)
& (S ⊆ R)
```

Three clauses. No `T ⊆ R`, no `S = BODY(E, T)` — the subset form does both jobs.

## The one successful case: `tc_nonlin__spec_nonlin__naive` (6 iter, 303 s)

Body and spec both use nonlinear TC: `BODY(E, T) = E ∪ π[0,3] σ[#1 = #2] (T × T)`.

Verified invariant:

```
((E ∪ ((π[0,3] σ[#1 = #2] (R × R)))) ⊆ R)
& ((E ∪ ((π[0,3] σ[#1 = #2] (T × T)))) ⊆ S)
& (S ⊆ R)
```

### Why each clause

**Clause 1 — closure on R.** Standard, copied from P.

**Clause 2 — `BODY(E, T) ⊆ S`.**

- Init: `T = ∅`, `S = E`. Clause becomes `E ∪ proj(∅*∅) ⊆ E`, i.e. `E ⊆ E`. ✓
- Maint: after body, `new-S := E ∪ proj(new-T × new-T)`, so the clause becomes `E ∪ proj(new-T × new-T) ⊆ E ∪ proj(new-T × new-T)`. ✓ trivially, because the body assigns S to exactly this expression.
- Term: under `¬G`, `S = T`. Clause becomes `E ∪ proj(T × T) ⊆ T` — **this is Q conjunct (i) directly**.

**Clause 3 — `S ⊆ R`.** Standard bound.

- Init: `S = E ⊆ R` via closure.
- Maint: new-S = E + proj(new-T * new-T). Need this `⊆ R`. Use new-T <= R (derived from clause 3 before update: `S ⊆ R`, then `new-T := S`) + closure `(E ∪ proj(R*R)) ⊆ R` + monotonicity. ✓
- Term: `S = T` gives `T ⊆ R` — **Q conjunct (ii) directly**.

### Why no `S = BODY(E, T)` equality

The standard equality form would fail Maint on this nonlinear body. Tracing iter 1 of the log:

```
Iter 1: (closure) ∧ (T ⊆ R) ∧ (S = BODY(E, T)) ∧ ... → maint 0/1 fail
```

The reason: with `S = BODY(E, T)` and `T × T` self-join, Vampire struggles to close Maint for the `T ⊆ R` clause through the chain `new-T = S = BODY(E, T)`, `T ⊆ R`, `R × R ⊆ R`. It needs `new-T × new-T ⊆ R × R`, which requires both `new-T ⊆ R` *and* monotonicity of `*` — and the verifier times out or can't find the argument.

Replacing `=` with `⊆` and moving `T ⊆ R` away lets Vampire work directly with the inclusions `BODY(T) ⊆ S ⊆ R`, which chains through without self-join expansion.

### Why no `T ⊆ R`

Once clauses 2 and 3 hold, `T ⊆ R` is derivable: after the body, `new-T := S`, and clause 3 gives `S ⊆ R`, so `new-T ⊆ R`. Vampire figures this out without needing it spelled out. Before the body, old-T is either empty (Init) or bounded via the previous iteration's update.

Apparently the verifier wants `T ⊆ R` removed so it doesn't spend time proving a redundant obligation. The successful iter-6 invariant has exactly three clauses.

## Iteration trace of the 6 iterations

```
Iter 1: (closure) ∧ (T ⊆ R) ∧ (S = BODY(E, T)) ∧ ...                → maint 0/1 fail
Iter 2: (closure) ∧ (T ⊆ R) ∧ (BODY(E, T) ⊆ S) ∧ ...                 → maint 0/1 fail  (has the right coupling but wrong extras)
Iter 3: (closure) ∧ (T ⊆ R) ∧ (S ⊆ R) ∧ (BODY(E, T) ⊆ S)            → maint 0/1 fail
Iter 4: (closure) ∧ (T ⊆ S) ∧ (S = BODY(E, T)) ∧ ...                  → maint 0/1 fail  (went back to equality)
Iter 5: (closure) ∧ (S = BODY(E, T)) ∧ (S ⊆ R)                        → maint 0/1 fail
Iter 6: (closure) ∧ (BODY(E, T) ⊆ S) ∧ (S ⊆ R)                       → ✓ success
```

Six iterations because the LLM rediscovered the subset form twice (iters 2, 3) but kept adding wrong supporters. The minimal successful form is three clauses: closure + subset-coupling + aux-bound.

## When to use

Decision procedure:

1. Start with `pattern-postfix-naive.md` (4-clause, equality).
2. If Maint fails after 3 iterations and the body has a self-join (`T × T`, `proj(T × T)`, etc.), switch to this pattern.
3. If the program's body is linear (`T × E` or `E × T`), the equality form usually works — don't switch prematurely.

## Applies to

- Nonlinear TC (self-join bodies).
- Potentially: mutually recursive programs where per-IDB Maint is tight.
- Not usually needed for linear TC — the equality form works.

## Term-side guarantee

Because Q is subset-form (`BODY_spec(T) ⊆ T`), the invariant clause `BODY(T) ⊆ S` + guard `S = T` immediately gives Q's first conjunct. If Q were equality `T = BODY(T)` you'd need *both* `BODY(T) ⊆ S` and `T ⊆ S` (or `S = BODY(T)`). The subset Q is what makes this minimal 3-clause form work.
