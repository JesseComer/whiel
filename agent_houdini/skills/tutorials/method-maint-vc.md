---
id: method-maint-vc
program_type: general-method
description: Maint VC — every clause must be inductive; failing clauses need *supporters* added, not rewritten.
---

# method-maint-vc

**Key insight:** Every clause of `I` must be inductive: assume `I ∧ G` holds before the body, show each clause holds after the body. A clause that can't justify itself against the body needs a **supporter** — another clause you add to help discharge it. Don't rewrite the failing clause; add the one it needs.

**Final invariant (template, standard postfix form):**

```
(closure-on-R from P)
& (S = BODY(E, T))          -- or  BODY(E, T) ⊆ S  (subset form; see pattern-postfix-subset)
& (T ⊆ R)
& (S ⊆ R)
```

## Walkthrough

### What Maint proves

```
I ∧ G |= wp(body, I)
```

For `I = b_1 ∧ ... ∧ b_k`, the prover splits into per-clause obligations `I ∧ G |= wp(body, b_i)`. Each clause is defended individually but can lean on *every* other clause of I as a hypothesis.

### The four postfix clauses and their roles

#### (1) Closure on `R`: `(closure of BODY over R) ⊆ R`

Inherited from P. Re-exposed inside I so Maint can use it.

- Not an induction target — it has no body-variables on either side.
- **Absolutely required.** Without this clause, *any* Maint obligation about `_ ⊆ R` is unprovable. The CEGIS loop frequently wastes iterations rediscovering this.

#### (2) Definitional equality: `S = BODY(E, T)`

Mirrors the `S := ...` assignment in pre and body.

- Init: discharged by the assignment in pre.
- Maint: trivially inductive because the body re-assigns S.
- Term: when `¬G` gives `S = T`, collapses to `T = BODY(E, T)` — one half of Q.

*If Maint fails on this clause, you transcribed the RHS wrong.* Re-open the program JSON.

*If Maint fails on the clauses that depend on this one*, consider replacing it with a subset form `BODY(E, T) ⊆ S` (see `pattern-postfix-subset.md` for when this is the right move).

#### (3) Accumulator bound: `T ⊆ R`

The real induction target.

- Init: `T = ∅ ⊆ R`. Trivial.
- Maint: after `T := S`, new-T = old-S. Need `S ⊆ R`.
- Term: directly gives `T ⊆ R` in Q.

Maint for this clause is what most candidate invariants get wrong. The supporter chain you need is: `S = BODY(E, T)` (or `BODY(E, T) ⊆ S`) + `T ⊆ R` + `closure on R` → `S ⊆ R` → `new-T ⊆ R`.

#### (4) Aux bound: `S ⊆ R`

The direct supporter for (3). Without this clause in I, Vampire has to chain through `BODY`, which sometimes works and sometimes doesn't within the time budget.

- Init: `S = E ⊆ R`. Requires the closure to imply `E ⊆ R`.
- Maint: after `S := BODY(E, new-T)`, need `BODY(E, new-T) ⊆ R`. Use `new-T ⊆ R` (from clause 3 after update) + `BODY(E, R) ⊆ R` (clause 1) + monotonicity. ✓
- Term: when `¬G` gives `S = T`, this clause and (3) both say `T ⊆ R`. Redundant at Term — useful at Maint.

## Iteration trace: when `S ⊆ R` isn't present

From `tc_left__spec_left__naive.log`:

```
Iter 1: (S = BODY(E, T)) ∧ (T ⊆ R) ∧ (S ⊆ R)                     — no closure → fail
Iter 2: (S = BODY(E, T)) ∧ (T ⊆ R)                                — no closure, no S-bound → fail
Iter 3: (S = BODY(E, T)) ∧ (closure-on-R) ∧ (S ⊆ R)               — success ✓
```

Three iterations to rediscover the pattern **closure + def-eq + aux-bound**. Note iter 3 **drops `T ⊆ R`** — the verifier derives it from `S ⊆ R` + `T ⊆ S` implicitly (from the def-eq giving `S = E ∪ ... ⊇ ∅`, plus the body update `T := S`, plus `new-S ⊆ R`).

## The one rule people break

**Don't rewrite a failing clause — add the clause it needs.**

If `T ⊆ R` fails Maint, the first instinct is to weaken `T ⊆ R` to something weaker, or replace it. Wrong. The right move is to **add `S ⊆ R`** (and/or the closure on R) and keep `T ⊆ R`. The bound clause is the direct Q-relevant fact; its supporter is what you're missing.

### Supporter quick reference

| Failing clause | Usual missing supporter |
|---|---|
| `T ⊆ R` | `S ⊆ R`, or the closure on R, or both |
| `S ⊆ R` | `BODY(E, R) ⊆ R` + `T ⊆ R` |
| `S = BODY(E, T)` | None — transcription error; re-copy RHS |
| `(T ∪ D) ⊆ R` (seminaive) | Closure on R |
| `BODY(E, T) ⊆ (T ∪ D)` (seminaive coupling) | Closure on R + a bound on `T` or `(T+D)` |
| `BODY(E, T) ⊆ S` (subset def-eq) | The next-iteration S update propagates this; no direct supporter needed, but see pattern-postfix-subset |

## Why "3-clause minimal" is sometimes the real answer

For some programs, the verifier only needs closure + def-eq + one bound, because everything else is derivable. `tc_right__spec_right__naive` converged in **2 iterations** with exactly this 4-clause shape (no extras). `tc_nonlin__spec_nonlin__naive` converged in 6 iterations with a **3-clause** invariant using the subset-def-eq form (`BODY(T) ⊆ S`) — even more minimal.

So: start with the minimal template. Add supporters only as Vampire complains.
