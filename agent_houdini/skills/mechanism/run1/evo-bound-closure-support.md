---
id: evo-bound-closure-support
type: repair-rule
description: Repair non-inductive bound clauses for naive fixpoint loops by adding the bound-carrier closure fact that mirrors the loop step.
applies_query: prefix_equivalence
applies_eval: naive
source: Example0008
---

Use this when a naive loop maintains an output `X` from a snapshot `X_2`, and direct bound goals like `X ⊆ XBound` or `X_2 ⊆ XBound` fail at `maint` from junk states even though the run suggests the bound should hold.

Pattern:
- You already have the loop-update shape `X = F(X_2)`.
- You also have a bridge such as `X_2 ⊆ X` or a one-step support clause relating `F(X_2)` back to `X`.
- The missing ingredient is that `XBound` is not yet known to be closed under the same one-step constructor `F`.

TRIGGER:
- A dropped clause of the form `X ⊆ XBound` or `X_2 ⊆ XBound`.
- The failure is a `maint` counterexample from an unreachable junk state, typically marked as lacking support.
- The trajectory later certifies the bound clause after adding a support fact.

FIX:
- Add the closure clause saying that applying the loop step to tuples already in `XBound` stays inside `XBound`.
- Keep or derive the base seed into `XBound`.
- Then re-propose `X ⊆ XBound` and `X_2 ⊆ XBound`.

Why it works:
- Closure of `XBound` turns the update formula `X = F(X_2)` into an induction step for `X ⊆ XBound`.
- The snapshot bound then follows via the usual monotonic relation between snapshot and current state, such as `X_2 ⊆ X`.
- This repairs exactly the failed→proved pattern seen here: unsupported bound clauses were not wrong, just under-explained.
