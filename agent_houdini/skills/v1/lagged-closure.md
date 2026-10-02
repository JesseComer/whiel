# Lagging a closure fact

**When it applies.** A closure fact of the shape `F(X) ⊆ X`, "X is closed under
one step", is required at exit but is false mid-run: the loop is still running
precisely because `X` is not closed yet.

**What to inspect.** Whether the schema carries a snapshot copy `X_aux` (the
previous iterate) or a prophecy copy `X∞` (the exit value) of `X`, and what the
guard compares.

**How to construct.** Two lagged forms are invariants where the plain fact is
not. Over the snapshot: `F(X_aux) ⊆ X`, one step from the previous iterate is
already inside the current one; at exit the guard gives `X = X_aux` and the
clause collapses to the postcondition. Over the prophecy copy: `F(X) ⊆ X∞`, one
step from the current value is inside the final value; it has minimum level 1
and needs the level-0 exit facts, and at exit `X = X∞` collapses it. Propose
the snapshot form when the guard is an equality with the snapshot, the prophecy
form otherwise, and add `X ⊆ X∞` beside the prophecy form.

**Which query tests it.** `validate_clauses`; after a refutation,
`evaluate_clauses` on the countermodel tells which of the two forms holds
there.

**How to read the next failure.** The prophecy form pending at level 1 usually
lacks the level-0 definitional equation of `X` (its exit image is the premise
that makes the step provable). The snapshot form refuted at level 0 means the
body extends `X` by more than one step per iteration; use the prophecy form.
