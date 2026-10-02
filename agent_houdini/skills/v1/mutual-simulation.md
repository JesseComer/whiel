# Mutual simulation for two synchronized programs

**When it applies.** Two evaluation strategies run in one loop and the
postcondition asserts their outputs are equal, `X = Y`, or one contains the
other.

**What to inspect.** The two step shapes in the body: for instance one
extends on the left (`E ∘ X`) and the other on the right (`Y ∘ E`).

**How to construct.** The equality alone is rarely inductive, because within
one iteration the two strategies extend their outputs differently. Add
one-step simulation containments that bridge the two shapes in both
directions, for instance `(X ∘ E) ⊆ (E ∪ (E ∘ Y))` and
`(E ∘ Y) ⊆ (E ∪ (X ∘ E))`, and keep the equality clause as well. Lagged
variants over the snapshot or prophecy copies also work when the plain ones
are only true at exit.

**Which query tests it.** `validate_clauses`; on a refuted step check,
`evaluate_clauses` on the countermodel shows which direction fails.

**How to read the next failure.** Only one direction pending means the other
program's step needs its own definitional equation at level 0 first. Both
pending at level 1 usually means the containments should be over the prophecy
copies (`X∞`, `Y∞`) with `X ⊆ X∞` and `Y ⊆ Y∞` beside them.
