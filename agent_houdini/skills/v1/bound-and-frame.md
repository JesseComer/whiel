# Bounds and their frame facts

**When it applies.** The postcondition, or a conjunct of it, bounds an
accumulator by a reference relation: `X ⊆ Bound`, where the loop grows `X` and
never assigns `Bound`.

**What to inspect.** Whether the precondition states a closure fact about
`Bound` (for instance that `Bound` is closed under the body's step), and which
relations the body assigns.

**How to construct.** Propose the bound `X ⊆ Bound` itself as a clause: the
output only grows toward the bound, so it usually holds at every loop head, not
just at exit. Its step check cannot pass alone, because nothing bounds the
step's contribution: it needs the frame fact that `Bound` is closed under the
step, and that fact is over relations the loop never touches, so it is
preserved for free. If the frame fact is a top-level conjunct of the
precondition the verifier already holds it as a protected row and you must not
resubmit it; if it is only a consequence of the precondition, propose it. From
`X ⊆ Bound` and the closure of `Bound`, the step's new rows land inside
`Bound`.

**Which query tests it.** `validate_clauses` for the syntax. If the bound is
refuted at level 0, `countermodel` shows a row of `X` outside `Bound`; ask
which assignment put it there.

**How to read the next failure.** The bound pending with the frame fact
committed means the step needs one more containment, typically that the
freshly assigned relation is inside `Bound` too (`S ⊆ Bound` beside
`T ⊆ Bound`).
