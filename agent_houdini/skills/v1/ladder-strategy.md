# Building a Core in layers

**When it applies.** Every task. Read it once before the first proposal.

**What to inspect.** The preprocessed loop: which relations the body assigns
(they have prophecy copies), which it only reads, the guard, and how the
postcondition mentions each relation.

**How to construct, in this order, in small batches.**

1. Level 0: facts true at every iteration. The definitional equation of each
   relation the body assigns, transcribed literally from the body's right-hand
   side (`S = <body's expression for S>`), and any containment that only grows
   toward its limit. They are cheap, they almost always commit, and each one
   becomes a premise for everything above it. Do not propose a top-level
   conjunct of the precondition over relations the body never assigns: the
   verifier installs those itself as protected rows.
2. Clauses whose step check needs exit facts. If a clause is true at every
   iteration but cannot be proved inductive from the running state alone, ask
   what it needs from the exit state: usually that the guard is false there, or
   that a level-0 equation holds there. Those are exactly the premises level 1
   supplies, so get the supporting level-0 fact committed first.
3. The clause that carries the postcondition. Take the postcondition and
   replace the occurrences that are not yet true mid-run by their prophecy
   copies. The result is often true from the first iteration and collapses
   back to the postcondition at exit. Where a relation occurs several times,
   which occurrence to lift is not obvious: put one clause per choice in the
   same batch, with the companion `R ⊆ R∞` that lets a running row be read as
   a final one, and let the checks decide.

A batch should be self-supporting: a bound without its frame fact, or a subset
clause without the companion that covers the freshly assigned relation, fails
the step fixed point together with nothing to show for it. Three to six
clauses per round is the usual size.

**Which query tests it.** `validate_clauses` for syntax before submitting.
After a `refuted` Term check, `countermodel` and `evaluate_clauses` show which
draft excludes the countermodel.

**How to read the next failure.** A level-0 clause that comes back pending was
not provable from the running state: either it needs a companion or it is only
true at exit and belongs lifted at level 1. A lifted clause that stays pending
usually lacks the level-0 fact whose exit image it needs.
