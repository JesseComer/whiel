# Reading a countermodel

**When it applies.** The latest result is `postcondition_open` with
`refuted` and an attempt number, or `history` shows a check row that was
`refuted`. Nothing here applies to an `inconclusive` check: that one has no
countermodel.

**What to inspect.** `countermodel({attempt})`: one table per relation of
the prophecy schema. For a Term check it satisfies every Core clause and the
negated guard and violates the postcondition; for a maintenance check of
clause `c` it satisfies the premises and violates `c` after one execution of
the body; for an initialization check it satisfies the precondition and the
exit facts and violates `c`.

**How to construct.** Find the violating tuple: the row the postcondition (or
the clause) demands and the table lacks, or the row the table holds that the
clause forbids. Ask which relation and which assignment could have produced
it in a real run, and whether any clause in the Core says anything about that
relation. The countermodel is a database no run may reach that the Core
nevertheless allows; the clause to add is the one that rules it out, usually
a containment between the relation that holds the offending row and the one
that should bound it, or a lifted fact about the final value. Test the
candidates with `evaluate_clauses` on the same attempt before submitting: the
right one is false on the countermodel.

**Which query tests it.** `countermodel`, then `evaluate_clauses` with
`{"kind": "retained", "attempt": N}`.

**How to read the next failure.** If the new clause commits and the next
Term check is refuted again, the new countermodel differs; repeat. If the new
clause is itself refuted at level 0, it is false mid-run and belongs lifted to
a prophecy copy at level 1.
