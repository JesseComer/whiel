# Coupling the accumulator to the frontier

**When it applies.** Semi-naive evaluation: a guard of the shape
`Delta ≠ ∅`, a body that extends an accumulator `Acc` by a step taken from the
frontier `Delta` and recomputes the frontier as the new rows.

**What to inspect.** The exact step expression in the body (`Delta ∘ E`,
`E ∘ Delta`, or both), and the postcondition's closure fact on `Acc`.

**How to construct.** The load-bearing clause is the coupling law: one step of
the accumulator is covered by the accumulator plus one step of the frontier,
`(Acc ∘ E) ⊆ (Acc ∪ (Delta ∘ E))` for a right-extending step. At exit
`Delta = ∅` and it collapses to the closure fact `(Acc ∘ E) ⊆ Acc`. Add the
simple containments `Seed ⊆ Acc` and `Delta ⊆ Acc`, and the bound and frame
clauses the postcondition needs.

**Which query tests it.** `validate_clauses` for the composition syntax
(`π[0,3] (σ[#1 = #2] ((X × Y)))`); `evaluate_clauses` on a countermodel to see
whether the coupling or a containment is what fails there.

**How to read the next failure.** The coupling law pending means the step's
new rows are not covered: either `Delta ⊆ Acc` is missing or the step in the
clause is on the wrong side of the composition. Equality where a containment
was meant fails the step check; write `⊆`.
