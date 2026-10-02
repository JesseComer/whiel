---
id: seed-delta-coupling
type: invariant-template
description: accumulator/frontier coupling law for semi-naive (delta) loops
applies_query: any
applies_eval: seminaive
source: seed
---

For delta/frontier loops (guard `Delta ≠ ∅`, body extends an
accumulator by a frontier step), the load-bearing invariant is the COUPLING
LAW: one-step extensions of the accumulator are covered by the accumulator
plus a one-step extension of the frontier, e.g.
`(Acc∘E) ⊆ (Acc ∪ (Delta∘E))`. At exit Delta = ∅ collapses it to the
closure postcondition `(Acc∘E) ⊆ Acc`. Also include the simple containments
`Seed ⊆ Acc` and `Delta ⊆ Acc`, and bound/frame clauses as usual.
