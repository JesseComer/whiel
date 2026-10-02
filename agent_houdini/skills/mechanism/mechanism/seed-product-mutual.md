---
id: seed-product-mutual
type: invariant-template
description: mutual one-step simulation containments for two synchronized programs
applies_query: equiv_pairs
applies_eval: any
source: seed
---

When two programs run synchronized in one loop and the postcondition
asserts their outputs EQUAL (`X = Y`), the equality alone is rarely
inductive: the two evaluation strategies extend their outputs differently
within an iteration. Add MUTUAL ONE-STEP SIMULATION containments that bridge
the two step shapes, e.g. for left-linear vs right-linear closure:
`(X∘E) ⊆ (E ∪ (E∘Y))` and `(E∘Y) ⊆ (E ∪ (X∘E))` (lagged variants over the
snapshots also work). Keep the equality clause itself as well.
