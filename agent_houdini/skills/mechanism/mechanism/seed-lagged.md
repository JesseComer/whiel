---
id: seed-lagged
type: invariant-template
description: lag postcondition clauses that only hold at exit via the snapshot relation
applies_query: any
applies_eval: naive
source: seed
---

A postcondition clause of the shape `F(X) ⊆ X` (the output is closed
under the step operator) is typically FALSE mid-run — the loop exists
precisely because X is not closed yet. Its LAGGED variant is the invariant:
replace X by its snapshot X_2 on the LEFT side only, giving `F(X_2) ⊆ X`
("one step from the PREVIOUS iterate is already inside the CURRENT one").
At exit the guard gives X = X_2, which turns the lagged clause back into the
postcondition. Applies only when the schema lists the snapshot relation X_2.
