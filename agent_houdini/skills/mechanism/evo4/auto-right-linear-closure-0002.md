---
id: auto-right-linear-closure-0002
type: invariant-template
description: auto-abstracted certified core of Example0002 (right_linear_closure)
applies_query: any
applies_eval: any
applies_loop: right_linear_closure
source: Example0002
inst_example: production_40
template: {"roles": ["Seed", "Acc", "Acc_2"], "clauses": ["({Seed} ∪ (π[0, 3] (σ[#1 = #2] ({Seed} × {Acc_2})))) ⊆ {Acc}"]}
---

Machine-abstracted from the certified core of Example0002: role-substituted clauses for a right_linear_closure accumulator. Admitted only after a mechanical instantiation on a held-out task proved all three obligations.
