---
id: auto-left-linear-closure-0001
type: invariant-template
description: auto-abstracted certified core of Example0001 (left_linear_closure)
applies_query: any
applies_eval: any
applies_loop: left_linear_closure
source: Example0001
inst_example: Example0010
template: {"roles": ["Seed", "Acc", "Acc_2"], "clauses": ["({Seed} ∪ (π[0, 3] (σ[#1 = #2] ({Acc_2} × {Seed})))) ⊆ {Acc}", "{Seed} ⊆ {Acc}"]}
---

Machine-abstracted from the certified core of Example0001: role-substituted clauses for a left_linear_closure accumulator. Admitted only after a mechanical instantiation on a held-out task proved all three obligations.
