---
id: auto-nonlinear-closure-0003
type: invariant-template
description: auto-abstracted certified core of Example0003 (nonlinear_closure)
applies_query: any
applies_eval: any
applies_loop: nonlinear_closure
source: Example0003
inst_example: production_40
template: {"roles": ["Seed", "Acc", "Acc_2"], "clauses": ["({Seed} ∪ (π[0, 3] (σ[#1 = #2] ({Acc_2} × {Acc_2})))) = {Acc}", "({Seed} ∪ (π[0, 3] (σ[#1 = #2] ({Acc_2} × {Acc_2})))) ⊆ {Acc}", "{Acc_2} ⊆ {Acc}", "{Seed} ⊆ {Acc}"]}
---

Machine-abstracted from the certified core of Example0003: role-substituted clauses for a nonlinear_closure accumulator. Admitted only after a mechanical instantiation on a held-out task proved all three obligations.
