---
id: tpl-nonlinear-support
type: invariant-template
description: support pack for nonlinear (squaring) closure loops (X := S ∪ X_2∘X_2)
applies_query: any
applies_eval: any
applies_loop: nonlinear_closure
source: template-pack
template: {"roles": ["Seed", "Acc", "Acc_2"], "clauses": ["{Seed} ⊆ {Acc}", "{Acc_2} ⊆ {Acc}", "({Seed} ∪ (π[0, 3] (σ[#1 = #2] ({Acc_2} × {Acc_2})))) = {Acc}"]}
---

Support pack for NONLINEAR (squaring) closure accumulators
(body X := Seed ∪ X_2∘X_2): seed containment, lag containment, and the
definitional equality.
