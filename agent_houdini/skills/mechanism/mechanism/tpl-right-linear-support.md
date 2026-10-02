---
id: tpl-right-linear-support
type: invariant-template
description: support pack for right-linear closure loops (X := S ∪ S∘X_2): mirror of the left-linear pack
applies_query: any
applies_eval: any
applies_loop: right_linear_closure
source: template-pack
template: {"roles": ["Seed", "Acc", "Acc_2"], "clauses": ["{Seed} ⊆ {Acc}", "{Acc_2} ⊆ {Acc}", "({Seed} ∪ (π[0, 3] (σ[#1 = #2] ({Seed} × {Acc_2})))) = {Acc}", "(π[0, 3] (σ[#1 = #2] ({Acc_2} × {Seed}))) ⊆ {Acc}", "{Acc} ⊆ ({Seed} ∪ (π[0, 3] (σ[#1 = #2] ({Acc_2} × {Seed}))))"]}
---

Mirror of the left-linear pack for RIGHT-LINEAR closure
accumulators (body X := Seed ∪ Seed∘X_2).
