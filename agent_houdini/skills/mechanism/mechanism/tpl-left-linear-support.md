---
id: tpl-left-linear-support
type: invariant-template
description: support pack for left-linear closure loops (X := S ∪ X_2∘S): seed/lag/def-eq/right-lag/right-dec
applies_query: any
applies_eval: any
applies_loop: left_linear_closure
source: template-pack
template: {"roles": ["Seed", "Acc", "Acc_2"], "clauses": ["{Seed} ⊆ {Acc}", "{Acc_2} ⊆ {Acc}", "({Seed} ∪ (π[0, 3] (σ[#1 = #2] ({Acc_2} × {Seed})))) = {Acc}", "(π[0, 3] (σ[#1 = #2] ({Seed} × {Acc_2}))) ⊆ {Acc}", "{Acc} ⊆ ({Seed} ∪ (π[0, 3] (σ[#1 = #2] ({Seed} × {Acc_2}))))"]}
---

Machine-instantiable support pack for a LEFT-LINEAR closure
accumulator (body X := Seed ∪ X_2∘Seed): seed containment, lag containment,
the definitional equality, the opposite-side lag (Seed∘X_2 ⊆ X), and the
opposite-side decomposition (X ⊆ Seed ∪ Seed∘X_2). These are the per-loop
correctness facts an equivalence or containment task needs for EACH of its
accumulators; bridge clauses between accumulators must be added separately.
