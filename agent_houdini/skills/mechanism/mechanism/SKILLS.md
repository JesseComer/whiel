# Skill Library Index

| id | type | applies | description |
|---|---|---|---|
| seed-bound | invariant-template | any | postcondition bound clauses hold at every loop head |
| seed-delta-coupling | invariant-template | eval=seminaive | accumulator/frontier coupling law for semi-naive (delta) loops |
| seed-frame | invariant-template | any | frame facts over input-only relations; bound clauses cannot survive without them |
| seed-lagged | invariant-template | eval=naive | lag postcondition clauses that only hold at exit via the snapshot relation |
| seed-product-mutual | invariant-template | query=equiv_pairs | mutual one-step simulation containments for two synchronized programs |
| tpl-left-linear-support | invariant-template | any | support pack for left-linear closure loops (X := S ∪ X_2∘S): seed/lag/def-eq/right-lag/right-dec |
| tpl-nonlinear-support | invariant-template | any | support pack for nonlinear (squaring) closure loops (X := S ∪ X_2∘X_2) |
| tpl-right-linear-support | invariant-template | any | support pack for right-linear closure loops (X := S ∪ S∘X_2): mirror of the left-linear pack |
