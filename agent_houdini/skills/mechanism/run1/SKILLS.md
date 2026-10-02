# Skill Library Index

| id | type | applies | description |
|---|---|---|---|
| evo-bound-closure-support | repair-rule | query=prefix_equivalence,eval=naive | Repair non-inductive bound clauses for naive fixpoint loops by adding the bound-carrier closure fact that mirrors the loop step. |
| seed-bound | invariant-template | any | postcondition bound clauses hold at every loop head |
| seed-delta-coupling | invariant-template | eval=seminaive | accumulator/frontier coupling law for semi-naive (delta) loops |
| seed-frame | invariant-template | any | frame facts over input-only relations; bound clauses cannot survive without them |
| seed-lagged | invariant-template | eval=naive | lag postcondition clauses that only hold at exit via the snapshot relation |
| seed-product-mutual | invariant-template | query=equiv_pairs | mutual one-step simulation containments for two synchronized programs |
