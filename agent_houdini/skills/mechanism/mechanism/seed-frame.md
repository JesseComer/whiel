---
id: seed-frame
type: invariant-template
description: frame facts over input-only relations; bound clauses cannot survive without them
applies_query: any
applies_eval: any
source: seed
---

Clauses over INPUT-ONLY relations (never assigned by the loop) are
preserved for free — the body cannot change them. The precondition itself is
usually such a clause (e.g. `F(XBound) ⊆ XBound`, "the reference relation is
closed under the operator"): include it verbatim. This FRAME fact is what
makes bound clauses (`X ⊆ XBound`) provable at preservation: from X ⊆ XBound
alone nothing bounds F(X); with the frame, F(X) ⊆ F(XBound) ⊆ XBound.
