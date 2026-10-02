---
id: seed-bound
type: invariant-template
description: postcondition bound clauses hold at every loop head
applies_query: any
applies_eval: any
source: seed
---

A postcondition clause of the shape `X ⊆ XBound` (the output is
contained in a reference relation) usually holds at EVERY loop head, not just
at exit — the output only grows toward the bound. Include it verbatim as an
invariant clause. It almost always needs a FRAME supporter (see seed-frame)
to survive preservation.
