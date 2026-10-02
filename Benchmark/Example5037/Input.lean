-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Go's garbage-collector marking, a frontier traversal with a
  marked-bit check, against the materialised transitive
  closure of the pointer graph joined with the roots.

  Inputs `RootPtr(x)` (unary, the objects referenced from the
  roots) and `HeapPtr(x, y)` (binary, object x holds a pointer
  to object y).  Two Datalog programs: the marking
    `Marked(x) :- RootPtr(x)`
    `Marked(y) :- Marked(x), HeapPtr(x, y)`
  and Soufflé's `tc` benchmark program (the normalised `tc.dl` of
  the Soufflé benchmark suite, read 2026-09-15) with `base =
  HeapPtr`,
    `Tc(x, y) :- HeapPtr(x, y)`
    `Tc(x, z) :- Tc(x, y), Tc(y, z)`

  Side 1, Go (src/runtime/mgcmark.go, `gcDrain` and
  `greyobject`; src/runtime/mgcmark_greenteagc.go and
  mgcmark_nogreenteagc.go, `scanObject`; read 2026-09-15).
  `gcDrain` first runs the root marking jobs (`markroot`), then
  drains the heap marking jobs: it pops an object from the work
  queue and calls `scanObject`, which reads every pointer slot
  of the object and calls `greyobject` on the pointee;
  `greyobject` returns at once "If marked we have nothing to
  do", otherwise sets the mark bit (`mbits.setMarked()`) and
  queues the object (`gcw.putObj`).  The loop ends when no work
  can be obtained.  This is the program of legacy Example2012:
  `Marked` the marked set, `Grey` the queue, `NewG` the pointees
  of the queue not yet marked.  Not modelled: noscan objects
  (marked without being queued, they hold no pointers), oblets,
  the per-P work buffers and work stealing, write barriers and
  the checkmark mode; the queue is served level by level, since
  the order in which objects are popped does not change the
  marked set.

  Side 2, Soufflé's `tc` program compiled by the naive compiler
  (the non-linear closure of `HeapPtr`; `Tc_aux` is its
  snapshot), materialised in full for every source, then joined
  with the roots.

  The schemas differ, unary marks against a binary closure;
  they are linked by the view `Marked = RootPtr ∪ π[2](σ[#0 = #1]
  (RootPtr × Tc))` stated as the postcondition (method 3 of the
  handoff: the linking view is computed inside the claim).
  Independent programs, merged side by side.  Precondition
  `true`.

  Expected verdict: valid.  Both sides give the objects
  reachable from a root by zero or more pointers.

  Expected obstruction: rate mismatch with a dependent join. The
  marking advances one pointer per round for all roots at once,
  the non-linear closure doubles the path length it covers per
  round and holds rows for every source, and the join is applied
  to the finished closure; `Marked ⊆ RootPtr ∪ π(RootPtr ⋈ Tc)`
  holds round by round but the reverse does not, so no
  first-order invariant over the current states gives the
  equality (a leveled-framework target).  With the final values
  as prophecy constants the non-linear fixpoint equation
  `Tc∞ ⊇ Tc∞ ∘ Tc∞` gives transitivity directly, so both
  containments follow from the fixpoint facts without leastness.

  Why a database audience cares: reachability from a root set
  is the canonical demand-restricted query (only the roots'
  rows are wanted), and the choice between a per-root traversal
  and a materialised closure filtered by the roots is the
  demand-driven versus bulk choice that Example5033 makes for
  one bound source; here the roots are a set, the sides have
  different schemas, and the link is a view.

  Sources: golang/go master (commit 8f5d82065574, 2026-09-15):
  src/runtime/mgcmark.go `gcDrain`, `greyobject`;
  src/runtime/mgcmark_greenteagc.go, src/runtime/
  mgcmark_nogreenteagc.go `scanObject`; read 2026-09-15. The
  normalised `tc.dl` of the Soufflé benchmark suite, read
  2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5037

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {RootPtr, Marked, Grey, NewG} (arity: 1),
    {HeapPtr, Tc, Tc_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    true
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Marked := RootPtr;
      Grey := RootPtr;
      WHILE (Grey ≠ ∅) DO
        NewG := ((π[1] (σ[#0 = #2] (HeapPtr × Grey))) ∖ Marked);
        Marked := (Marked ∪ NewG);
        Grey := NewG
      END;
      Tc_aux := ∅[2];
      Tc := (HeapPtr ∪ π[0,3] (σ[#1 = #2] ((Tc_aux × Tc_aux))));
      WHILE (¬((Tc = Tc_aux))) DO
        Tc_aux := Tc;
        Tc := (Tc ∪ (HeapPtr ∪ π[0,3] (σ[#1 = #2] ((Tc_aux × Tc_aux)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (Marked = (RootPtr ∪ (π[2] (σ[#0 = #1] (RootPtr × Tc)))))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5037
end Benchmark
end Whiel
