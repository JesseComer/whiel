-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Chase order-independence on a full-TGD scenario of
  ChaseBench: the parallel chase (every dependency applied
  to every active trigger in each round) against the
  dependency-at-a-time chase (one dependency chased to its
  own fixpoint, then the next, the sweep repeated until no
  dependency has an active trigger).

  Scenario: the full-TGD subset of the correctness scenario
  `tgds` of ChaseBench (github.com/dbunibas/chasebench,
  master at commit 7427e1c1e3196769ee4ea04557465965ec26d02b,
  read 2026-09-15), files
  `scenarios/correctness/tgds/dependencies/tgds.st-tgds.txt`
    s(?a,?b,?c) -> t1(?a,?b,?c)
    s(?a,?b,?c) -> w1(?a,?b)
  and `tgds.t-tgds.txt`
    t1(?a,?b,?c) -> t2(?a,?b)
    t2(?a,?b) -> t3(?a,?b,?C)        (existential, dropped)
    t3(?a,?b,?c) -> t2(?b,?b)
    w1(?a,?b) -> w2(?a,?b)
    w2(?a,?b) -> w1(?b,?b)
  (schemas in `tgds.s-schema.txt`, `tgds.t-schema.txt`; the
  shipped `data/s.csv` holds only the header line).  The
  one dependency with an existential variable is dropped,
  which leaves `t3` with no producer, so `t3` is an input
  relation here.  Relation names may not contain digits:
  `S` = s, `TA` = t1, `TB` = t2, `TC` = t3, `WA` = w1,
  `WB` = w2.  The dependencies then read as the Datalog
  program
    `TA(x, y, z) :- S(x, y, z)`
    `WA(x, y)    :- S(x, y, z)`
    `TB(x, y)    :- TA(x, y, z)`
    `TB(y, y)    :- TC(x, y, z)`
    `WB(x, y)    :- WA(x, y)`
    `WA(y, y)    :- WB(x, y)`
  With full TGDs there are no labelled nulls, so a trigger
  is active exactly when its head fact is missing, and the
  restricted, oblivious, parallel and 1-parallel variants of
  Benedikt et al. (PODS 2017, section 3, "Chase variants")
  all produce the same instance; the universal solution is
  the least fixpoint of this program.

  Side 1, dependency-at-a-time chase, hand-written.  The
  s-t dependencies have source-only bodies, so one
  application saturates them and the target starts as
  `TAQ = S`, `WAQ = π[0,1] S` with `TBQ`, `WBQ` empty (the
  target instance is initially empty in data exchange).  The
  outer loop runs while some target dependency has an active
  trigger; its body chases the four target dependencies in
  file order, each by an inner loop to its own fixpoint.
  This is a fair chase sequence in the sense of the paper's
  Section 2 ("no chase step should be postponed
  indefinitely") that applies chase steps one dependency at
  a time, the order the paper mentions when it replaces the
  semi-naive round of its Algorithm 1 by "a loop that selects
  just one active trigger for one dependency and applies the
  chase step immediately".

  Side 2, parallel chase: each round applies every
  dependency to the current instance (Algorithm 1 of the
  paper accumulates the facts of a round in N and adds them
  at the end of the round), which is naive evaluation of the
  program above; compiled by the repository's naive
  compiler, snapshots `TA_aux`, `TB_aux`, `WA_aux`, `WB_aux`.

  Precondition `true`; postcondition
  `(TAQ = TA) ∧ (TBQ = TB) ∧ (WAQ = WA) ∧ (WBQ = WB)`.

  Expected verdict: valid, since both sides compute the
  least fixpoint (every fair chase sequence of full TGDs
  does).  Expected obstruction: rate mismatch.  The parallel
  side advances every relation by one rule application per
  round; the flattened nested loops of the sequential side
  advance one dependency per iteration and cycle through
  four inner phases under flags, so no round-by-round
  equality holds, and the invariant has to relate the
  sequential instance to the parallel one by inclusions
  (each `…Q` relation stays between the s-t seed and the
  fixpoint, and the parallel side's relations are the
  fixpoint's under-approximations).

  Why it matters (data exchange): the chase result for full
  dependencies is unique, and this is what allows an engine
  to pick its evaluation order freely; Benedikt et al.
  report that RDBMS-based engines such as Llunatic run the
  1-parallel or unrestricted chase orders of magnitude
  faster than the restricted chase, and conclude that "the
  choice of the chase variant can be mainly driven by the
  ease of implementation".  Example5019, which applies the
  dependencies in file order once and does not repeat the
  sweep, is invalid.

  Sources: ChaseBench, https://github.com/dbunibas/chasebench
  (README: 23 scenarios in 5 families, 6 correctness
  scenarios), scenario `scenarios/correctness/tgds`, files
  named above, master commit 7427e1c1e3196769ee4ea04557465965ec26d02b
  (2017-09-13), read 2026-09-15.  M. Benedikt, G.
  Konstantinidis, G. Mecca, B. Motik, P. Papotti, D.
  Santoro, E. Tsamoura, "Benchmarking the Chase", PODS 2017,
  https://doi.org/10.1145/3034786.3034796, read 2026-09-15
  from https://www.cs.ox.ac.uk/boris.motik/pubs/bkmmpst17becnhmarking-chase.pdf
  (Section 2, chase sequences and fairness; Section 3,
  Algorithm 1 and "Chase variants"; Section 8, "Restricted
  vs. unrestricted vs. parallel chase").
-/

namespace Whiel
namespace Benchmark
namespace Example5018

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {S, TA, TC, TA_aux, TAQ} (arity: 3),
    {TB, WA, WB, TB_aux, WA_aux, WB_aux, TBQ, WAQ, WBQ} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TAQ := S;
      WAQ := π[0, 1] S;
      TBQ := ∅[2];
      WBQ := ∅[2];
      WHILE (¬((((π[0, 1] TAQ) ⊆ TBQ) ∧ ((π[1, 1] TC) ⊆ TBQ)) ∧ ((WAQ ⊆ WBQ) ∧ ((π[1, 1] WBQ) ⊆ WAQ)))) DO
        WHILE (¬((π[0, 1] TAQ) ⊆ TBQ)) DO
          TBQ := (TBQ ∪ π[0, 1] TAQ)
        END;
        WHILE (¬((π[1, 1] TC) ⊆ TBQ)) DO
          TBQ := (TBQ ∪ π[1, 1] TC)
        END;
        WHILE (¬(WAQ ⊆ WBQ)) DO
          WBQ := (WBQ ∪ WAQ)
        END;
        WHILE (¬((π[1, 1] WBQ) ⊆ WAQ)) DO
          WAQ := (WAQ ∪ π[1, 1] WBQ)
        END
      END;
      TA_aux := ∅[3];
      WA_aux := ∅[2];
      TB_aux := ∅[2];
      WB_aux := ∅[2];
      TA := S;
      WA := (π[0,1] (S) ∪ π[1,1] (WB_aux));
      TB := (π[0,1] (TA_aux) ∪ π[1,1] (TC));
      WB := WA_aux;
      WHILE (¬(((TA = TA_aux) ∧ ((WA = WA_aux) ∧ ((TB = TB_aux) ∧ (WB = WB_aux)))))) DO
      TA_aux := TA;
      WA_aux := WA;
      TB_aux := TB;
      WB_aux := WB;
      TA := (TA ∪ S);
      WA := (WA ∪ (π[0,1] (S) ∪ π[1,1] (WB_aux)));
      TB := (TB ∪ (π[0,1] (TA_aux) ∪ π[1,1] (TC)));
      WB := (WB ∪ WA_aux)
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (((TAQ = TA) ∧ (TBQ = TB)) ∧ ((WAQ = WA) ∧ (WBQ = WB)))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5018
end Benchmark
end Whiel
