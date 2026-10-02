-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  One pass over the dependencies of a full-TGD ChaseBench
  scenario against the parallel chase: the invalid twin of
  Example5018.

  Scenario, names and the parallel side are those of
  Example5018 (the full-TGD subset of
  `scenarios/correctness/tgds` of ChaseBench at commit
  7427e1c1e3196769ee4ea04557465965ec26d02b, read 2026-09-15:
  `S` = s, `TA` = t1, `TB` = t2, `TC` = t3, `WA` = w1,
  `WB` = w2, dependencies
    `TA(x, y, z) :- S(x, y, z)`
    `WA(x, y)    :- S(x, y, z)`
    `TB(x, y)    :- TA(x, y, z)`
    `TB(y, y)    :- TC(x, y, z)`
    `WB(x, y)    :- WA(x, y)`
    `WA(y, y)    :- WB(x, y)`
  compiled by the naive compiler with snapshots `TA_aux`,
  `TB_aux`, `WA_aux`, `WB_aux`).

  Side 1 applies the s-t dependencies once and then chases
  each target dependency to its fixpoint once, in file
  order, without repeating the sweep: the sequence of
  INSERT ... SELECT statements one writes when the
  dependencies are executed as a script.  It is not a chase
  sequence: after `w2(?a,?b) -> w1(?b,?b)` fires, the
  earlier `w1(?a,?b) -> w2(?a,?b)` has a new active trigger
  that is never applied, which violates the fairness
  condition of Benedikt et al., Section 2.

  Precondition `true`; postcondition
  `(TAQ = TA) ∧ (TBQ = TB) ∧ (WAQ = WA) ∧ (WBQ = WB)`.

  Expected verdict: invalid.  Witness: S = {(1, 2, 3)}, TC
  empty.  The chase derives w1(1,2), w2(1,2), w1(2,2) and
  then w2(2,2); the single pass stops with WBQ = {(1, 2)}
  (kernel-checked in Certificate/Invalid.lean).  Controls:
  S = {(1, 1, 1)} (the new w1 fact is the old one) and
  S empty with TC = {(0, 5, 0)} are not counterexamples.

  Why it matters: as for Example5018; the twin records that
  the fixpoint sweep, not the order, is what the chase
  needs.

  Sources: as Example5018 (ChaseBench scenario files and
  Benedikt et al., PODS 2017, read 2026-09-15).
-/

namespace Whiel
namespace Benchmark
namespace Example5019

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

end Example5019
end Benchmark
end Whiel
