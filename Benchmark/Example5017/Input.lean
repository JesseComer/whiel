-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Deletion by overdeletion alone (semi-naive propagation of
  the deleted edges through the closure, without DRed's
  rederivation phase) against recomputation: the invalid
  twin of Example5016.

  Inputs `E(x, y)` and `Del(x, y)` with `Del ⊆ E`; the
  maintained program is the closure
    `T(x, y) :- E(x, y)`
    `T(x, z) :- T(x, y), E(y, z)`
  materialised first (naive compiler, snapshot `T_aux`).

  Side 1 is step 1 of DRed only (Gupta, Mumick and
  Subrahmanian, SIGMOD 1993, section 7; DR1-DR3 of Motik,
  Nenov, Piro and Horrocks, AAAI 2015, section 3): the
  overestimate of the deleted closure facts
    `T⁻(x, y) :- E⁻(x, y)`
    `T⁻(x, z) :- T(x, y), E⁻(y, z)`
    `T⁻(x, z) :- T⁻(x, y), E(y, z)`
  is computed to a fixpoint (`Over`; `Cand` and `New` as in
  Example5017) and removed from `T`, and the algorithm stops
  there: no fact of `Over` is put back.  Gupta et al. say of
  exactly this computation that it "would delete a derived
  tuple that depends upon a deleted base tuple", that
  "alternative derivations of t are not considered", and
  that it "therefore computes an overestimate of the tuples
  that actually need to be deleted".

  Side 2, recomputation (compiled from)
    `Tn(x, y) :- EN(x, y)`
    `Tn(x, z) :- Tn(x, y), EN(y, z)`
  with `EN = E ∖ Del` and snapshot `Tn_aux`.

  Precondition `Del ⊆ E`; postcondition `T = Tn`.

  Expected verdict: invalid.  Witness: E = {(0, 1), (1, 2),
  (0, 2)}, Del = {(0, 1)}: the closure fact (0, 2) has the
  derivation through the deleted edge and is overdeleted,
  but it is also an edge of EN, so the recomputed closure
  keeps it (kernel-checked in Certificate/Invalid.lean).
  The control E = {(0, 1), (1, 2)}, Del = {(1, 2)} is not a
  counterexample: every overdeleted fact really depends on
  the deleted edge.

  Why it matters: this is the mistake DRed exists to
  correct; a maintenance engine that stops after
  propagating deletions loses facts with alternative
  derivations.

  Sources: as Example5017 (Gupta, Mumick, Subrahmanian,
  SIGMOD 1993, section 7, read 2026-09-15 from
  http://www.cs.umd.edu/projects/hermes/publications/postscripts/sigmod93_1.ps;
  Motik, Nenov, Piro, Horrocks, AAAI 2015, section 3, read
  2026-09-15 from
  https://www.cs.ox.ac.uk/people/ian.horrocks/Publications/download/2015/MNPH15b.pdf).
-/

namespace Whiel
namespace Benchmark
namespace Example5017

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, Del, EN, T, T_aux, Over, Cand, New, Tn, Tn_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ (Del ⊆ E) ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      T_aux := ∅[2];
      T := (E ∪ π[0,3] (σ[#1 = #2] ((T_aux × E))));
      WHILE (¬((T = T_aux))) DO
        T_aux := T;
        T := (T ∪ (E ∪ π[0,3] (σ[#1 = #2] ((T_aux × E)))))
      END;
      EN := (E ∖ Del);
      Over := ∅[2];
      Cand := (Del ∪ π[0, 3] (σ[#1 = #2] (T × Del)));
      WHILE ((Cand ∖ Over) ≠ ∅) DO
        New := (Cand ∖ Over);
        Over := (Over ∪ New);
        Cand := π[0, 3] (σ[#1 = #2] (New × E))
      END;
      T := (T ∖ Over);
      Tn_aux := ∅[2];
      Tn := (EN ∪ π[0,3] (σ[#1 = #2] ((Tn_aux × EN))));
      WHILE (¬((Tn = Tn_aux))) DO
        Tn_aux := Tn;
        Tn := (Tn ∪ (EN ∪ π[0,3] (σ[#1 = #2] ((Tn_aux × EN)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (T = Tn)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5017
end Benchmark
end Whiel
