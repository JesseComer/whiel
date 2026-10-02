-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  DRed (Delete/Rederive) maintenance of a materialised
  transitive closure under deletions against recomputation
  of the closure from the updated edges.

  Inputs `E(x, y)`, the edges, and `Del(x, y)`, the edges to
  delete; precondition `Del ⊆ E`.  The maintained program is
  the closure
    `T(x, y) :- E(x, y)`
    `T(x, z) :- T(x, y), E(y, z)`
  whose materialisation `T` (compiled by the repository's
  naive compiler, snapshot `T_aux`) is computed first.

  Side 1, DRed, hand-written after the step list DR1-DR5 of
  Motik, Nenov, Piro and Horrocks (AAAI 2015, section 3,
  "The Delete/Rederive Algorithm", which restates Gupta,
  Mumick and Subrahmanian, SIGMOD 1993, section 7, steps 1
  and 2; both read 2026-09-15), specialised to this program
  and to a deletion-only update (E⁺ = ∅).  `EN = E ∖ Del` is
  the updated edge set (DR1).  Overdeletion (DR2) evaluates,
  for each rule and each body position, the rule with that
  position taken from the facts deleted in the last round
  (N) and the other positions from the old materialisation
  (I), until nothing new is found:
    `T⁻(x, y) :- E⁻(x, y)`
    `T⁻(x, z) :- T(x, y), E⁻(y, z)`
    `T⁻(x, z) :- T⁻(x, y), E(y, z)`
  The first round, whose N is `Del` itself, is the initial
  `Cand`; `Over` is the set D of overdeleted closure facts,
  `New` the set N = A ∖ D of a round, `Cand` the set A the
  round derives (`E` here is the old edge set, as in the
  paper: I still contains the old explicit facts during
  DR2).  DR3 removes `Over` from `T`; since E⁺ = ∅ and the
  deleted edges are no longer explicit, A is empty and
  rederivation (DR4, rule (6): the head restricted to D, the
  body evaluated in the updated I) is
    `T⁺(x, y) :- T⁻(x, y), EN(x, y)`
    `T⁺(x, z) :- T⁻(x, z), T(x, y), EN(y, z)`
  followed by the reinsertion rounds DR5 that propagate the
  rederived facts through the rule with the new edges
    `T⁺(x, z) :- T⁺(x, y), EN(y, z)`
  until nothing is new.  Intersections are written
  `X ∖ (X ∖ Y)`.

  Side 2, recomputation (compiled from)
    `Tn(x, y) :- EN(x, y)`
    `Tn(x, z) :- Tn(x, y), EN(y, z)`
  with snapshot `Tn_aux`.

  Precondition `Del ⊆ E`; postcondition `T = Tn`.

  Expected verdict: valid; it is Theorem 7.1 of Gupta et al. ("the new derived view
  computed by the DRed algorithm contains tuple t if and only if t has a derivation
  in the database (E ∖ δ⁻) ∪ δ⁺") and, for the same result computed differently,
  Theorem 1 of Motik et al.  Expected obstruction: dependent phases.  The four loops
  must run in order (overdeletion reads the finished `T`, rederivation reads the
  finished `Over`), so the preprocessor draws flags, and the invariant of the
  rederivation phase has to say that `T` stays between the survivors and the new
  closure while `Over` may hold facts that are still derivable; a leveled-framework
  (phase-wise) target rather than a lockstep one.

  Why it matters: DRed is the standard algorithm for
  maintaining recursive materialised views and RDF
  materialisations under deletions (it is the baseline that
  RDFox's Backward/Forward algorithm improves on), and its
  whole point is that the overdeletion is an overestimate:
  Example5017, the twin without the rederivation phase, is
  the naive semi-naive deletion that Gupta et al. describe
  as computing "an overestimate of the tuples that actually
  need to be deleted", and it is invalid.

  Sources: A. Gupta, I. S. Mumick, V. S. Subrahmanian,
  "Maintaining Views Incrementally", SIGMOD 1993,
  https://doi.org/10.1145/170035.170066, read 2026-09-15
  from the authors' copy
  http://www.cs.umd.edu/projects/hermes/publications/postscripts/sigmod93_1.ps
  (section 7, "Incremental Maintenance of Recursive Views",
  steps 1-3 and Theorem 7.1).  B. Motik, Y. Nenov, R. Piro,
  I. Horrocks, "Incremental Update of Datalog
  Materialisation: the Backward/Forward Algorithm", AAAI
  2015, https://doi.org/10.1609/aaai.v29i1.9409, read
  2026-09-15 from
  https://www.cs.ox.ac.uk/people/ian.horrocks/Publications/download/2015/MNPH15b.pdf
  (section 3, steps DR1-DR5, rules (5) and (6); Algorithm 1
  and Theorem 1 for B/F).
-/

namespace Whiel
namespace Benchmark
namespace Example5016

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
      Cand := (Over ∖ (Over ∖ (EN ∪ π[0, 3] (σ[#1 = #2] (T × EN)))));
      WHILE ((Cand ∖ T) ≠ ∅) DO
        New := (Cand ∖ T);
        T := (T ∪ New);
        Cand := π[0, 3] (σ[#1 = #2] (New × EN))
      END;
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

end Example5016
end Benchmark
end Whiel
