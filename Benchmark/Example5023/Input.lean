-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Win-move under the well-founded semantics: the alternating
  fixpoint (Van Gelder) computed with nested loops against
  the attractor computation of Example0162 and legacy
  Example2019 (positions with a move to a losing position
  win; positions all of whose moves lead to winning
  positions lose).

  Input `Move(x, y)`; `Nodes = π[0] Move ∪ π[1] Move` are the
  positions.  The program is
    `win(X) :- move(X, Y), not win(Y)`
  (Van Gelder, Ross, Schlipf, JACM 1991; Abiteboul, Hull,
  Vianu, Foundations of Databases, Example 15.3.1), whose
  well-founded model is three-valued: true (winning), false
  (losing, including positions without moves) and undefined
  (drawn, as on a cycle that no winning move leaves).

  Side 1, the alternating fixpoint.  For a set I of atoms
  taken as true, S_P(I) is the least model of the positive
  program P^I in which `not win(Y)` is read as "Y ∉ I"; the
  alternating sequence is A_0 = ∅, A_{i+1} = S_P(A_i); the
  even subsequence increases to the true set and the odd one
  decreases to the complement of the false set (Van Gelder,
  PODS 1989 / JCSS 1993; Abiteboul, Hull, Vianu, section
  15.3, "A Fixpoint Definition": I_0 = ⊥, I_{i+1} =
  conseq_P(I_i), Theorem 15.3.9).  Encoding: `Under` is the
  current even term A_{2i} and `Over` the odd term after it;
  the outer loop computes `Over := S_P(Under)` and then
  `Under := S_P(Over)` until `Under` stops changing (`Prev`
  is the previous even term; its initial value `Nodes` only
  makes the first test succeed).  Each S_P is the least
  fixpoint of a positive program,
    `OverI(x)  :- Move(x, y), NotUnder(y)`   with `NotUnder = Nodes ∖ Under`
    `UnderI(x) :- Move(x, y), NotOver(y)`    with `NotOver  = Nodes ∖ Over`
  computed by an inner loop in exactly the form the naive
  compiler gives these programs (pinned in Fidelity/).  For
  win-move the positive program is not recursive, so each
  inner loop stabilises after one round, but the inner loop
  is the generic S_P step.  This is the first case with
  nested loops; the preprocessor flattens the inner loops
  under flags.

  Side 2, the attractor (Example0162 / legacy Example2019
  style, simultaneous update): `Win` is the set of positions
  with a move into the previous `Lose`, `Lose` the set of
  positions none of whose moves leaves the previous `Win`
  (positions without moves included), iterated from
  `WinP = LoseP = ∅` until both are stable.

  Precondition `true`; postcondition
    `(Under = Win) ∧ ((Nodes ∖ Over) = Lose)`:
  the well-founded true set is the attractor's win set and
  the false set is its lose set.

  Expected verdict: valid.  S_P(J) is the set of positions
  with a move to a position outside J, so `Nodes ∖ S_P(Win_i)`
  is the next `Lose` and `S_P(Nodes ∖ Lose_i)` the next
  `Win`: the two half-steps of one alternation round are the
  two half-steps of the attractor, which the simultaneous
  update spreads over two rounds.  Expected obstruction:
  rate mismatch with dependent phases.  The flattened
  alternation spends several iterations per outer round (the
  inner fixpoints run under flags) while the attractor
  advances `Win` or `Lose` by half a step per iteration, so
  no iteration-wise equality holds; the invariant has to
  relate `Under`, `Over` to `Win`, `Lose` by inclusions that
  are refreshed only at outer-round boundaries.

  Why it matters: win-move is the standard query that
  stratified negation cannot express and the well-founded
  semantics answers; deductive database systems that
  implement the well-founded semantics compute it by
  alternating-fixpoint-style iteration, while game solvers
  compute the same sets by attractors, and the equivalence is
  what lets one replace the other.  Example5024 claims in
  addition that the odd limit equals the win set (that there
  are no draws) and is invalid.

  Sources: A. Van Gelder, K. A. Ross, J. S. Schlipf, "The
  Well-Founded Semantics for General Logic Programs", JACM 38(3),
  1991, https://doi.org/10.1145/116825.116838; A. Van Gelder, "The
  Alternating Fixpoint of Logic Programs with Negation", PODS 1989,
  https://doi.org/10.1145/73721.73722, and JCSS 47(1), 1993,
  https://doi.org/10.1016/0022-0000(93)90024-Q. The full texts of
  these three could not be retrieved in this session (ACM DL and
  ScienceDirect refused automated access on 2026-09-15); the
  definitions and the win-move example were checked against S.
  Abiteboul, R. Hull, V. Vianu, Foundations of Databases,
  Addison-Wesley 1995, chapter 15 (Example 15.3.1; section 15.3, "A
  Fixpoint Definition"; Example 15.3.8(b); Theorem 15.3.9),
  http://webdam.inria.fr/Alice/pdfs/Chapter-15.pdf, read 2026-09-15.
  Attractor side: Example0162 and the retired corpus case Example2019
  (Oink attractor model), read 2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5023

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Move} (arity: 2),
    {Nodes, Under, Over, Prev, NotUnder, NotOver, OverI, OverI_aux, UnderI, UnderI_aux,
      Win, Lose, WinP, LoseP} (arity: 1)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Nodes := (π[0] Move ∪ π[1] Move);
      Under := ∅[1];
      Over := ∅[1];
      Prev := Nodes;
      WHILE (¬((Under = Prev))) DO
        Prev := Under;
        NotUnder := (Nodes ∖ Under);
        OverI_aux := ∅[1];
        OverI := π[0] (σ[#1 = #2] ((Move × NotUnder)));
        WHILE (¬((OverI = OverI_aux))) DO
          OverI_aux := OverI;
          OverI := (OverI ∪ π[0] (σ[#1 = #2] ((Move × NotUnder))))
        END;
        Over := OverI;
        NotOver := (Nodes ∖ Over);
        UnderI_aux := ∅[1];
        UnderI := π[0] (σ[#1 = #2] ((Move × NotOver)));
        WHILE (¬((UnderI = UnderI_aux))) DO
          UnderI_aux := UnderI;
          UnderI := (UnderI ∪ π[0] (σ[#1 = #2] ((Move × NotOver))))
        END;
        Under := UnderI
      END;
      WinP := ∅[1];
      LoseP := ∅[1];
      Win := π[0] (σ[#1 = #2] (Move × LoseP));
      Lose := (Nodes ∖ π[0] (Move ∖ π[0, 1] (σ[#1 = #2] (Move × WinP))));
      WHILE (¬((Win = WinP) ∧ (Lose = LoseP))) DO
        WinP := Win;
        LoseP := Lose;
        Win := π[0] (σ[#1 = #2] (Move × LoseP));
        Lose := (Nodes ∖ π[0] (Move ∖ π[0, 1] (σ[#1 = #2] (Move × WinP))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((Under = Win) ∧ ((Nodes ∖ Over) = Lose))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5023
end Benchmark
end Whiel
