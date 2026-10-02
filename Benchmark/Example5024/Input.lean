-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Win-move under the well-founded semantics, the invalid
  twin of Example5023: the alternating fixpoint against the
  attractor, claiming in addition that the odd limit (the
  positions that are not false) is the attractor's win set,
  that is, that the well-founded model of win-move is total.

  Input, sides and encoding are those of Example5023: the
  alternating fixpoint A_0 = ∅, A_{i+1} = S_P(A_i) of
    `win(X) :- move(X, Y), not win(Y)`
  with the inner least fixpoints
    `OverI(x)  :- Move(x, y), NotUnder(y)`   (`NotUnder = Nodes ∖ Under`)
    `UnderI(x) :- Move(x, y), NotOver(y)`    (`NotOver  = Nodes ∖ Over`)
  as nested loops, and the attractor `Win`/`Lose` of
  Example0162 / legacy Example2019.

  Precondition `true`; postcondition
    `(Under = Win) ∧ (Over = Win)`.

  Expected verdict: invalid.  Witness: the two-cycle
  `Move = {(0, 1), (1, 0)}`.  Neither position can force a
  win, so the true set and the attractor's win set are empty,
  but neither position is false either: `Over = S_P(∅) =
  {0, 1}` (each has a move to a position not known to win),
  and the odd sequence stays there (kernel-checked in
  Certificate/Invalid.lean).  Controls: the chain
  `{(0, 1), (1, 2)}` and the game `{(0, 1), (1, 2), (2, 0),
  (2, 3)}`, in which every position is won or lost, are not
  counterexamples.

  Why it matters: as for Example5023; the twin records the
  undefined truth value that distinguishes the well-founded
  model from a two-valued reading of the overestimate
  (Abiteboul, Hull, Vianu, Example 15.3.8(b): win(a), win(b),
  win(c) unknown).

  Sources: as Example5023 (Van Gelder, Ross, Schlipf, JACM
  1991; Van Gelder, PODS 1989 / JCSS 1993, not retrievable in
  this session; Abiteboul, Hull, Vianu, Foundations of
  Databases, chapter 15, read 2026-09-15; Example0162 and
  legacy Example2019).
-/

namespace Whiel
namespace Benchmark
namespace Example5024

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
    ((Under = Win) ∧ (Over = Win))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5024
end Benchmark
end Whiel
