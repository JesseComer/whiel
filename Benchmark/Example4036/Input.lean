-- Benchmark contributors: Leo Zhang, Val Tannen
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Single-airline reachability and a reformulation over
  three flight views, tested for containment.

  Global schema `{F}` (ternary): `F(x, y, u)` is a non-stop
  flight from airport `x` to airport `y` on airline `u`.
  The constants are `"a"`, `"b"`, `"c"`. The global query
  computes per-airline reachability and then the airports
  reachable from `"b"` without changing airline:
    `T(x, y, u) :- F(x, y, u)`
    `T(x, y, u) :- F(x, z, u), T(z, y, u)`
    `Q(y) :- T("b", y, u)`

  Local schema `{Va, Vb, Vc}`, the three conjunctive views
    `Va(x, y) ↔ F(x, y, "a")`
    `Vb(y, u) ↔ F("b", y, u)`
    `Vc(x, z) ↔ ∃y. F(x, y, "c") ∧ F(y, z, "c")`
  with the proposed reformulation
    `Q↑(y) :- Va("b", y)`
    `Q↑(z) :- Vb(y, "c"), Vc(y, z)`
    `Q↑(y) :- Vb(y, u)`

  The command is the two compiled programs run one after
  the other, and `T_aux`, `Q_aux` and `QUp_aux` are the
  snapshots the compiler generates. The single loop the
  tool verifies is computed from this sequence by the
  generic preprocessor.

  The precondition is the three view equations. The
  postcondition is the claim that the reformulation is
  contained in the global query, `Q↑ ⊆ Q`.

  Expected verdict: valid. Every `Q↑` rule unfolds to a
  same-airline itinerary out of `"b"`, so `Q↑ ⊆ Q`. No
  distinctness of the constants is assumed.
-/

namespace Whiel
namespace Benchmark
namespace Example4036

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Q, QUp, Q_aux, QUp_aux} (arity: 1),
    {Va, Vb, Vc} (arity: 2),
    {F, T, T_aux} (arity: 3)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((Va = (π[0, 1] (σ[#2 = "a"] F))) ∧
      ((Vb = (π[1, 2] (σ[#0 = "b"] F))) ∧
        (Vc =
          (π[0, 4]
            (σ[((#2 = "c" ∧ #1 = #3) ∧ #5 = "c")]
              (F × F))))))
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      T_aux := ∅[3];
      Q_aux := ∅[1];
      T :=
        (F ∪
          (π[0, 4, 2]
            (σ[(#1 = #3 ∧ #2 = #5)] (F × T_aux))));
      Q := (π[1] (σ[#0 = "b"] T_aux));
      WHILE (¬ ((T = T_aux) ∧ (Q = Q_aux))) DO
        T_aux := T;
        Q_aux := Q;
        T :=
          (T ∪
            (F ∪
              (π[0, 4, 2]
                (σ[(#1 = #3 ∧ #2 = #5)]
                  (F × T_aux)))));
        Q := (Q ∪ (π[1] (σ[#0 = "b"] T_aux)))
      END;
      QUp_aux := ∅[1];
      QUp :=
        ((π[1] (σ[#0 = "b"] Va)) ∪
          ((π[3]
              (σ[(#1 = "c" ∧ #0 = #2)] (Vb × Vc))) ∪
            (π[0] Vb)));
      WHILE (¬ (QUp = QUp_aux)) DO
        QUp_aux := QUp;
        QUp :=
          (QUp ∪
            ((π[1] (σ[#0 = "b"] Va)) ∪
              ((π[3]
                  (σ[(#1 = "c" ∧ #0 = #2)]
                    (Vb × Vc))) ∪
                (π[0] Vb))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (QUp ⊆ Q)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example4036
end Benchmark
end Whiel
