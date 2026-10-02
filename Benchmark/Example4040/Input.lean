-- Benchmark contributors: Leo Zhang, Val Tannen
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Two-colour reachability and a reformulation read off two
  recursive path views.

  Global schema `{R, B}` (both binary): the red and the blue
  edges of a digraph. The global query is the transitive
  closure of `R ∪ B`, right-linearly:
    `T(x, y) :- R(x, y)`
    `T(x, y) :- B(x, y)`
    `T(x, y) :- R(x, z), T(z, y)`
    `T(x, y) :- B(x, z), T(z, y)`

  The local schema is `{Vr, Vb}`, and the views are
  themselves Datalog over the same edges: the monochrome
  red and blue paths
    `Vr(x, y) :- R(x, y)`
    `Vr(x, y) :- R(x, z), Vr(z, y)`
    `Vb(x, y) :- B(x, y)`
    `Vb(x, y) :- B(x, z), Vb(z, y)`
  The reformulation is a program over that local schema,
  itself recursive:
    `T↑(x, y) :- Vr(x, y)`
    `T↑(x, y) :- Vb(x, y)`
    `T↑(x, y) :- T↑(x, z), T↑(z, y)`

  The command is the three compiled programs run one after
  the other — the closure, the views, then the
  reformulation, which reads the views the program before
  it computed — and `T_aux`, `Vr_aux`, `Vb_aux` and
  `TUp_aux` are the snapshots the compiler generates. The
  single loop the tool verifies is computed from this
  sequence by the generic preprocessor.

  There is no view hypothesis, so the precondition is
  `true`; the postcondition is the claim `T = T↑`.

  Expected verdict: valid. Both sides compute the
  transitive closure of `R ∪ B`, one edge at a time on the
  left and by composing whole monochrome walks on the
  right.
-/

namespace Whiel
namespace Benchmark
namespace Example4040

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {R, B, T, Vr, Vb, TUp, T_aux, Vr_aux, Vb_aux,
      TUp_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    true
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      T_aux := ∅[2];
      T :=
        (R ∪
          (B ∪
            ((π[0, 3] (σ[#1 = #2] (R × T_aux))) ∪
              (π[0, 3] (σ[#1 = #2] (B × T_aux))))));
      WHILE (¬ (T = T_aux)) DO
        T_aux := T;
        T :=
          (T ∪
            (R ∪
              (B ∪
                ((π[0, 3]
                    (σ[#1 = #2] (R × T_aux))) ∪
                  (π[0, 3]
                    (σ[#1 = #2] (B × T_aux)))))))
      END;
      Vr_aux := ∅[2];
      Vb_aux := ∅[2];
      Vr :=
        (R ∪ (π[0, 3] (σ[#1 = #2] (R × Vr_aux))));
      Vb :=
        (B ∪ (π[0, 3] (σ[#1 = #2] (B × Vb_aux))));
      WHILE (¬ ((Vr = Vr_aux) ∧ (Vb = Vb_aux))) DO
        Vr_aux := Vr;
        Vb_aux := Vb;
        Vr :=
          (Vr ∪
            (R ∪
              (π[0, 3] (σ[#1 = #2] (R × Vr_aux)))));
        Vb :=
          (Vb ∪
            (B ∪
              (π[0, 3] (σ[#1 = #2] (B × Vb_aux)))))
      END;
      TUp_aux := ∅[2];
      TUp :=
        (Vr ∪
          (Vb ∪
            (π[0, 3]
              (σ[#1 = #2] (TUp_aux × TUp_aux)))));
      WHILE (¬ (TUp = TUp_aux)) DO
        TUp_aux := TUp;
        TUp :=
          (TUp ∪
            (Vr ∪
              (Vb ∪
                (π[0, 3]
                  (σ[#1 = #2]
                    (TUp_aux × TUp_aux))))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (T = TUp)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example4040
end Benchmark
end Whiel
