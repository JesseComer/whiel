-- Benchmark contributors: Fangzhu Shen
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  All paths through odd and even halves, computed twice:
  by a linear program and by a non-linear one.

  Schema `{E, TaX, TbX, TcX, TaY, TbY, TcY}` (all binary).
  `E` is the edge relation of a digraph; the `X` relations
  are the linear program's outputs and the `Y` relations
  the non-linear one's, with `TcX` and `TcY` the union of
  the two halves. `TaX_aux`, `TbX_aux`, `TcX_aux`,
  `TaY_aux`, `TbY_aux` and `TcY_aux` are the snapshots the
  compiler generates.

  The linear program is
    `TbX(x, y) :- E(x, y)`
    `TbX(x, y) :- E(x, z), TaX(z, y)`
    `TaX(x, y) :- E(x, z), TbX(z, y)`
    `TcX(x, y) :- TaX(x, y)`
    `TcX(x, y) :- TbX(x, y)`
  and the non-linear one is
    `TaY(x, y) :- E(x, z), E(z, y)`
    `TaY(x, y) :- TaY(x, z), TaY(z, y)`
    `TaY(x, y) :- TbY(x, z), TbY(z, y)`
    `TbY(x, y) :- E(x, y)`
    `TbY(x, y) :- TbY(x, z), TaY(z, y)`
    `TbY(x, y) :- TaY(x, z), TbY(z, y)`
    `TcY(x, y) :- TaY(x, y)`
    `TcY(x, y) :- TbY(x, y)`

  The command is the two compiled programs run one after
  the other. The single loop the tool verifies is computed
  from that sequence by the generic preprocessor.

  The precondition is `true`. The postcondition is that
  the two computations agree relation by relation:
  `TaX = TaY`, `TbX = TbY` and `TcX = TcY`. Each output
  relation starts empty and accumulates its program's
  immediate consequences, and each loop exits only when
  every output equals its snapshot, so on exit the six
  outputs hold the least fixpoints of the two programs;
  the postcondition compares those fixpoints.

  Expected verdict: valid. Both programs compute the paths
  of even length, of odd length, and their union.
-/

namespace Whiel
namespace Benchmark
namespace Example0133

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, TaX, TbX, TcX, TaY, TbY, TcY,
      TaX_aux, TbX_aux, TcX_aux,
      TaY_aux, TbY_aux, TcY_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TbX_aux := ∅[2];
      TaX_aux := ∅[2];
      TcX_aux := ∅[2];
      TbX :=
        (E ∪ (π[0, 3] (σ[#1 = #2] (E × TaX_aux))));
      TaX := (π[0, 3] (σ[#1 = #2] (E × TbX_aux)));
      TcX := (TaX_aux ∪ TbX_aux);
      WHILE
          (¬ ((TbX = TbX_aux) ∧
            ((TaX = TaX_aux) ∧ (TcX = TcX_aux)))) DO
        TbX_aux := TbX;
        TaX_aux := TaX;
        TcX_aux := TcX;
        TbX :=
          (TbX ∪
            (E ∪
              (π[0, 3]
                (σ[#1 = #2] (E × TaX_aux)))));
        TaX :=
          (TaX ∪
            (π[0, 3] (σ[#1 = #2] (E × TbX_aux))));
        TcX := (TcX ∪ (TaX_aux ∪ TbX_aux))
      END;
      TaY_aux := ∅[2];
      TbY_aux := ∅[2];
      TcY_aux := ∅[2];
      TaY :=
        ((π[0, 3] (σ[#1 = #2] (E × E))) ∪
          ((π[0, 3]
              (σ[#1 = #2] (TaY_aux × TaY_aux))) ∪
            (π[0, 3]
              (σ[#1 = #2] (TbY_aux × TbY_aux)))));
      TbY :=
        (E ∪
          ((π[0, 3]
              (σ[#1 = #2] (TbY_aux × TaY_aux))) ∪
            (π[0, 3]
              (σ[#1 = #2] (TaY_aux × TbY_aux)))));
      TcY := (TaY_aux ∪ TbY_aux);
      WHILE
          (¬ ((TaY = TaY_aux) ∧
            ((TbY = TbY_aux) ∧ (TcY = TcY_aux)))) DO
        TaY_aux := TaY;
        TbY_aux := TbY;
        TcY_aux := TcY;
        TaY :=
          (TaY ∪
            ((π[0, 3] (σ[#1 = #2] (E × E))) ∪
              ((π[0, 3]
                  (σ[#1 = #2]
                    (TaY_aux × TaY_aux))) ∪
                (π[0, 3]
                  (σ[#1 = #2]
                    (TbY_aux × TbY_aux))))));
        TbY :=
          (TbY ∪
            (E ∪
              ((π[0, 3]
                  (σ[#1 = #2]
                    (TbY_aux × TaY_aux))) ∪
                (π[0, 3]
                  (σ[#1 = #2]
                    (TaY_aux × TbY_aux))))));
        TcY := (TcY ∪ (TaY_aux ∪ TbY_aux))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((TaX = TaY) ∧ ((TbX = TbY) ∧ (TcX = TcY)))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0133
end Benchmark
end Whiel
