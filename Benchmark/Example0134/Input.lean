-- Benchmark contributors: Fangzhu Shen
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Alternating red and blue walks, computed twice: by a
  linear program and by a non-linear one.

  Schema `{B, R, TaX, TbX, TcX, TdX, TaY, TbY, TcY, TdY}`
  (all binary). `B` and `R` are the blue and the red edges
  of a digraph; the `X` relations are the linear program's
  outputs and the `Y` relations the non-linear one's. The
  four computed relations are the walks that begin blue
  and end blue, begin blue and end red, begin red and end
  blue, and begin red and end red, with colours
  alternating along the way. `TaX_aux`, `TbX_aux`,
  `TcX_aux`, `TdX_aux`, `TaY_aux`, `TbY_aux`, `TcY_aux`
  and `TdY_aux` are the snapshots the compiler generates.

  The linear program is
    `TaX(x, y) :- B(x, y)`
    `TaX(x, y) :- B(x, z), TcX(z, y)`
    `TbX(x, y) :- TaX(x, z), R(z, y)`
    `TcX(x, y) :- TdX(x, z), B(z, y)`
    `TdX(x, y) :- R(x, y)`
    `TdX(x, y) :- R(x, z), TbX(z, y)`
  and the non-linear one is
    `TaY(x, y) :- B(x, y)`
    `TaY(x, y) :- TaY(x, z), TcY(z, y)`
    `TbY(x, y) :- B(x, z), R(z, y)`
    `TbY(x, y) :- TaY(x, z), TdY(z, y)`
    `TcY(x, y) :- R(x, z), B(z, y)`
    `TcY(x, y) :- TdY(x, z), TaY(z, y)`
    `TdY(x, y) :- R(x, y)`
    `TdY(x, y) :- TdY(x, z), TbY(z, y)`

  The command is the two compiled programs run one after
  the other. The single loop the tool verifies is computed
  from that sequence by the generic preprocessor.

  The precondition is `true`. The postcondition is that
  the two computations agree relation by relation:
  `TaX = TaY`, `TbX = TbY`, `TcX = TcY` and `TdX = TdY`.
  Each output relation starts empty and accumulates its
  program's immediate consequences, and each loop exits
  only when every output equals its snapshot, so on exit
  the eight outputs hold the least fixpoints of the two
  programs; the postcondition compares those fixpoints.

  Expected verdict: valid. Both programs compute the same
  four families of colour-alternating walks.
-/

namespace Whiel
namespace Benchmark
namespace Example0134

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {B, R, TaX, TbX, TcX, TdX, TaY, TbY, TcY, TdY,
      TaX_aux, TbX_aux, TcX_aux, TdX_aux,
      TaY_aux, TbY_aux, TcY_aux, TdY_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TaX_aux := ∅[2];
      TbX_aux := ∅[2];
      TcX_aux := ∅[2];
      TdX_aux := ∅[2];
      TaX :=
        (B ∪ (π[0, 3] (σ[#1 = #2] (B × TcX_aux))));
      TbX := (π[0, 3] (σ[#1 = #2] (TaX_aux × R)));
      TcX := (π[0, 3] (σ[#1 = #2] (TdX_aux × B)));
      TdX :=
        (R ∪ (π[0, 3] (σ[#1 = #2] (R × TbX_aux))));
      WHILE
          (¬ ((TaX = TaX_aux) ∧
            ((TbX = TbX_aux) ∧
              ((TcX = TcX_aux) ∧
                (TdX = TdX_aux))))) DO
        TaX_aux := TaX;
        TbX_aux := TbX;
        TcX_aux := TcX;
        TdX_aux := TdX;
        TaX :=
          (TaX ∪
            (B ∪
              (π[0, 3]
                (σ[#1 = #2] (B × TcX_aux)))));
        TbX :=
          (TbX ∪
            (π[0, 3] (σ[#1 = #2] (TaX_aux × R))));
        TcX :=
          (TcX ∪
            (π[0, 3] (σ[#1 = #2] (TdX_aux × B))));
        TdX :=
          (TdX ∪
            (R ∪
              (π[0, 3]
                (σ[#1 = #2] (R × TbX_aux)))))
      END;
      TaY_aux := ∅[2];
      TbY_aux := ∅[2];
      TcY_aux := ∅[2];
      TdY_aux := ∅[2];
      TaY :=
        (B ∪
          (π[0, 3]
            (σ[#1 = #2] (TaY_aux × TcY_aux))));
      TbY :=
        ((π[0, 3] (σ[#1 = #2] (B × R))) ∪
          (π[0, 3]
            (σ[#1 = #2] (TaY_aux × TdY_aux))));
      TcY :=
        ((π[0, 3] (σ[#1 = #2] (R × B))) ∪
          (π[0, 3]
            (σ[#1 = #2] (TdY_aux × TaY_aux))));
      TdY :=
        (R ∪
          (π[0, 3]
            (σ[#1 = #2] (TdY_aux × TbY_aux))));
      WHILE
          (¬ ((TaY = TaY_aux) ∧
            ((TbY = TbY_aux) ∧
              ((TcY = TcY_aux) ∧
                (TdY = TdY_aux))))) DO
        TaY_aux := TaY;
        TbY_aux := TbY;
        TcY_aux := TcY;
        TdY_aux := TdY;
        TaY :=
          (TaY ∪
            (B ∪
              (π[0, 3]
                (σ[#1 = #2]
                  (TaY_aux × TcY_aux)))));
        TbY :=
          (TbY ∪
            ((π[0, 3] (σ[#1 = #2] (B × R))) ∪
              (π[0, 3]
                (σ[#1 = #2]
                  (TaY_aux × TdY_aux)))));
        TcY :=
          (TcY ∪
            ((π[0, 3] (σ[#1 = #2] (R × B))) ∪
              (π[0, 3]
                (σ[#1 = #2]
                  (TdY_aux × TaY_aux)))));
        TdY :=
          (TdY ∪
            (R ∪
              (π[0, 3]
                (σ[#1 = #2]
                  (TdY_aux × TbY_aux)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((TaX = TaY) ∧
      ((TbX = TbY) ∧ ((TcX = TcY) ∧ (TdX = TdY))))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0134
end Benchmark
end Whiel
