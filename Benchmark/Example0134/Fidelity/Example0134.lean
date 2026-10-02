-- Author: Jesse Comer
import Benchmark.Example0134.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

/-
  Fidelity of `Benchmark/Example0134/Input.lean` to its
  source Datalog programs.

  The two Datalog programs below compute the four families
  of colour-alternating red/blue walks, the first
  linearly and the second non-linearly.

  Compiling each program with the naive compiler and
  writing the results one after the other, with the
  generated snapshots renamed to auxiliary input names,
  reproduces the input file's command exactly, so the
  encoding is faithful by construction rather than by
  inspection. The single loop the tool verifies is
  computed from that sequence by the generic
  preprocessor and is pinned at the end of this module.

  The reference encoding of this problem ran the two
  programs in one hand-written loop that iterated
  destructively: it carried a second copy `SaX` of each
  relation, assigned `TaX := SaX` and then recomputed
  `SaX` from the new `TaX`, so the pair stepped the
  immediate-consequence operator `T ↦ T_P(T)` from the
  empty relation. That operator is monotone, so its orbit
  from `∅` is increasing and its limit is the least
  fixpoint — the same limit the compiled accumulating
  form `T := T ∪ T_P(T)` reaches. The reference
  postcondition was
  `(TaX = TaY) ∧ ((TbX = TbY) ∧ ((TcX = TcY) ∧
  (TdX = TdY)))` over those previous-round copies, which
  at loop exit equal the fixpoints; the input file states
  the same equalities over the compiled output relations,
  which hold the fixpoints on exit, so the two say the
  same thing.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.hashCommand false

------------------------------------------------------------
-- Datalog Sources
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

namespace Example0134

open Whiel.Concrete

def B : ProgramNames :=
  .programSymbol ⟨"B", by decide⟩ 0

def R : ProgramNames :=
  .programSymbol ⟨"R", by decide⟩ 0

def TaX : ProgramNames :=
  .programSymbol ⟨"TaX", by decide⟩ 0

def TbX : ProgramNames :=
  .programSymbol ⟨"TbX", by decide⟩ 0

def TcX : ProgramNames :=
  .programSymbol ⟨"TcX", by decide⟩ 0

def TdX : ProgramNames :=
  .programSymbol ⟨"TdX", by decide⟩ 0

def TaY : ProgramNames :=
  .programSymbol ⟨"TaY", by decide⟩ 0

def TbY : ProgramNames :=
  .programSymbol ⟨"TbY", by decide⟩ 0

def TcY : ProgramNames :=
  .programSymbol ⟨"TcY", by decide⟩ 0

def TdY : ProgramNames :=
  .programSymbol ⟨"TdY", by decide⟩ 0

/- The linear program's schema. -/
def schemaX : UnnamedSchema ProgramNames :=
  programSch![
    {B, R, TaX, TbX, TcX, TdX} (arity: 2)
  ]

/- The non-linear program's schema. -/
def schemaY : UnnamedSchema ProgramNames :=
  programSch![
    {B, R, TaY, TbY, TcY, TdY} (arity: 2)
  ]

/- Colour-alternating walks, linearly. -/
def programX : Datalog.Program Data schemaX :=
  datalog![
    TaX(x1, y1) :- B(x1, y1);
    TaX(x1, y1) :- B(x1, z1), TcX(z1, y1);
    TbX(x1, y1) :- TaX(x1, z1), R(z1, y1);
    TcX(x1, y1) :- TdX(x1, z1), B(z1, y1);
    TdX(x1, y1) :- R(x1, y1);
    TdX(x1, y1) :- R(x1, z1), TbX(z1, y1);
  ]

/- Colour-alternating walks, non-linearly. -/
def programY : Datalog.Program Data schemaY :=
  datalog![
    TaY(x1, y1) :- B(x1, y1);
    TaY(x1, y1) :- TaY(x1, z1), TcY(z1, y1);
    TbY(x1, y1) :- B(x1, z1), R(z1, y1);
    TbY(x1, y1) :- TaY(x1, z1), TdY(z1, y1);
    TcY(x1, y1) :- R(x1, z1), B(z1, y1);
    TcY(x1, y1) :- TdY(x1, z1), TaY(z1, y1);
    TdY(x1, y1) :- R(x1, y1);
    TdY(x1, y1) :- TdY(x1, z1), TbY(z1, y1);
  ]

end Example0134

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Compiled Sequence
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

namespace Example0134

open Whiel.Concrete

/- The compiled linear program, in input names. -/
def rawX : RawCmd ProgramNames Data :=
  mapCmd toRawInput programX.toWhielCmd.toRaw

/- The compiled non-linear program, in input names. -/
def rawY : RawCmd ProgramNames Data :=
  mapCmd toRawInput programY.toWhielCmd.toRaw

/- The reduction: the two compiled programs in sequence. -/
def compiledRaw : RawCmd ProgramNames Data :=
  seqAfter rawX rawY

end Example0134

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Input Fidelity
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

namespace Example0134

open Whiel.Concrete

open Whiel.Benchmark.Example0134
  (inputSchema inputPre inputCmd inputPost)

/- The claim: the two computations agree. -/
def claimRaw : RawGuard ProgramNames Data :=
  .and (.eq (.rel TaX) (.rel TaY))
    (.and (.eq (.rel TbX) (.rel TbY))
      (.and (.eq (.rel TcX) (.rel TcY))
        (.eq (.rel TdX) (.rel TdY))))

theorem inputPre_eq :
    inputPre.formula.toRaw = .«true» := by
  decide

theorem inputPost_eq :
    inputPost.formula.toRaw = claimRaw := by
  decide

theorem compiledRaw_eq :
    compiledRaw = inputCmd.toRaw := by
  decide +kernel

/- The renamed sequence is the input file's command. -/
theorem inputCmd_eq :
    compiledRaw.toCmd? inputSchema = some inputCmd :=
  toCmd?_eq compiledRaw_eq

end Example0134

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Preprocessed Loop
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

namespace Example0134

open Whiel.Benchmark.Example0134 (inputPreproc)

/-
  The single loop the generic preprocessor computes
  from the sequence above. It is what the tool verifies,
  so it is pinned here rather than only displayed.
-/
/-- info:
WHILE ((¬(((TaX = TaX_aux) ∧ ((TbX = TbX_aux) ∧ ((TcX = TcX_aux) ∧ (TdX = TdX_aux)))))) ∨ (¬(((TaY = TaY_aux) ∧ ((TbY = TbY_aux) ∧ ((TcY = TcY_aux) ∧ (TdY = TdY_aux))))))) DO
IF (¬(((TaX = TaX_aux) ∧ ((TbX = TbX_aux) ∧ ((TcX = TcX_aux) ∧ (TdX = TdX_aux)))))) THEN
TaX_aux := TaX;
TbX_aux := TbX;
TcX_aux := TcX;
TdX_aux := TdX;
TaX := (TaX ∪ (B ∪ π[0,3] (σ[#1 = #2] ((B × TcX_aux)))));
TbX := (TbX ∪ π[0,3] (σ[#1 = #2] ((TaX_aux × R))));
TcX := (TcX ∪ π[0,3] (σ[#1 = #2] ((TdX_aux × B))));
TdX := (TdX ∪ (R ∪ π[0,3] (σ[#1 = #2] ((R × TbX_aux)))))
ELSE
SKIP
END;
IF (¬(((TaY = TaY_aux) ∧ ((TbY = TbY_aux) ∧ ((TcY = TcY_aux) ∧ (TdY = TdY_aux)))))) THEN
TaY_aux := TaY;
TbY_aux := TbY;
TcY_aux := TcY;
TdY_aux := TdY;
TaY := (TaY ∪ (B ∪ π[0,3] (σ[#1 = #2] ((TaY_aux × TcY_aux)))));
TbY := (TbY ∪ (π[0,3] (σ[#1 = #2] ((B × R))) ∪ π[0,3] (σ[#1 = #2] ((TaY_aux × TdY_aux)))));
TcY := (TcY ∪ (π[0,3] (σ[#1 = #2] ((R × B))) ∪ π[0,3] (σ[#1 = #2] ((TdY_aux × TaY_aux)))));
TdY := (TdY ∪ (R ∪ π[0,3] (σ[#1 = #2] ((TdY_aux × TbY_aux)))))
ELSE
SKIP
END
END
-/
#guard_msgs (whitespace := lax) in
#eval DBTPretty.display ("\n" ++ inputPreproc.loopCmd.pretty)

end Example0134

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel
