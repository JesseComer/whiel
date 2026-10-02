-- Author: Jesse Comer
import Benchmark.Example0133.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

/-
  Fidelity of `Benchmark/Example0133/Input.lean` to its
  source Datalog programs.

  The two Datalog programs below are the linear and the
  non-linear odd/even path programs, each with the union
  of its two halves as a third output.

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
  `(TaX = TaY) ∧ ((TbX = TbY) ∧ (TcX = TcY))` over those
  previous-round copies, which at loop exit equal the
  fixpoints; the input file states the same equalities
  over the compiled output relations, which hold the
  fixpoints on exit, so the two say the same thing.
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

namespace Example0133

open Whiel.Concrete

def E : ProgramNames :=
  .programSymbol ⟨"E", by decide⟩ 0

def TaX : ProgramNames :=
  .programSymbol ⟨"TaX", by decide⟩ 0

def TbX : ProgramNames :=
  .programSymbol ⟨"TbX", by decide⟩ 0

def TcX : ProgramNames :=
  .programSymbol ⟨"TcX", by decide⟩ 0

def TaY : ProgramNames :=
  .programSymbol ⟨"TaY", by decide⟩ 0

def TbY : ProgramNames :=
  .programSymbol ⟨"TbY", by decide⟩ 0

def TcY : ProgramNames :=
  .programSymbol ⟨"TcY", by decide⟩ 0

/- The linear program's schema. -/
def schemaX : UnnamedSchema ProgramNames :=
  programSch![
    {E, TaX, TbX, TcX} (arity: 2)
  ]

/- The non-linear program's schema. -/
def schemaY : UnnamedSchema ProgramNames :=
  programSch![
    {E, TaY, TbY, TcY} (arity: 2)
  ]

/- Odd and even paths and their union, linearly. -/
def programX : Datalog.Program Data schemaX :=
  datalog![
    TbX(x1, y1) :- E(x1, y1);
    TbX(x1, y1) :- E(x1, z1), TaX(z1, y1);
    TaX(x1, y1) :- E(x1, z1), TbX(z1, y1);
    TcX(x1, y1) :- TaX(x1, y1);
    TcX(x1, y1) :- TbX(x1, y1);
  ]

/- Odd and even paths and their union, non-linearly. -/
def programY : Datalog.Program Data schemaY :=
  datalog![
    TaY(x1, y1) :- E(x1, z1), E(z1, y1);
    TaY(x1, y1) :- TaY(x1, z1), TaY(z1, y1);
    TaY(x1, y1) :- TbY(x1, z1), TbY(z1, y1);
    TbY(x1, y1) :- E(x1, y1);
    TbY(x1, y1) :- TbY(x1, z1), TaY(z1, y1);
    TbY(x1, y1) :- TaY(x1, z1), TbY(z1, y1);
    TcY(x1, y1) :- TaY(x1, y1);
    TcY(x1, y1) :- TbY(x1, y1);
  ]

end Example0133

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

namespace Example0133

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

end Example0133

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

namespace Example0133

open Whiel.Concrete

open Whiel.Benchmark.Example0133
  (inputSchema inputPre inputCmd inputPost)

/- The claim: the two computations agree. -/
def claimRaw : RawGuard ProgramNames Data :=
  .and (.eq (.rel TaX) (.rel TaY))
    (.and (.eq (.rel TbX) (.rel TbY))
      (.eq (.rel TcX) (.rel TcY)))

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

end Example0133

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

namespace Example0133

open Whiel.Benchmark.Example0133 (inputPreproc)

/-
  The single loop the generic preprocessor computes
  from the sequence above. It is what the tool verifies,
  so it is pinned here rather than only displayed.
-/
/-- info:
WHILE ((¬(((TbX = TbX_aux) ∧ ((TaX = TaX_aux) ∧ (TcX = TcX_aux))))) ∨ (¬(((TaY = TaY_aux) ∧ ((TbY = TbY_aux) ∧ (TcY = TcY_aux)))))) DO
IF (¬(((TbX = TbX_aux) ∧ ((TaX = TaX_aux) ∧ (TcX = TcX_aux))))) THEN
TbX_aux := TbX;
TaX_aux := TaX;
TcX_aux := TcX;
TbX := (TbX ∪ (E ∪ π[0,3] (σ[#1 = #2] ((E × TaX_aux)))));
TaX := (TaX ∪ π[0,3] (σ[#1 = #2] ((E × TbX_aux))));
TcX := (TcX ∪ (TaX_aux ∪ TbX_aux))
ELSE
SKIP
END;
IF (¬(((TaY = TaY_aux) ∧ ((TbY = TbY_aux) ∧ (TcY = TcY_aux))))) THEN
TaY_aux := TaY;
TbY_aux := TbY;
TcY_aux := TcY;
TaY := (TaY ∪ (π[0,3] (σ[#1 = #2] ((E × E))) ∪ (π[0,3] (σ[#1 = #2] ((TaY_aux × TaY_aux))) ∪ π[0,3] (σ[#1 = #2] ((TbY_aux × TbY_aux))))));
TbY := (TbY ∪ (E ∪ (π[0,3] (σ[#1 = #2] ((TbY_aux × TaY_aux))) ∪ π[0,3] (σ[#1 = #2] ((TaY_aux × TbY_aux))))));
TcY := (TcY ∪ (TaY_aux ∪ TbY_aux))
ELSE
SKIP
END
END
-/
#guard_msgs (whitespace := lax) in
#eval DBTPretty.display ("\n" ++ inputPreproc.loopCmd.pretty)

end Example0133

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel
