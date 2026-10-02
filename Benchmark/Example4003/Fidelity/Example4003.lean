-- Author: Jesse Comer
import Benchmark.Example4003.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

/-
  Fidelity of `Benchmark/Example4003/Input.lean` to its
  source Datalog programs.

  The two Datalog programs below are the left-linear
  transitive closure and its length-two path-view
  reformulation; they are `Example4002`'s programs, under a
  containment rather than an equality.

  Compiling each program with the naive compiler and
  writing the results one after the other, with the
  generated snapshots renamed to auxiliary input names,
  reproduces the input file's command exactly, so the
  encoding is faithful by construction rather than by
  inspection. The single loop the tool verifies is
  computed from that sequence by the generic
  preprocessor and is pinned at the end of this module.
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

namespace Example4003

open Whiel.Concrete

def E : ProgramNames :=
  .programSymbol ⟨"E", by decide⟩ 0

def T : ProgramNames :=
  .programSymbol ⟨"T", by decide⟩ 0

def V : ProgramNames :=
  .programSymbol ⟨"V", by decide⟩ 0

def TUp : ProgramNames :=
  .programSymbol ⟨"TUp", by decide⟩ 0

/- The global schema and its transitive-closure output. -/
def globalSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, T} (arity: 2)
  ]

/- The local schema and the reformulation's output. -/
def localSchema : UnnamedSchema ProgramNames :=
  programSch![
    {TUp} (arity: 2),
    {V} (arity: 3)
  ]

/- `T xy :- Exy` and `T xy :- Exz, T zy`. -/
def globalProgram : Datalog.Program Data globalSchema :=
  datalog![
    T(x1, y1) :- E(x1, y1);
    T(x1, y1) :- E(x1, z1), T(z1, y1);
  ]

/- `T↑ xy :- V xwy` and `T↑ xz :- V xwy, T↑ yz`. -/
def localProgram : Datalog.Program Data localSchema :=
  datalog![
    TUp(x1, y1) :- V(x1, z1, y1);
    TUp(x1, x2) :- V(x1, z1, y1), TUp(y1, x2);
  ]

end Example4003

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

namespace Example4003

open Whiel.Concrete

/- The compiled global program, in input names. -/
def globalRaw : RawCmd ProgramNames Data :=
  mapCmd toRawInput globalProgram.toWhielCmd.toRaw

/- The compiled local program, in input names. -/
def localRaw : RawCmd ProgramNames Data :=
  mapCmd toRawInput localProgram.toWhielCmd.toRaw

/- The reduction: the two compiled programs in sequence. -/
def compiledRaw : RawCmd ProgramNames Data :=
  seqAfter globalRaw localRaw

end Example4003

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

namespace Example4003

open Whiel.Concrete

open Whiel.Benchmark.Example4003
  (inputSchema inputPre inputCmd inputPost)

/- `V = E ∘ E`, keeping the midpoint. -/
def viewConstraintRaw : RawGuard ProgramNames Data :=
  .eq (.rel V)
    (.proj [0, 1, 3]
      (.select (Sel.eqIdx 1 2)
        (.prod (.rel E) (.rel E))))

/- The claim `T↑ ⊆ T`. -/
def claimRaw : RawGuard ProgramNames Data :=
  .subset (.rel TUp) (.rel T)

theorem inputPre_eq :
    inputPre.formula.toRaw = viewConstraintRaw := by
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

end Example4003

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Regression Guard Against the Accelerated Variant
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

namespace Example4003

open Whiel.Concrete

/-
  The reference encoding's transitive closure, with the
  derived two-edge and three-edge rules added so that the
  frontier advances two edges per iteration. Its least
  fixpoint is still the transitive closure of `E`.
-/
def acceleratedProgram :
    Datalog.Program Data globalSchema :=
  datalog![
    T(x1, y1) :- E(x1, y1);
    T(x1, y1) :- E(x1, z1), E(z1, y1);
    T(x1, y1) :- E(x1, z1), T(z1, y1);
    T(x1, y1) :- E(x1, z1), E(z1, x2), T(x2, y1);
  ]

/- A two-edge path, with the output relation empty. -/
def twoEdges : Instance Data globalSchema :=
  Instance.update (Instance.empty globalSchema)
    (globalSchema.sym E)
    (Notation.relationFromRows 2
      [[Data.num 0, Data.num 1],
       [Data.num 1, Data.num 2]])

/-
  One immediate-consequence step separates the two: the
  verbatim program derives only the two edges, while the
  accelerated one already derives `(0, 2)`.
-/
theorem accelerated_differs_after_one_step :
    (globalProgram.immediate twoEdges)
        (globalSchema.sym T) ≠
      (acceleratedProgram.immediate twoEdges)
        (globalSchema.sym T) := by
  decide +kernel

end Example4003

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

namespace Example4003

open Whiel.Benchmark.Example4003 (inputPreproc)

/-
  The single loop the generic preprocessor computes
  from the sequence above. It is what the tool verifies,
  so it is pinned here rather than only displayed.
-/
/-- info:
WHILE ((¬((T = T_aux))) ∨ (¬((TUp = TUp_aux)))) DO
IF (¬((T = T_aux))) THEN
T_aux := T;
T := (T ∪ (E ∪ π[0,3] (σ[#1 = #2] ((E × T_aux)))))
ELSE
SKIP
END;
IF (¬((TUp = TUp_aux))) THEN
TUp_aux := TUp;
TUp := (TUp ∪ (π[0,2] (V) ∪ π[0,4] (σ[#2 = #3] ((V × TUp_aux)))))
ELSE
SKIP
END
END
-/
#guard_msgs (whitespace := lax) in
#eval DBTPretty.display ("\n" ++ inputPreproc.loopCmd.pretty)

end Example4003

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel
