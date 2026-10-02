-- Author: Jesse Comer
import Benchmark.Example4037.Input
import Whiel.DatalogCompiler.Naive
import Whiel.Eval.CounterExample.Kernel
import Benchmark.Fidelity.Support

/-
  Fidelity of `Benchmark/Example4037/Input.lean` to its
  source Datalog programs.

  The two Datalog programs below are the single-airline
  reachability query and its reformulation over the three
  flight views; they are `Example4036`'s programs, under
  the reverse containment.

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

namespace Example4037

open Whiel.Concrete

def F : ProgramNames :=
  .programSymbol ⟨"F", by decide⟩ 0

def T : ProgramNames :=
  .programSymbol ⟨"T", by decide⟩ 0

def Q : ProgramNames :=
  .programSymbol ⟨"Q", by decide⟩ 0

def Va : ProgramNames :=
  .programSymbol ⟨"Va", by decide⟩ 0

def Vb : ProgramNames :=
  .programSymbol ⟨"Vb", by decide⟩ 0

def Vc : ProgramNames :=
  .programSymbol ⟨"Vc", by decide⟩ 0

def QUp : ProgramNames :=
  .programSymbol ⟨"QUp", by decide⟩ 0

/- The global schema and its two query outputs. -/
def globalSchema : UnnamedSchema ProgramNames :=
  programSch![
    {F, T} (arity: 3),
    {Q} (arity: 1)
  ]

/- The local schema and the reformulation's output. -/
def localSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Va, Vb, Vc} (arity: 2),
    {QUp} (arity: 1)
  ]

/-
  `T xyu :- Fxyu`, `T xyu :- Fxzu, T zyu`, and
  `Qy :- T byu`.
-/
def globalProgram : Datalog.Program Data globalSchema :=
  datalog![
    T(x1, y1, x2) :- F(x1, y1, x2);
    T(x1, y1, x2) :- F(x1, z1, x2), T(z1, y1, x2);
    Q(y1) :- T("b", y1, x2);
  ]

/-
  `Q↑ y :- Va by`, `Q↑ z :- Vb yc, Vc yz`, and
  `Q↑ y :- Vb yu`.
-/
def localProgram : Datalog.Program Data localSchema :=
  datalog![
    QUp(y1) :- Va("b", y1);
    QUp(z1) :- Vb(y1, "c"), Vc(y1, z1);
    QUp(y1) :- Vb(y1, x2);
  ]

end Example4037

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

namespace Example4037

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

end Example4037

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

namespace Example4037

open Whiel.Concrete

open Whiel.Benchmark.Example4037
  (inputSchema inputPre inputCmd inputPost)

/- `Va xy :- Fxya`. -/
def airlineARaw : RawRAExpr ProgramNames Data :=
  .proj [0, 1]
    (.select (Sel.eqConst 2 (Data.str "a")) (.rel F))

/- `Vb yu :- Fbyu`. -/
def outOfBRaw : RawRAExpr ProgramNames Data :=
  .proj [1, 2]
    (.select (Sel.eqConst 0 (Data.str "b")) (.rel F))

/- `Vc xz :- Fxyc, Fyzc`. -/
def twoHopCRaw : RawRAExpr ProgramNames Data :=
  .proj [0, 4]
    (.select
      (Sel.and
        (Sel.and (Sel.eqConst 2 (Data.str "c"))
          (Sel.eqIdx 1 3))
        (Sel.eqConst 5 (Data.str "c")))
      (.prod (.rel F) (.rel F)))

/- The three exact conjunctive view equations. -/
def viewConstraintRaw : RawGuard ProgramNames Data :=
  .and (.eq (.rel Va) airlineARaw)
    (.and (.eq (.rel Vb) outOfBRaw)
      (.eq (.rel Vc) twoHopCRaw))

/- The claim `Q ⊆ Q↑`. -/
def claimRaw : RawGuard ProgramNames Data :=
  .subset (.rel Q) (.rel QUp)

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

end Example4037

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Expected Counterexample
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

namespace Example4037

open Whiel.Concrete

open Whiel.Benchmark.Example4037
  (inputSchema inputPre inputCmd inputPost)

/- The flights `F(b, x, d)` and `F(x, y, d)`. -/
def witnessFlights : Instance Data inputSchema :=
  Instance.update (Instance.empty inputSchema)
    (inputSchema.sym F)
    (Notation.relationFromRows 3
      [[Data.str "b", Data.str "x", Data.str "d"],
        [Data.str "x", Data.str "y", Data.str "d"]])

/- The views on those flights: only `Vb` is nonempty. -/
def witness : Instance Data inputSchema :=
  Instance.update witnessFlights
    (inputSchema.sym Vb)
    (Notation.relationFromRows 2
      [[Data.str "x", Data.str "d"]])

/- `y` is reachable from `b` but is in no view. -/
theorem witness_refutes :
    Hoare.CounterExample.kernelRefutes 64 inputPre
      inputCmd inputPost witness = Bool.true := by
  decide +kernel

end Example4037

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

namespace Example4037

open Whiel.Benchmark.Example4037 (inputPreproc)

/-
  The single loop the generic preprocessor computes
  from the sequence above. It is what the tool verifies,
  so it is pinned here rather than only displayed.
-/
/-- info:
WHILE ((¬(((T = T_aux) ∧ (Q = Q_aux)))) ∨ (¬((QUp = QUp_aux)))) DO
IF (¬(((T = T_aux) ∧ (Q = Q_aux)))) THEN
T_aux := T;
Q_aux := Q;
T := (T ∪ (F ∪ π[0,4,2] (σ[(#1 = #3 ∧ #2 = #5)] ((F × T_aux)))));
Q := (Q ∪ π[1] (σ[#0 = "b"] (T_aux)))
ELSE
SKIP
END;
IF (¬((QUp = QUp_aux))) THEN
QUp_aux := QUp;
QUp := (QUp ∪ (π[1] (σ[#0 = "b"] (Va)) ∪ (π[3] (σ[(#1 = "c" ∧ #0 = #2)] ((Vb × Vc))) ∪ π[0] (Vb))))
ELSE
SKIP
END
END
-/
#guard_msgs (whitespace := lax) in
#eval DBTPretty.display ("\n" ++ inputPreproc.loopCmd.pretty)

end Example4037

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel
