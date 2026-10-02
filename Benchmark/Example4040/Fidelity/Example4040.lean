-- Author: Jesse Comer
import Benchmark.Example4040.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

/-
  Fidelity of `Benchmark/Example4040/Input.lean` to its
  source Datalog programs.

  The views are themselves Datalog, so they are not free
  source tables: they are computed from the coloured edges,
  and the reformulation is a program over them. The three
  Datalog programs below are the global closure, the two
  monochrome path views, and that reformulation.

  Compiling each program with the naive compiler and
  writing the results one after the other, with the
  generated snapshots renamed to auxiliary input names,
  reproduces the input file's command exactly, so the
  encoding is faithful by construction rather than by
  inspection. The single loop the tool verifies is
  computed from that sequence by the generic
  preprocessor and is pinned at the end of this module.

  The reformulation reads relations the program before
  it computes, so the merge is the two-phase one and the
  pinned loop carries the flags it draws.
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

namespace Example4040

open Whiel.Concrete

def R : ProgramNames :=
  .programSymbol ⟨"R", by decide⟩ 0

def B : ProgramNames :=
  .programSymbol ⟨"B", by decide⟩ 0

def T : ProgramNames :=
  .programSymbol ⟨"T", by decide⟩ 0

def Vr : ProgramNames :=
  .programSymbol ⟨"Vr", by decide⟩ 0

def Vb : ProgramNames :=
  .programSymbol ⟨"Vb", by decide⟩ 0

def TUp : ProgramNames :=
  .programSymbol ⟨"TUp", by decide⟩ 0

/- The global schema and its closure output. -/
def globalSchema : UnnamedSchema ProgramNames :=
  programSch![
    {R, B, T} (arity: 2)
  ]

/- The schema the two path views are computed over. -/
def viewSchema : UnnamedSchema ProgramNames :=
  programSch![
    {R, B, Vr, Vb} (arity: 2)
  ]

/- The local schema and the reformulation's output. -/
def reformSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Vr, Vb, TUp} (arity: 2)
  ]

/- The transitive closure of `R ∪ B`, left-linearly. -/
def globalProgram : Datalog.Program Data globalSchema :=
  datalog![
    T(x1, y1) :- R(x1, y1);
    T(x1, y1) :- B(x1, y1);
    T(x1, y1) :- R(x1, z1), T(z1, y1);
    T(x1, y1) :- B(x1, z1), T(z1, y1);
  ]

/- The red and the blue monochrome path views. -/
def viewProgram : Datalog.Program Data viewSchema :=
  datalog![
    Vr(x1, y1) :- R(x1, y1);
    Vr(x1, y1) :- R(x1, z1), Vr(z1, y1);
    Vb(x1, y1) :- B(x1, y1);
    Vb(x1, y1) :- B(x1, z1), Vb(z1, y1);
  ]

/- The reformulation over the two path views. -/
def reformProgram : Datalog.Program Data reformSchema :=
  datalog![
    TUp(x1, y1) :- Vr(x1, y1);
    TUp(x1, y1) :- Vb(x1, y1);
    TUp(x1, y1) :- TUp(x1, z1), TUp(z1, y1);
  ]

end Example4040

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

namespace Example4040

open Whiel.Concrete

/- The compiled global program, in input names. -/
def globalRaw : RawCmd ProgramNames Data :=
  mapCmd toRawInput globalProgram.toWhielCmd.toRaw

/- The compiled view program, in input names. -/
def viewRaw : RawCmd ProgramNames Data :=
  mapCmd toRawInput viewProgram.toWhielCmd.toRaw

/- The compiled reformulation, in input names. -/
def reformRaw : RawCmd ProgramNames Data :=
  mapCmd toRawInput reformProgram.toWhielCmd.toRaw

/- The reduction: the three compiled programs in sequence. -/
def compiledRaw : RawCmd ProgramNames Data :=
  seqAfter globalRaw (seqAfter viewRaw reformRaw)

end Example4040

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

namespace Example4040

open Whiel.Concrete

open Whiel.Benchmark.Example4040
  (inputSchema inputPre inputCmd inputPost)

/- Task 9 states no view hypothesis. -/
def viewConstraintRaw : RawGuard ProgramNames Data :=
  .«true»

/- The claim `T = T↑`. -/
def claimRaw : RawGuard ProgramNames Data :=
  .eq (.rel T) (.rel TUp)

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

end Example4040

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Split-Halves Regression Guard
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

namespace Example4040

open Whiel.Concrete

/-
  The reference encoding of the `TUp ⊆ T` half, with the
  derived nonlinear rule added so that the global frontier
  doubles per iteration. Its least fixpoint is still the
  transitive closure of `R ∪ B`.
-/
def derivedRuleProgram :
    Datalog.Program Data globalSchema :=
  datalog![
    T(x1, y1) :- R(x1, y1);
    T(x1, y1) :- B(x1, y1);
    T(x1, y1) :- R(x1, z1), T(z1, y1);
    T(x1, y1) :- B(x1, z1), T(z1, y1);
    T(x1, y1) :- T(x1, z1), T(z1, y1);
  ]

/-
  A two-step `T` with no edges at all: the PDF's rules all
  read `R` or `B`, so only the derived rule can fire.
-/
def strandedWalks : Instance Data globalSchema :=
  Instance.update (Instance.empty globalSchema)
    (globalSchema.sym T)
    (Notation.relationFromRows 2
      [[Data.num 0, Data.num 1],
       [Data.num 1, Data.num 2]])

/-
  One immediate-consequence step separates the two: the
  verbatim program is already at a fixed point here, while
  the derived rule composes the two walks and adds `(0, 2)`.
-/
theorem derivedRule_differs_after_one_step :
    (globalProgram.immediate strandedWalks)
        (globalSchema.sym T) ≠
      (derivedRuleProgram.immediate strandedWalks)
        (globalSchema.sym T) := by
  decide +kernel

end Example4040

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

namespace Example4040

open Whiel.Benchmark.Example4040 (inputPreproc)

/-
  The single loop the generic preprocessor computes
  from the sequence above. It is what the tool verifies,
  so it is pinned here rather than only displayed.
-/
/-- info:
WHILE ((¬((T = T_aux))) ∨ ((flag_0_0 = ⊤) ∨ (flag_1_0 = ⊤))) DO
IF (¬((T = T_aux))) THEN
T_aux := T;
T := (T ∪ (R ∪ (B ∪ (π[0,3] (σ[#1 = #2] ((R × T_aux))) ∪ π[0,3] (σ[#1 = #2] ((B × T_aux)))))))
ELSE
SKIP
END;
IF ((flag_0_0 = ⊤) ∨ (flag_1_0 = ⊤)) THEN
IF (flag_0_0 = ⊤) THEN
IF (¬(((Vr = Vr_aux) ∧ (Vb = Vb_aux)))) THEN
Vr_aux := Vr;
Vb_aux := Vb;
Vr := (Vr ∪ (R ∪ π[0,3] (σ[#1 = #2] ((R × Vr_aux)))));
Vb := (Vb ∪ (B ∪ π[0,3] (σ[#1 = #2] ((B × Vb_aux)))))
ELSE
flag_0_0 := ∅[0];
flag_1_0 := ⊤;
TUp_aux := ∅[2];
TUp := (Vr ∪ (Vb ∪ π[0,3] (σ[#1 = #2] ((TUp_aux × TUp_aux)))))
END
ELSE
IF (¬((TUp = TUp_aux))) THEN
TUp_aux := TUp;
TUp := (TUp ∪ (Vr ∪ (Vb ∪ π[0,3] (σ[#1 = #2] ((TUp_aux × TUp_aux))))))
ELSE
flag_1_0 := ∅[0]
END
END
ELSE
SKIP
END
END
-/
#guard_msgs (whitespace := lax) in
#eval DBTPretty.display ("\n" ++ inputPreproc.loopCmd.pretty)

end Example4040

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel
