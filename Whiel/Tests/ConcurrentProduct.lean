import Whiel.DatalogCompiler.NaiveConcurrentProduct
import Whiel.Cmd.PrettyPrint
import Whiel.Concrete.Notation

------------------------------------------------------------
-- Example Datalog Sources
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace ConcurrentProduct

open Whiel.Concrete
open Whiel.ConcurrentProduct
open Datalog.WhielCompiler

def Base : IndexAlphaName :=
  IndexAlphaName.baseString "Base"

def LAcc : IndexAlphaName :=
  IndexAlphaName.baseString "LAcc"

def RAcc : IndexAlphaName :=
  IndexAlphaName.baseString "RAcc"

def leftSchema : UnnamedSchema IndexAlphaName :=
  whielSch![
    {Base, LAcc} (arity: 2),
    _ (arity: 0)
  ]

def rightSchema : UnnamedSchema IndexAlphaName :=
  whielSch![
    {Base, RAcc} (arity: 2),
    _ (arity: 0)
  ]

def leftDatalogProgram :
    Datalog.Program Data leftSchema :=
  datalog![
    LAcc(x1, y1) :- Base(x1, y1);
    LAcc(x1, z1) :-
      LAcc(x1, y1), Base(y1, z1);
  ]

def rightDatalogProgram :
    Datalog.Program Data rightSchema :=
  datalog![
    RAcc(x1, y1) :- Base(x1, y1);
    RAcc(x1, z1) :-
      Base(x1, y1), RAcc(y1, z1);
  ]

end ConcurrentProduct

end Tests

end Whiel

------------------------------------------------------------
-- Manual Naive-Compiler Outputs
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace ConcurrentProduct

open Whiel.Concrete
open Datalog.WhielCompiler

abbrev leftCompiledSchema :
    UnnamedSchema IndexAlphaName :=
  Naive.execSchema leftDatalogProgram

abbrev rightCompiledSchema :
    UnnamedSchema IndexAlphaName :=
  Naive.execSchema rightDatalogProgram

/- The left program after naive compilation and before
  concurrent-product rewriting. -/
def manualLeftCompiledCommand :
    Cmd Data leftCompiledSchema :=
  whielCmd![
    { ExecSchema: leftCompiledSchema }
    {
      LAcc_2 := ∅;
      LAcc :=
        Base ∪
          (π[0, 3]
            (σ[#1 = #2] (LAcc_2 × Base)));
      WHILE LAcc ≠ LAcc_2 DO
        LAcc_2 := LAcc;
        LAcc :=
          LAcc ∪
            (Base ∪
              (π[0, 3]
                (σ[#1 = #2] (LAcc_2 × Base))))
      END
    }
  ]

/- The right program after naive compilation and before
  concurrent-product rewriting. -/
def manualRightCompiledCommand :
    Cmd Data rightCompiledSchema :=
  whielCmd![
    { ExecSchema: rightCompiledSchema }
    {
      RAcc_2 := ∅;
      RAcc :=
        Base ∪
          (π[0, 3]
            (σ[#1 = #2] (Base × RAcc_2)));
      WHILE RAcc ≠ RAcc_2 DO
        RAcc_2 := RAcc;
        RAcc :=
          RAcc ∪
            (Base ∪
              (π[0, 3]
                (σ[#1 = #2] (Base × RAcc_2))))
      END
    }
  ]

theorem leftCompiledCommand_eq_manual :
    leftDatalogProgram.toWhielCmd =
      manualLeftCompiledCommand := by
  apply Cmd.eq_of_toRaw_eq
  decide +kernel

theorem rightCompiledCommand_eq_manual :
    rightDatalogProgram.toWhielCmd =
      manualRightCompiledCommand := by
  apply Cmd.eq_of_toRaw_eq
  decide +kernel

def manualLeftCompiledProgram :
    Whiel.Program Data leftDatalogProgram.edbSchema
      leftSchema where
  execSchema := leftCompiledSchema
  extendsInput :=
    Naive.execSchema_extension_input leftDatalogProgram
  extendsOutput :=
    Naive.execSchema_extension_output leftDatalogProgram
  cmd := manualLeftCompiledCommand

def manualRightCompiledProgram :
    Whiel.Program Data rightDatalogProgram.edbSchema
      rightSchema where
  execSchema := rightCompiledSchema
  extendsInput :=
    Naive.execSchema_extension_input rightDatalogProgram
  extendsOutput :=
    Naive.execSchema_extension_output rightDatalogProgram
  cmd := manualRightCompiledCommand

theorem leftCompiledProgram_eq_manual :
    leftDatalogProgram.toWhielProgram =
      manualLeftCompiledProgram := by
  unfold Datalog.Program.toWhielProgram
    manualLeftCompiledProgram
  congr
  exact leftCompiledCommand_eq_manual

theorem rightCompiledProgram_eq_manual :
    rightDatalogProgram.toWhielProgram =
      manualRightCompiledProgram := by
  unfold Datalog.Program.toWhielProgram
    manualRightCompiledProgram
  congr
  exact rightCompiledCommand_eq_manual

end ConcurrentProduct

end Tests

end Whiel

------------------------------------------------------------
-- Certified Example Components
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace ConcurrentProduct

open Whiel.Concrete
open Whiel.ConcurrentProduct
open Datalog.WhielCompiler

def leftComponent :=
  Naive.concurrentComponent leftDatalogProgram

def rightComponent :=
  Naive.concurrentComponent rightDatalogProgram

/- The two generated snapshot/live write sets are disjoint,
  while `Base` is a common read-only input. -/
def independent :
    Independent leftComponent rightComponent := by
  constructor <;> decide

theorem base_is_shared_input :
    Base ∈ leftComponent.inputSchema.syms ∩
      rightComponent.inputSchema.syms := by
  decide

theorem generated_writes_are_disjoint :
    leftComponent.writes ∩ rightComponent.writes = ∅ :=
  Independent.disjoint_writes independent

/- This is the certificate used in an asymmetric round
  after the left compiler has already converged. -/
theorem left_body_stutters_after_convergence
    {J : Instance Data leftComponent.program.execSchema}
    (hInv : leftComponent.invariant J)
    (hDone : ¬ leftComponent.guard.eval J) :
    Cmd.BigStep leftComponent.body J J :=
  leftComponent.body_stutter hInv hDone

end ConcurrentProduct

end Tests

end Whiel

------------------------------------------------------------
-- Concurrent Product Construction
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace ConcurrentProduct

open Whiel.Concrete
open Whiel.ConcurrentProduct

def computedComponent :=
  product leftComponent rightComponent independent

abbrev productSchema : UnnamedSchema IndexAlphaName :=
  productExecSchema leftComponent rightComponent independent

def computedCommand :
    Cmd Data productSchema :=
  computedComponent.program.cmd

/- Remove administrative sequencing skips for display. -/
def displayedCommand := computedCommand.clean

end ConcurrentProduct

end Tests

end Whiel

------------------------------------------------------------
-- Manual Product Syntax
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace ConcurrentProduct

open Whiel.Concrete

/- The product written directly in user-facing notation. -/
def manualCommand : Cmd Data productSchema :=
  whielCmd![
    { ExecSchema: productSchema }
    {
      LAcc_2 := ∅;
      LAcc :=
        Base ∪
          (π[0, 3]
            (σ[#1 = #2] (LAcc_2 × Base)));
      RAcc_2 := ∅;
      RAcc :=
        Base ∪
          (π[0, 3]
            (σ[#1 = #2] (Base × RAcc_2)));
      WHILE
          (LAcc ≠ LAcc_2) ∨ (RAcc ≠ RAcc_2) DO
        LAcc_2 := LAcc;
        LAcc :=
          LAcc ∪
            (Base ∪
              (π[0, 3]
                (σ[#1 = #2] (LAcc_2 × Base))));
        RAcc_2 := RAcc;
        RAcc :=
          RAcc ∪
            (Base ∪
              (π[0, 3]
                (σ[#1 = #2] (Base × RAcc_2))))
      END
    }
  ]

/- The cleaned computed syntax is propositionally equal to
  the directly written command. -/
theorem displayedCommand_eq_manual :
    displayedCommand = manualCommand := by
  apply Cmd.eq_of_toRaw_eq
  decide +kernel

theorem displayedPretty_eq_manualPretty :
    displayedCommand.pretty = manualCommand.pretty := by
  rw [displayedCommand_eq_manual]

theorem manualCommand_equiv :
    Cmd.BigStepEquiv manualCommand computedCommand := by
  rw [← displayedCommand_eq_manual]
  intro I J
  exact Cmd.bigStep_clean_iff computedCommand I J

end ConcurrentProduct

end Tests

end Whiel

------------------------------------------------------------
-- Product Correctness Checks
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace ConcurrentProduct

open Whiel.Concrete
open Whiel.ConcurrentProduct

/- The computed result has exactly one while command. -/
theorem computed_has_one_while :
    computedCommand.whileCount = 1 :=
  productCommand_whileCount
    leftComponent rightComponent independent

/- The instantiated semantic product theorem type-checks. -/
theorem computed_bigStep_spec
    {I : Instance Data
      (productInputSchema leftComponent rightComponent
        independent)}
    {K : Instance Data
      (productOutputSchema leftComponent rightComponent
        independent)} :
    computedComponent.program.BigStep I K ↔
      leftComponent.program.BigStep
          (Instance.reduct
            (productInputSchema_extension_left
              leftComponent rightComponent independent) I)
          (Instance.reduct
            (productOutputSchema_extension_left
              leftComponent rightComponent
              independent) K) ∧
        rightComponent.program.BigStep
          (Instance.reduct
            (productInputSchema_extension_right
              leftComponent rightComponent independent) I)
          (Instance.reduct
            (productOutputSchema_extension_right
              leftComponent rightComponent
              independent) K) := by
  exact product_bigStep_iff
    leftComponent rightComponent independent

theorem displayedCommand_equiv :
    Cmd.BigStepEquiv displayedCommand computedCommand := by
  intro I J
  exact Cmd.bigStep_clean_iff computedCommand I J

#eval manualCommand.display

end ConcurrentProduct

end Tests

end Whiel
