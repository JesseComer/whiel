-- Author: Jesse Comer
import Whiel.Eval.Cmd.Fast
import Whiel.Concrete.Notation

/-
  Synthetic workloads for evaluator benchmarking.

  These examples isolate relational and command costs that
  are entangled in the generated Benchmark001 programs.
-/

------------------------------------------------------------
-- Shared Workload Representation
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace EvaluatorWorkloads

open Whiel.Concrete

structure Workload where
  schema : UnnamedSchema IndexAlphaName
  command : Cmd Data schema
  makeInput : Unit → FastInstance Data schema
  inputTuples : Nat
  inputNames : List String
  outputNames : List String
  inputProbeName : String
  outputProbeName : String
  inputProbe : schema.syms
  outputProbe : schema.syms
  shape : String
  outputNonempty : Bool
  expectedOutputSizes : String := ""

def name : String → IndexAlphaName
| "EA" => IndexAlphaName.baseString "EA"
| "EB" => IndexAlphaName.baseString "EB"
| "EC" => IndexAlphaName.baseString "EC"
| "L" => IndexAlphaName.baseString "L"
| "R" => IndexAlphaName.baseString "R"
| "O" => IndexAlphaName.baseString "O"
| "SA" => IndexAlphaName.baseString "SA"
| "SB" => IndexAlphaName.baseString "SB"
| "SC" => IndexAlphaName.baseString "SC"
| "TA" => IndexAlphaName.baseString "TA"
| "TB" => IndexAlphaName.baseString "TB"
| "TC" => IndexAlphaName.baseString "TC"
| _ => IndexAlphaName.baseString "Unknown"

def schemaSym
    (Γ : UnnamedSchema IndexAlphaName)
    (s : String)
    (h : name s ∈ Γ.syms) :
    Γ.syms :=
  Γ.sym (name s) h

def d (n : Nat) : Data :=
  Data.num n

def tup2 (x y : Nat) : Tuple Data 2 :=
  Vector.ofFn (fun i =>
    if i.1 = 0 then d x else d y)

def tup4
    (a b c e : Nat) : Tuple Data 4 :=
  Vector.ofFn (fun i =>
    if i.1 = 0 then d a
    else if i.1 = 1 then d b
    else if i.1 = 2 then d c
    else d e)

def rel2
    (xs : List (Nat × Nat)) :
    FastRelation Data 2 :=
  FastRelation.ofList
    (xs.map (fun p => tup2 p.1 p.2))

def rel4
    (xs : List (Nat × Nat × Nat × Nat)) :
    FastRelation Data 4 :=
  FastRelation.ofList
    (xs.map (fun p =>
      tup4 p.1 p.2.1 p.2.2.1 p.2.2.2))

def emptyFast
    (Γ : UnnamedSchema IndexAlphaName) :
    FastInstance Data Γ where
  relation := fun X =>
    FastRelation.empty (Γ.arity X)

def setRel
    {Γ : UnnamedSchema IndexAlphaName}
    {arity : Nat}
    (S : FastInstance Data Γ)
    (X : Γ.syms)
    (R : FastRelation Data arity)
    (h : arity = Γ.arity X) :
    FastInstance Data Γ :=
  S.update X (FastRelation.castArity h R)

def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).map (fun i => (i, i))

end EvaluatorWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Binary Join Workloads
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace EvaluatorWorkloads

open Whiel.Concrete

def binarySchema : UnnamedSchema IndexAlphaName :=
  whielSch![
    {L, R, O} (arity: 2),
    _ (arity: 0)
  ]

def binaryL : binarySchema.syms :=
  schemaSym binarySchema "L" (by native_decide)

def binaryR : binarySchema.syms :=
  schemaSym binarySchema "R" (by native_decide)

def binaryO : binarySchema.syms :=
  schemaSym binarySchema "O" (by native_decide)

def disjointRight
    (n : Nat) : List (Nat × Nat) :=
  (List.range n).map (fun i => (n + i, i))

def disjointJoinCmd : Cmd Data binarySchema :=
  whielCmd![
    { ExecSchema: binarySchema }
    { O := π[0, 3] (σ[#1 = #2] (L × R)) }
  ]

def binaryInput
    (left right : List (Nat × Nat)) :
    FastInstance Data binarySchema :=
  setRel
    (setRel (emptyFast binarySchema)
      binaryL (rel2 left) (by native_decide))
    binaryR (rel2 right) (by native_decide)

def disjointJoin (n : Nat) : Workload where
  schema := binarySchema
  command := disjointJoinCmd
  makeInput := fun _ =>
    binaryInput (pairs n) (disjointRight n)
  inputTuples := 2 * n
  inputNames := ["L", "R"]
  outputNames := ["O"]
  inputProbeName := "L"
  outputProbeName := "O"
  inputProbe := binaryL
  outputProbe := binaryO
  shape := "join-disjoint"
  outputNonempty := Bool.false

/- A one-to-one equijoin with one output per input. -/
def oneToOneJoin (n : Nat) : Workload where
  schema := binarySchema
  command := disjointJoinCmd
  makeInput := fun _ =>
    binaryInput (pairs n) (pairs n)
  inputTuples := 2 * n
  inputNames := ["L", "R"]
  outputNames := ["O"]
  inputProbeName := "L"
  outputProbeName := "O"
  inputProbe := binaryL
  outputProbe := binaryO
  shape := "join-one-to-one"
  outputNonempty := decide (n > 0)

end EvaluatorWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Skewed Projection Workload
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace EvaluatorWorkloads

open Whiel.Concrete

def skewSchema : UnnamedSchema IndexAlphaName :=
  whielSch![
    {L, R} (arity: 2),
    O (arity: 1),
    _ (arity: 0)
  ]

def skewL : skewSchema.syms :=
  schemaSym skewSchema "L" (by native_decide)

def skewR : skewSchema.syms :=
  schemaSym skewSchema "R" (by native_decide)

def skewO : skewSchema.syms :=
  schemaSym skewSchema "O" (by native_decide)

def skewLeft
    (n : Nat) : List (Nat × Nat) :=
  (List.range n).map (fun i => (i, 0))

def skewRight
    (n : Nat) : List (Nat × Nat) :=
  (List.range n).map (fun i => (0, i))

def skewJoinCmd : Cmd Data skewSchema :=
  whielCmd![
    { ExecSchema: skewSchema }
    { O := π[1] (σ[#1 = #2] (L × R)) }
  ]

def skewInput (n : Nat) : FastInstance Data skewSchema :=
  setRel
    (setRel (emptyFast skewSchema)
      skewL (rel2 (skewLeft n)) (by native_decide))
    skewR (rel2 (skewRight n)) (by native_decide)

def skewJoin (n : Nat) : Workload where
  schema := skewSchema
  command := skewJoinCmd
  makeInput := fun _ => skewInput n
  inputTuples := 2 * n
  inputNames := ["L", "R"]
  outputNames := ["O"]
  inputProbeName := "L"
  outputProbeName := "O"
  inputProbe := skewL
  outputProbe := skewO
  shape := "join-skew-collapse"
  outputNonempty := Bool.true

end EvaluatorWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Wide Tuple Join Workload
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace EvaluatorWorkloads

open Whiel.Concrete

def wideSchema : UnnamedSchema IndexAlphaName :=
  whielSch![
    {L, R} (arity: 4),
    O (arity: 2),
    _ (arity: 0)
  ]

def wideL : wideSchema.syms :=
  schemaSym wideSchema "L" (by native_decide)

def wideR : wideSchema.syms :=
  schemaSym wideSchema "R" (by native_decide)

def wideO : wideSchema.syms :=
  schemaSym wideSchema "O" (by native_decide)

def wideLeft
    (n : Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range n).map (fun i => (i, 0, 0, i))

def wideRight
    (n : Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range n).map (fun i => (n + i, 0, 0, i))

def wideJoinCmd : Cmd Data wideSchema :=
  whielCmd![
    { ExecSchema: wideSchema }
    { O := π[0, 7] (σ[#3 = #4] (L × R)) }
  ]

def wideInput (n : Nat) : FastInstance Data wideSchema :=
  setRel
    (setRel (emptyFast wideSchema)
      wideL (rel4 (wideLeft n)) (by native_decide))
    wideR (rel4 (wideRight n)) (by native_decide)

def wideJoin (n : Nat) : Workload where
  schema := wideSchema
  command := wideJoinCmd
  makeInput := fun _ => wideInput n
  inputTuples := 2 * n
  inputNames := ["L", "R"]
  outputNames := ["O"]
  inputProbeName := "L"
  outputProbeName := "O"
  inputProbe := wideL
  outputProbe := wideO
  shape := "join-wide-disjoint"
  outputNonempty := Bool.false

end EvaluatorWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Difference and Guard Controls
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace EvaluatorWorkloads

open Whiel.Concrete

def overlapPairs
    (n : Nat) : List (Nat × Nat) :=
  pairs (n / 2)

def diffCmd : Cmd Data binarySchema :=
  whielCmd![
    { ExecSchema: binarySchema }
    { O := L ∖ R }
  ]

def diffWorkload (n : Nat) : Workload where
  schema := binarySchema
  command := diffCmd
  makeInput := fun _ =>
    binaryInput (pairs n) (overlapPairs n)
  inputTuples := n + n / 2
  inputNames := ["L", "R"]
  outputNames := ["O"]
  inputProbeName := "L"
  outputProbeName := "O"
  inputProbe := binaryL
  outputProbe := binaryO
  shape := "difference-overlap"
  outputNonempty := decide (n > 1)

def equalGuardCmd : Cmd Data binarySchema :=
  whielCmd![
    { ExecSchema: binarySchema }
    {
      IF L = R THEN
        O := L
      ELSE
        O := R
      END
    }
  ]

def equalGuard (n : Nat) : Workload where
  schema := binarySchema
  command := equalGuardCmd
  makeInput := fun _ =>
    binaryInput (pairs n) (pairs n)
  inputTuples := 2 * n
  inputNames := ["L", "R"]
  outputNames := ["O"]
  inputProbeName := "L"
  outputProbeName := "O"
  inputProbe := binaryL
  outputProbe := binaryO
  shape := "guard-equal"
  outputNonempty := decide (n > 0)

end EvaluatorWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Persistent State Update Workload
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace EvaluatorWorkloads

open Whiel.Concrete

def repeatedAssign : Nat → Cmd Data binarySchema
| 0 => .skip
| n + 1 =>
    .seq
      (.assign binaryO
        (RAExpr.rel (D := Data) binaryL))
      (repeatedAssign n)

def stateInput : FastInstance Data binarySchema :=
  setRel (emptyFast binarySchema)
    binaryL (rel2 (pairs 32)) (by native_decide)

def stateDepth (n : Nat) : Workload where
  schema := binarySchema
  command := repeatedAssign n
  makeInput := fun _ => stateInput
  inputTuples := 32
  inputNames := ["L"]
  outputNames := ["O"]
  inputProbeName := "L"
  outputProbeName := "O"
  inputProbe := binaryL
  outputProbe := binaryO
  shape := "state-depth"
  outputNonempty := decide (n > 0)

end EvaluatorWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Workload Lookup
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace EvaluatorWorkloads

open Whiel.Concrete

def find?
    (caseName : String)
    (n : Nat) : Option Workload :=
  match caseName with
  | "syn-join-disjoint" => some (disjointJoin n)
  | "syn-join-one-to-one" => some (oneToOneJoin n)
  | "syn-join-skew" => some (skewJoin n)
  | "syn-join-wide" => some (wideJoin n)
  | "syn-diff" => some (diffWorkload n)
  | "syn-guard-equal" => some (equalGuard n)
  | "syn-state-depth" => some (stateDepth n)
  | _ => none

end EvaluatorWorkloads

end CmdFast

end Tests

end Whiel
