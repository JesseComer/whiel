-- Author: Jesse Comer
import Whiel.Tests.CmdFast.EvaluatorWorkloads

/-
  Independent lockstep products of positive inflationary
  transitive-closure components for CexFast benchmarking.

  Every command initializes all components before one global
  loop. Each body runs unconditionally, so a stabilized
  component stutters while another component remains active.
-/

------------------------------------------------------------
-- Shared Product Representation
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace IndependentProductWorkloads

open Whiel.Concrete
open EvaluatorWorkloads

abbrev Workload := EvaluatorWorkloads.Workload

def productSchema : UnnamedSchema IndexAlphaName :=
  whielSch![
    {EA, EB, EC, SA, TA, SB, TB, SC, TC} (arity: 2),
    _ (arity: 0)
  ]

def ea : productSchema.syms :=
  schemaSym productSchema "EA" (by decide)

def eb : productSchema.syms :=
  schemaSym productSchema "EB" (by decide)

def ec : productSchema.syms :=
  schemaSym productSchema "EC" (by decide)

def ta : productSchema.syms :=
  schemaSym productSchema "TA" (by decide)

def closureSize (n : Nat) : Nat :=
  n * (n + 1) / 2

def chainPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).map (fun i => (i, i + 1))

def setChain
    (S : FastInstance Data productSchema)
    (X : productSchema.syms)
    (n : Nat)
    (h : 2 = productSchema.arity X) :
    FastInstance Data productSchema :=
  setRel S X (rel2 (chainPairs n)) h

def outputSizes2 (n : Nat) : String :=
  let c := toString (closureSize n)
  "SA=" ++ c ++ ";TA=" ++ c ++ ";SB=" ++ c ++
    ";TB=" ++ c

def outputSizes3 (n : Nat) : String :=
  let c := toString (closureSize n)
  "SA=" ++ c ++ ";TA=" ++ c ++ ";SB=" ++ c ++
    ";TB=" ++ c ++ ";SC=" ++ c ++ ";TC=" ++ c

def outputSizesAsymmetric (n : Nat) : String :=
  let a := toString (closureSize n)
  let b := toString (closureSize 4)
  "SA=" ++ a ++ ";TA=" ++ a ++ ";SB=" ++ b ++
    ";TB=" ++ b

end IndependentProductWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Product Commands
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace IndependentProductWorkloads

open Whiel.Concrete

/- Two independent components with separate chain EDBs. -/
def disjointCmd : Cmd Data productSchema :=
  whielCmd![
    { ExecSchema: productSchema }
    {
      SA := ∅;
      TA := EA ∪ (π[0, 3] (σ[#1 = #2] (SA × EA)));
      SB := ∅;
      TB := EB ∪ (π[0, 3] (σ[#1 = #2] (SB × EB)));
      WHILE (TA ≠ SA) ∨ (TB ≠ SB) DO
        SA := TA;
        TA := TA ∪
          (EA ∪ (π[0, 3] (σ[#1 = #2] (SA × EA))));
        SB := TB;
        TB := TB ∪
          (EB ∪ (π[0, 3] (σ[#1 = #2] (SB × EB))))
      END
    }
  ]

/- Two components sharing one read-only chain EDB. -/
def sharedCmd : Cmd Data productSchema :=
  whielCmd![
    { ExecSchema: productSchema }
    {
      SA := ∅;
      TA := EA ∪ (π[0, 3] (σ[#1 = #2] (SA × EA)));
      SB := ∅;
      TB := EA ∪ (π[0, 3] (σ[#1 = #2] (SB × EA)));
      WHILE (TA ≠ SA) ∨ (TB ≠ SB) DO
        SA := TA;
        TA := TA ∪
          (EA ∪ (π[0, 3] (σ[#1 = #2] (SA × EA))));
        SB := TB;
        TB := TB ∪
          (EA ∪ (π[0, 3] (σ[#1 = #2] (SB × EA))))
      END
    }
  ]

/- A long component paired with a fixed short component. -/
def asymmetricCmd : Cmd Data productSchema :=
  disjointCmd

/- Three independent components with separate chain EDBs. -/
def threeCmd : Cmd Data productSchema :=
  whielCmd![
    { ExecSchema: productSchema }
    {
      SA := ∅;
      TA := EA ∪ (π[0, 3] (σ[#1 = #2] (SA × EA)));
      SB := ∅;
      TB := EB ∪ (π[0, 3] (σ[#1 = #2] (SB × EB)));
      SC := ∅;
      TC := EC ∪ (π[0, 3] (σ[#1 = #2] (SC × EC)));
      WHILE (TA ≠ SA) ∨ ((TB ≠ SB) ∨ (TC ≠ SC)) DO
        SA := TA;
        TA := TA ∪
          (EA ∪ (π[0, 3] (σ[#1 = #2] (SA × EA))));
        SB := TB;
        TB := TB ∪
          (EB ∪ (π[0, 3] (σ[#1 = #2] (SB × EB))));
        SC := TC;
        TC := TC ∪
          (EC ∪ (π[0, 3] (σ[#1 = #2] (SC × EC))))
      END
    }
  ]

end IndependentProductWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Product Workload Families
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace IndependentProductWorkloads

open EvaluatorWorkloads

def disjointBalanced (n : Nat) : Workload where
  schema := productSchema
  command := disjointCmd
  makeInput := fun _ =>
    setChain
      (setChain (emptyFast productSchema) ea n
        (by decide))
      eb n (by decide)
  inputTuples := 2 * n
  inputNames := ["EA", "EB"]
  outputNames := ["SA", "TA", "SB", "TB"]
  inputProbeName := "EA"
  outputProbeName := "TA"
  inputProbe := ea
  outputProbe := ta
  shape := "product-disjoint-balanced"
  outputNonempty := decide (n > 0)
  expectedOutputSizes := outputSizes2 n

def sharedBalanced (n : Nat) : Workload where
  schema := productSchema
  command := sharedCmd
  makeInput := fun _ =>
    setChain (emptyFast productSchema) ea n
      (by decide)
  inputTuples := n
  inputNames := ["EA"]
  outputNames := ["SA", "TA", "SB", "TB"]
  inputProbeName := "EA"
  outputProbeName := "TA"
  inputProbe := ea
  outputProbe := ta
  shape := "product-shared-balanced"
  outputNonempty := decide (n > 0)
  expectedOutputSizes := outputSizes2 n

def asymmetric (n : Nat) : Workload where
  schema := productSchema
  command := asymmetricCmd
  makeInput := fun _ =>
    setChain
      (setChain (emptyFast productSchema) ea n
        (by decide))
      eb 4 (by decide)
  inputTuples := n + 4
  inputNames := ["EA", "EB"]
  outputNames := ["SA", "TA", "SB", "TB"]
  inputProbeName := "EA"
  outputProbeName := "TA"
  inputProbe := ea
  outputProbe := ta
  shape := "product-asymmetric"
  outputNonempty := decide (n > 0)
  expectedOutputSizes := outputSizesAsymmetric n

def three (n : Nat) : Workload where
  schema := productSchema
  command := threeCmd
  makeInput := fun _ =>
    setChain
      (setChain
        (setChain (emptyFast productSchema) ea n
          (by decide))
        eb n (by decide)) ec n (by decide)
  inputTuples := 3 * n
  inputNames := ["EA", "EB", "EC"]
  outputNames := ["SA", "TA", "SB", "TB", "SC", "TC"]
  inputProbeName := "EA"
  outputProbeName := "TA"
  inputProbe := ea
  outputProbe := ta
  shape := "product-three"
  outputNonempty := decide (n > 0)
  expectedOutputSizes := outputSizes3 n

def find? (caseName : String) (n : Nat) : Option Workload :=
  match caseName with
  | "product-disjoint-balanced" => some (disjointBalanced n)
  | "product-shared-balanced" => some (sharedBalanced n)
  | "product-asymmetric" => some (asymmetric n)
  | "product-three" => some (three n)
  | _ => none

end IndependentProductWorkloads

end CmdFast

end Tests

end Whiel
