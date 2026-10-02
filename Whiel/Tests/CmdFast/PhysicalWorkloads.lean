-- Author: Jesse Comer
import Batteries.Data.Array.Merge
import Databases.Core.FinRelation
import Std.Data.HashMap
import Std.Data.HashSet
import Whiel.Eval.RA.Normalize

/-
  Controlled physical-operator measurements for the fast
  Whiel evaluator.  These workloads select no production
  representation.  They provide evidence for later passes.
-/

------------------------------------------------------------
-- Physical Workload Interface
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace PhysicalWorkloads

structure Sample where
  inputNs : Nat
  evalNs : Nat
  inputChecksum : Nat
  outputChecksum : Nat
  outputSizes : String

structure Workload where
  name : String
  shape : String
  n : Nat
  inputTuples : Nat
  expectedDistinct : Nat
  expectedCandidates : Nat
  expectedChecksum : Nat
  measure : Unit → IO Sample

@[noinline] def forceNatIO : Nat → IO Nat
| 0 => pure 0
| n + 1 => pure (n + 1)

def forceResult
    (result : Nat × String) : IO (Nat × String) := do
  let check ← forceNatIO result.1
  let _ ← forceNatIO result.2.length
  pure (check, result.2)

def measure
    {α : Type}
    (mkInput : Unit → α)
    (inputChecksum : α → Nat)
    (evaluate : α → Nat × String) : IO Sample := do
  let inputStart ← IO.monoNanosNow
  let input := mkInput ()
  let inputCheck := inputChecksum input
  let inputStop ← IO.monoNanosNow
  let evalStart ← IO.monoNanosNow
  let output ← forceResult (evaluate input)
  let evalStop ← IO.monoNanosNow
  pure
    { inputNs := inputStop - inputStart
      evalNs := evalStop - evalStart
      inputChecksum := inputCheck
      outputChecksum := output.1
      outputSizes := output.2 }

def resultSummary
    (distinct candidates : Nat) : String :=
  "distinct=" ++ toString distinct ++
    ";candidates=" ++ toString candidates

def validate
    (workload : Workload)
    (sample : Sample) : IO Sample := do
  if sample.outputChecksum != workload.expectedChecksum then
    throw <| IO.userError
      ("physical checksum mismatch for " ++ workload.name)
  let expected := resultSummary workload.expectedDistinct
    workload.expectedCandidates
  if sample.outputSizes != expected then
    throw <| IO.userError
      ("physical result mismatch for " ++ workload.name)
  pure sample

end PhysicalWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Container Workloads
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace PhysicalWorkloads

def sumList (xs : List Nat) : Nat :=
  xs.foldl (fun total x => total + x) 0

def sumArray (xs : Array Nat) : Nat :=
  xs.foldl (fun total x => total + x) 0

def containerList (n : Nat) : Workload where
  name := "phys-container-list"
  shape := "list-build-traverse"
  n
  inputTuples := n
  expectedDistinct := n
  expectedCandidates := n
  expectedChecksum := n * (n - 1) / 2
  measure := fun _ => measure
    (fun _ => n)
    (fun size => size)
    (fun size =>
      let xs := List.range size
      (sumList xs, resultSummary size size))

def containerArray (n : Nat) : Workload where
  name := "phys-container-array"
  shape := "array-build-traverse"
  n
  inputTuples := n
  expectedDistinct := n
  expectedCandidates := n
  expectedChecksum := n * (n - 1) / 2
  measure := fun _ => measure
    (fun _ => n)
    (fun size => size)
    (fun size =>
      let xs := (List.range size).foldl
        (fun acc x => acc.push x) #[]
      (sumArray xs, resultSummary size size))

def retainedPrefixes (n : Nat) : List (Array Nat) :=
  (List.range n).foldl
    (fun versions x =>
      match versions with
      | [] => [#[x]]
      | current :: _ =>
          let next := current.push x
          next :: versions)
    []

def sharedArray (n : Nat) : Workload where
  name := "phys-shared-array"
  shape := "retained-prefixes"
  n
  inputTuples := n
  expectedDistinct := n
  expectedCandidates := n * (n + 1) / 2
  expectedChecksum := n * (n + 1) / 2
  measure := fun _ => measure
    (fun _ => n)
    (fun size => size)
    (fun size =>
      let versions := retainedPrefixes size
      let total := versions.foldl
        (fun acc xs => acc + xs.size) 0
      (total, resultSummary size total))

end PhysicalWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Normalization Workloads
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace PhysicalWorkloads

def natTuple (arity value : Nat) : Tuple Nat arity :=
  Vector.ofFn (fun i => value + i.1)

def normalizationInput
    (duplicate : Bool)
    (n : Nat) : List (Tuple Nat 2) :=
  (List.range n).reverse.map (fun i =>
    natTuple 2 (if duplicate then i / 16 else i))

def expectedDistinct (duplicate : Bool) (n : Nat) : Nat :=
  if duplicate then (n + 15) / 16 else n

def normalizeCurrent
    (xs : List (Tuple Nat 2)) : Nat :=
  (Tuple.sortDedup xs).length

def normalizeAdjacent
    (xs : List (Tuple Nat 2)) : Nat :=
  (TupleNormalize.normalize xs).length

def normalizeArray
    (xs : List (Tuple Nat 2)) : Nat :=
  xs.toArray.sortDedup.size

def normalizeHash
    (xs : List (Tuple Nat 2)) : Nat :=
  let set := xs.foldl
    (fun set x =>
      if set.contains x then set else set.insert x)
    (∅ : Std.HashSet (Tuple Nat 2))
  set.size

def normalization
    (variant : String)
    (duplicate : Bool)
    (n : Nat) : Workload :=
  let distinct := expectedDistinct duplicate n
  let shape :=
    if duplicate then "sixteen-per-distinct"
    else "reverse-unique"
  let run : List (Tuple Nat 2) → Nat :=
    match variant with
    | "current" => normalizeCurrent
    | "adjacent" => normalizeAdjacent
    | "array" => normalizeArray
    | _ => normalizeHash
  { name := "phys-normalize-" ++ variant ++ "-" ++
      (if duplicate then "duplicates" else "unique")
    shape
    n
    inputTuples := n
    expectedDistinct := distinct
    expectedCandidates := n
    expectedChecksum := distinct
    measure := fun _ => measure
      (fun _ => normalizationInput duplicate n)
      List.length
      (fun xs =>
        let count := run xs
        (count, resultSummary count n)) }

end PhysicalWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Index Workloads
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace PhysicalWorkloads

def indexInput
    (arity : Nat)
    (skewed : Bool)
    (n : Nat) : List (Tuple Nat arity) :=
  (List.range n).map (fun i =>
    natTuple arity (if skewed then i / 16 else i))

def wholeTupleIndex
    {arity : Nat}
    (xs : List (Tuple Nat arity)) : Nat × Nat :=
  let set := xs.foldl
    (fun set x => set.insert x)
    (∅ : Std.HashSet (Tuple Nat arity))
  let successful := xs.foldl
    (fun count x =>
      if set.contains x then count + 1 else count)
    0
  (xs.length, successful)

def columnIndex
    {arity : Nat}
    (h : 0 < arity)
    (xs : List (Tuple Nat arity)) : Nat × Nat :=
  let column : Fin arity := ⟨0, h⟩
  let index := xs.foldl
    (fun index x =>
      let key := x.get column
      let bucket := index.getD key []
      index.insert key (x :: bucket))
    (∅ : Std.HashMap Nat (List (Tuple Nat arity)))
  let keys := xs.foldl
    (fun keys x => keys.insert (x.get column))
    (∅ : Std.HashSet Nat)
  keys.toList.foldl
    (fun result key =>
      let candidates := (index.getD key []).length
      (result.1 + candidates, result.2 + 1))
    (0, 0)

def indexWorkload
    (variant : String)
    (arity : Nat)
    (skewed : Bool)
    (n : Nat)
    (hArity : 0 < arity) : Workload :=
  let shape := "arity-" ++ toString arity ++ "-" ++
    (if skewed then "sixteen-per-key" else "unique-keys")
  let distinct :=
    if skewed then (n + 15) / 16 else n
  let successful :=
    if variant = "whole" then n else distinct
  { name := "phys-index-" ++ variant ++ "-a" ++
      toString arity ++ "-" ++
      (if skewed then "skew" else "unique")
    shape
    n
    inputTuples := n
    expectedDistinct := distinct
    expectedCandidates := n
    expectedChecksum := n + successful
    measure := fun _ => measure
      (fun _ => indexInput arity skewed n)
      List.length
      (fun xs =>
        let result :=
          if variant = "whole" then wholeTupleIndex xs
          else columnIndex hArity xs
        (result.1 + result.2,
          resultSummary distinct result.1)) }

end PhysicalWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Machine-Word Workloads
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace PhysicalWorkloads

def wordArray
    {α : Type}
    [OfNat α 0]
    (convert : Nat → α)
    (toNat : α → Nat)
    (n : Nat) : Nat :=
  let xs := (List.range n).foldl
    (fun acc x => acc.push (convert x)) #[]
  xs.foldl (fun total x => total + toNat x) 0

def wordArrayWorkload
    (variant : String)
    (n : Nat) : Workload :=
  let run : Nat → Nat :=
    match variant with
    | "nat" => wordArray id id
    | "usize" => wordArray USize.ofNat USize.toNat
    | _ => wordArray UInt64.ofNat UInt64.toNat
  { name := "phys-word-array-" ++ variant
    shape := "array-build-scan"
    n
    inputTuples := n
    expectedDistinct := n
    expectedCandidates := n
    expectedChecksum := n * (n - 1) / 2
    measure := fun _ => measure
      (fun _ => n)
      id
      (fun size =>
        (run size, resultSummary size size)) }

def hashProbe
    {α : Type}
    [BEq α] [Hashable α]
    (convert : Nat → α)
    (n : Nat) : Nat :=
  let values := (List.range n).map convert
  let set := values.foldl
    (fun set x => set.insert x)
    (∅ : Std.HashSet α)
  values.foldl
    (fun count x =>
      if set.contains x then count + 1 else count)
    0

def wordHashWorkload
    (variant : String)
    (n : Nat) : Workload :=
  let run : Nat → Nat :=
    match variant with
    | "nat" => hashProbe id
    | "usize" => hashProbe USize.ofNat
    | _ => hashProbe UInt64.ofNat
  { name := "phys-word-hash-" ++ variant
    shape := "hash-build-probe"
    n
    inputTuples := n
    expectedDistinct := n
    expectedCandidates := n
    expectedChecksum := n
    measure := fun _ => measure
      (fun _ => n)
      id
      (fun size =>
        let count := run size
        (count, resultSummary size count)) }

end PhysicalWorkloads

end CmdFast

end Tests

end Whiel

------------------------------------------------------------
-- Physical Workload Registry
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace PhysicalWorkloads

def find? (name : String) (n : Nat) : Option Workload :=
  match name with
  | "phys-container-list" => some (containerList n)
  | "phys-container-array" => some (containerArray n)
  | "phys-shared-array" => some (sharedArray n)
  | "phys-normalize-current-unique" =>
      some (normalization "current" false n)
  | "phys-normalize-current-duplicates" =>
      some (normalization "current" true n)
  | "phys-normalize-adjacent-unique" =>
      some (normalization "adjacent" false n)
  | "phys-normalize-adjacent-duplicates" =>
      some (normalization "adjacent" true n)
  | "phys-normalize-array-unique" =>
      some (normalization "array" false n)
  | "phys-normalize-array-duplicates" =>
      some (normalization "array" true n)
  | "phys-normalize-hash-unique" =>
      some (normalization "hash" false n)
  | "phys-normalize-hash-duplicates" =>
      some (normalization "hash" true n)
  | "phys-index-whole-a2-unique" =>
      some (indexWorkload "whole" 2 false n (by omega))
  | "phys-index-whole-a2-skew" =>
      some (indexWorkload "whole" 2 true n (by omega))
  | "phys-index-whole-a4-unique" =>
      some (indexWorkload "whole" 4 false n (by omega))
  | "phys-index-whole-a4-skew" =>
      some (indexWorkload "whole" 4 true n (by omega))
  | "phys-index-column-a2-unique" =>
      some (indexWorkload "column" 2 false n (by omega))
  | "phys-index-column-a2-skew" =>
      some (indexWorkload "column" 2 true n (by omega))
  | "phys-index-column-a4-unique" =>
      some (indexWorkload "column" 4 false n (by omega))
  | "phys-index-column-a4-skew" =>
      some (indexWorkload "column" 4 true n (by omega))
  | "phys-word-array-nat" =>
      some (wordArrayWorkload "nat" n)
  | "phys-word-array-usize" =>
      some (wordArrayWorkload "usize" n)
  | "phys-word-array-uint64" =>
      some (wordArrayWorkload "uint64" n)
  | "phys-word-hash-nat" =>
      some (wordHashWorkload "nat" n)
  | "phys-word-hash-usize" =>
      some (wordHashWorkload "usize" n)
  | "phys-word-hash-uint64" =>
      some (wordHashWorkload "uint64" n)
  | _ => none

end PhysicalWorkloads

end CmdFast

end Tests

end Whiel
