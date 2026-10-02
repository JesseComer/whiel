import Databases.Datalog.OperationalSemantics
import Databases.UnnamedRA.Substitution
import Whiel.Cmd.Syntax
import Whiel.Cmd.Rewrites
import Whiel.DatalogCompiler.Common
import Whiel.RelationNames.NameSupply

/-
  This file defines the synchronous naive Datalog-to-Whiel
  translation.

  Each generated Whiel program uses one additional
  auxiliary `snapshot` relation symbol for each IDB symbol
  in the original Datalog program. The Whiel command first
  initializes each snapshot symbol to empty, then
  destructively assigns each live IDB symbol to an SPJU
  expression representing the immediate consequence
  operator for that IDB, with occurrences of the IDB
  symbol in the expression replaced with the snapshot
  symbol. Then, the program loops, with each iteration
  updating the snapshot symbols and taking the union of
  each IDB with the immediate consequence UCQ. The loop
  halts when each snapshot is equivalent to its
  corresponding IDB symbol's value.

  Key definitions include:
    * `Datalog.WhielCompiler.Naive.execSchema`
    * `Datalog.WhielCompiler.Naive.initialInstance`
    * `Datalog.WhielCompiler.Naive.reductToProgramSchema`
    * `Datalog.WhielCompiler.Naive.snapshotOf`
    * `Datalog.WhielCompiler.Naive.oldifiedConsequenceSPJU`
    * `Datalog.WhielCompiler.Naive.consequenceExpr`
    * `Datalog.Program.toWhielCmd`
    * `Datalog.Program.toWhielProgram`

  Final correctness theorems:
    * `WhielCompiler.Naive.toWhielCmd_bigStep_LFP_reduct`
    * `Program.toWhielProgram_bigStep_LFP`
    * `Program.toWhielProgram_bigStep_minimalModel`

  Intervening definitions and lemmas are computable
  construction and proof support.
-/

------------------------------------------------------------
-- IDB Lists and Fresh Snapshot Names
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- IDB symbols of a Datalog program. -/
abbrev IDBSym
    (P : Program D Γ) : Type :=
  P.IDBSym

/-
  IDB symbols in first-head-occurrence order, without
  duplicates.
-/
def idbList
    (P : Program D Γ) :
    List Γ.syms :=
  P.idbList

/- Membership in `idbList` gives membership in `P.idb`. -/
theorem idbList_mem_idb
    (P : Program D Γ)
    {X : Γ.syms}
    (hX : X ∈ idbList P) :
    X ∈ P.idb := by
  simpa [idbList] using P.idbList_mem_idb hX

/- IDB symbols as a list of typed IDB witnesses. -/
def idbSymList
    (P : Program D Γ) :
    List (IDBSym P) :=
  P.idbSymList

/- Raw IDB names in `idbList` order. -/
def idbNameList
    (P : Program D Γ) :
    List A :=
  (idbList P).map Subtype.val

/- IDB arities in `idbList` order. -/
def idbArityList
    (P : Program D Γ) :
    List Nat :=
  (idbList P).map Γ.arity

/- Fresh snapshot names, paired positionally with IDBs. -/
variable [Whiel.RelationNameSupply A]

def snapshotNames
    (P : Program D Γ) :
    List A :=
  Whiel.RelationNameSupply.freshNames
    (Γ).syms (idbNameList P)

/- `snapshotNames` has one generated name per IDB. -/
theorem snapshotNames_length
    (P : Program D Γ) :
    (snapshotNames P).length = (idbList P).length := by
  simp [snapshotNames, idbNameList,
    Whiel.RelationNameSupply.freshNames_length]

/- Snapshot names are fresh for the program schema. -/
theorem snapshotNames_fresh
    (P : Program D Γ)
    {X : A}
    (hX : X ∈ snapshotNames P) :
    X ∉ (Γ).syms :=
  Whiel.RelationNameSupply.freshNames_fresh hX

/- Snapshot names have no duplicates. -/
theorem snapshotNames_nodup
    (P : Program D Γ) :
    (snapshotNames P).Nodup :=
  Whiel.RelationNameSupply.freshNames_nodup
    (Γ).syms (idbNameList P)

/- IDB arities have one entry per IDB. -/
omit [Whiel.RelationNameSupply A] in
theorem idbArityList_length
    (P : Program D Γ) :
    (idbArityList P).length = (idbList P).length := by
  simp [idbArityList]

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Positional Arity Lookup
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A : Type}
variable [DecidableEq A]

/- Lookup an arity paired positionally with a name. -/
def pairLookup
    (Y : A) :
    List A → List Nat → Option Nat
| X :: Xs, n :: ns =>
    if Y = X then some n else pairLookup Y Xs ns
| _, _ => none

/-
  Positional lookup succeeds at every name-list position.
-/
theorem pairLookup_get
    {names : List A}
    {arities : List Nat}
    (hLen : names.length = arities.length)
    (hNoDup : names.Nodup)
    (i : Nat)
    (hiNames : i < names.length)
    (hiAr : i < arities.length) :
    pairLookup (names[i]) names arities =
      some arities[i] := by
  induction names generalizing arities i with
  | nil =>
      cases hiNames
  | cons X Xs ih =>
      cases arities with
      | nil =>
          simp at hLen
      | cons n ns =>
          cases i with
          | zero =>
              simp [pairLookup]
          | succ i =>
              have hLenTail : Xs.length = ns.length := by
                simpa using Nat.succ.inj hLen
              have hNoDupTail : Xs.Nodup := by
                simpa using hNoDup.tail
              have hiXs : i < Xs.length := by
                simpa using hiNames
              have hiNs : i < ns.length := by
                simpa using hiAr
              have hNe : Xs[i] ≠ X := by
                intro hEq
                have hMem : Xs[i] ∈ Xs :=
                  List.getElem_mem _
                have hNot : Xs[i] ∉ Xs := by
                  simpa [hEq] using hNoDup.notMem
                exact hNot hMem
              simp [pairLookup, hNe,
                ih hLenTail hNoDupTail i hiXs hiNs]

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Execution Schema
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Snapshot arity lookup for the generated names. -/
def snapshotArity?
    (P : Program D Γ)
    (Y : A) :
    Option Nat :=
  pairLookup Y (snapshotNames P) (idbArityList P)

/-
  Execution schema for true naive evaluation. It contains
  the program-schema symbols plus hidden snapshots.
-/
def execSchema
    (P : Program D Γ) :
    UnnamedSchema A where
  syms :=
    (Γ).syms ∪
      (snapshotNames P).toFinset
  arity := fun X =>
    if hOut : X.1 ∈ (Γ).syms then
      (Γ).arity ⟨X.1, hOut⟩
    else
      match snapshotArity? P X.1 with
      | some n => n
      | none => 0

/- The execution schema extends the program schema. -/
theorem execSchema_extension_output
    (P : Program D Γ) :
    (execSchema P).extensionOf (Γ) := by
  refine ⟨?_, ?_⟩
  · intro X hX
    exact Finset.mem_union.mpr (Or.inl hX)
  · intro X
    have hMem :
        X.1 ∈ (execSchema P).syms := by
      exact Finset.mem_union.mpr (Or.inl X.2)
    simp [execSchema, UnnamedSchema.arity?, X.2]

/- The execution schema extends the external input. -/
theorem execSchema_extension_input
    (P : Program D Γ) :
    (execSchema P).extensionOf P.edbSchema :=
  UnnamedSchema.extensionOf_trans
    (execSchema_extension_output P)
    (P.ambient_extension_edbSchema)

/-
  Initial execution instance for the command translation.
-/
def initialInstance
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance D (execSchema P) :=
  Instance.expandEmpty
    (execSchema_extension_input P) I

/- Reduct of an execution instance to the program schema. -/
instance instFact_execSchema_extension_output
    (P : Program D Γ) :
    Fact ((execSchema P).extensionOf Γ) :=
  ⟨execSchema_extension_output P⟩

def reductToProgramSchema
    (P : Program D Γ)
    [hOut : Fact ((execSchema P).extensionOf Γ)]
    (J : Instance D (execSchema P)) :
    Instance D Γ :=
  Instance.reduct hOut.out J

/- A program-schema symbol as an execution symbol. -/
def outputSym
    (P : Program D Γ)
    (X : (Γ).syms) :
    (execSchema P).syms :=
  ⟨X.1, (execSchema_extension_output P).1 X.2⟩

/-
  Program-symbol arity is unchanged in the execution schema.
-/
theorem outputSym_arity
    (P : Program D Γ)
    (X : (Γ).syms) :
    (execSchema P).arity (outputSym P X) =
      (Γ).arity X :=
  UnnamedSchema.arity_eq_of_extensionOf
    (execSchema_extension_output P) X

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- IDB and Snapshot Symbols
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- An IDB symbol appears in the program schema. -/
theorem idb_mem_programSchema
    (P : Program D Γ)
    (X : IDBSym P) :
    X.1.1 ∈ Γ.syms :=
  X.1.2

/- An IDB symbol as a program-schema symbol. -/
def idbOutputSym
    (P : Program D Γ)
    (X : IDBSym P) :
    (Γ).syms :=
  ⟨X.1.1, idb_mem_programSchema P X⟩

/- An IDB symbol as an execution-schema symbol. -/
def idbExecSym
    (P : Program D Γ)
    (X : IDBSym P) :
    (execSchema P).syms :=
  outputSym P (idbOutputSym P X)

/- IDB arity is unchanged in the execution schema. -/
theorem idbExecSym_arity
    (P : Program D Γ)
    (X : IDBSym P) :
    (execSchema P).arity (idbExecSym P X) =
      Γ.arity X.1 := by
  have hOut :=
    outputSym_arity P (idbOutputSym P X)
  have hProg :=
    UnnamedSchema.arity_eq_of_extensionOf
      (UnnamedSchema.extensionOf_refl Γ) X.1
  exact hOut.trans hProg

/- Index of an IDB symbol in `idbList`. -/
def idbIndex
    (P : Program D Γ)
    (X : IDBSym P) :
    Nat :=
  (idbList P).idxOf X.1

/- The IDB index is in bounds. -/
theorem idbIndex_lt
  (P : Program D Γ)
  (X : IDBSym P) :
  idbIndex P X < (idbList P).length := by
  have hMem : X.1 ∈ idbList P := by
    have hHead : X.1 ∈ P.headSymbolList := by
      have hFin : X.1 ∈ P.headSymbolList.toFinset := by
        change X.1 ∈ P.headSymbolList.toFinset
        exact X.2
      exact List.mem_toFinset.mp hFin
    simpa [idbList, Program.idbList] using
      (List.mem_eraseDups.mpr hHead)
  exact List.idxOf_lt_length_of_mem hMem

/- Raw snapshot name paired with an IDB symbol. -/
def snapshotRawOf
    (P : Program D Γ)
    (X : IDBSym P) :
    A :=
  let i := idbIndex P X
  (snapshotNames P)[i]'(by
    rw [snapshotNames_length]
    exact idbIndex_lt P X)

/-
  The generated snapshot name appears in `snapshotNames`.
-/
theorem snapshotRawOf_mem
    (P : Program D Γ)
    (X : IDBSym P) :
    snapshotRawOf P X ∈ snapshotNames P := by
  unfold snapshotRawOf
  exact List.getElem_mem _

/-
  The generated snapshot name is not a program-schema
  symbol.
-/
theorem snapshotRawOf_not_prog
    (P : Program D Γ)
    (X : IDBSym P) :
    snapshotRawOf P X ∉ (Γ).syms :=
  snapshotNames_fresh P (snapshotRawOf_mem P X)

/-
  The generated snapshot name appears in the execution
  schema.
-/
theorem snapshotRawOf_mem_exec
    (P : Program D Γ)
    (X : IDBSym P) :
    snapshotRawOf P X ∈ (execSchema P).syms := by
  exact
    Finset.mem_union.mpr
      (Or.inr (by
        simpa using snapshotRawOf_mem P X))

/- Snapshot symbol paired with an IDB symbol. -/
def snapshotOf
    (P : Program D Γ)
    (X : IDBSym P) :
    (execSchema P).syms :=
  ⟨snapshotRawOf P X, snapshotRawOf_mem_exec P X⟩

/- Lookup returns the arity paired with `snapshotOf`. -/
theorem snapshotArity?_snapshotRawOf
    (P : Program D Γ)
    (X : IDBSym P) :
    snapshotArity? P (snapshotRawOf P X) =
      some (Γ.arity X.1) := by
  unfold snapshotArity? snapshotRawOf
  let i := idbIndex P X
  have hiIdb : i < (idbList P).length :=
    idbIndex_lt P X
  have hiSnap : i < (snapshotNames P).length := by
    rw [snapshotNames_length]
    exact hiIdb
  have hiAr : i < (idbArityList P).length := by
    rw [idbArityList_length]
    exact hiIdb
  have hLen :
      (snapshotNames P).length =
        (idbArityList P).length := by
    rw [snapshotNames_length, idbArityList_length]
  have hLookup :=
    pairLookup_get hLen (snapshotNames_nodup P)
      i hiSnap hiAr
  have hIdbGet :
      (idbList P)[i] = X.1 := by
    have hMem : X.1 ∈ idbList P := by
      have hHead : X.1 ∈ P.headSymbolList := by
        have hFin : X.1 ∈ P.headSymbolList.toFinset := by
          change X.1 ∈ P.headSymbolList.toFinset
          exact X.2
        exact List.mem_toFinset.mp hFin
      simpa [idbList, Program.idbList] using
        (List.mem_eraseDups.mpr hHead)
    change (idbList P)[(idbList P).idxOf X.1] = X.1
    exact List.getElem_idxOf
      (List.idxOf_lt_length_of_mem hMem)
  have hArGet :
      (idbArityList P)[i] = Γ.arity X.1 := by
    simp [idbArityList, hIdbGet]
  simpa [hiSnap, hArGet] using hLookup

/- Snapshot arity agrees with its paired IDB arity. -/
theorem snapshotOf_arity
    (P : Program D Γ)
    (X : IDBSym P) :
    (execSchema P).arity (snapshotOf P X) =
      Γ.arity X.1 := by
  have hNot := snapshotRawOf_not_prog P X
  have hLookup := snapshotArity?_snapshotRawOf P X
  simp [execSchema, snapshotOf, hNot, hLookup]

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Relational Algebra Helpers
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Relation expression for a live IDB. -/
def idbRelExpr
    (P : Program D Γ)
    (X : IDBSym P) :
    RAExpr D (execSchema P)
      ((execSchema P).arity (idbExecSym P X)) :=
  RAExpr.rel (idbExecSym P X)

/- Relation expression for an IDB snapshot. -/
def snapshotRelExpr
    (P : Program D Γ)
    (X : IDBSym P) :
    RAExpr D (execSchema P)
      ((execSchema P).arity (snapshotOf P X)) :=
  RAExpr.rel (snapshotOf P X)

/- Empty relation at the paired snapshot arity. -/
def emptySnapshotExpr
    (P : Program D Γ)
    (X : IDBSym P) :
    RAExpr D (execSchema P)
      ((execSchema P).arity (snapshotOf P X)) :=
  RAExpr.empty ((execSchema P).arity (snapshotOf P X))

/- Snapshot expression cast to the live IDB arity. -/
def snapshotAsIDBExpr
    (P : Program D Γ)
    (X : IDBSym P) :
    RAExpr D (execSchema P)
      ((execSchema P).arity (idbExecSym P X)) :=
  RAExpr.castArity
    (by
      rw [snapshotOf_arity, idbExecSym_arity])
    (snapshotRelExpr P X)

/- Live IDB expression cast to the snapshot arity. -/
def idbAsSnapshotExpr
    (P : Program D Γ)
    (X : IDBSym P) :
    RAExpr D (execSchema P)
      ((execSchema P).arity (snapshotOf P X)) :=
  RAExpr.castArity
    (by
      rw [idbExecSym_arity, snapshotOf_arity])
    (idbRelExpr P X)

/- Substitute one IDB read by its snapshot relation. -/
def oldifyOne
    (P : Program D Γ)
    {n : Nat}
    (e : RAExpr D (execSchema P) n)
    (X : IDBSym P) :
    RAExpr D (execSchema P) n :=
  if (idbExecSym P X).1 ∈ e.symbols then
    e.subst (idbExecSym P X) (snapshotAsIDBExpr P X)
  else
    e

/- Substitute all IDB reads by their snapshots. -/
def oldifyIDBs
    (P : Program D Γ)
    {n : Nat}
    (e : RAExpr D (execSchema P) n) :
    List (IDBSym P) → RAExpr D (execSchema P) n
| [] => e
| X :: Xs => oldifyIDBs P (oldifyOne P e X) Xs

/-
  View the Datalog `SPJU` query for `X` over the execution
  schema and replace live IDB reads by their snapshot
  relations.
-/
def oldifiedConsequenceSPJU
    (P : Program D Γ)
    (X : IDBSym P) :
    RAExpr D (execSchema P) (Γ.arity X.1) :=
  let hExt :=
    UnnamedSchema.extensionOf_trans
      (execSchema_extension_output P)
      (UnnamedSchema.extensionOf_refl Γ)
  oldifyIDBs P
    ((P.consequenceSPJU X.1).onExtension hExt)
    (idbSymList P)

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Consequence Expressions
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Immediate-consequence `SPJU` contribution for one live
  IDB.
-/
def consequenceExpr
    (P : Program D Γ)
    (X : IDBSym P) :
    RAExpr D (execSchema P)
      ((execSchema P).arity (idbExecSym P X)) :=
  RAExpr.castArity
    (idbExecSym_arity P X)
    (oldifiedConsequenceSPJU P X)

/- Cumulative next value for one live IDB. -/
def nextIDBExpr
    (P : Program D Γ)
    (X : IDBSym P) :
    RAExpr D (execSchema P)
      ((execSchema P).arity (idbExecSym P X)) :=
  RAExpr.union (idbRelExpr P X) (consequenceExpr P X)

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Commands and Guards
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Copy one live IDB relation into its snapshot. -/
def snapshotIDBCmd
    (P : Program D Γ)
    (X : IDBSym P) :
    Whiel.Cmd D (execSchema P) :=
  .assign (snapshotOf P X) (idbAsSnapshotExpr P X)

/- Initialize one snapshot relation to empty. -/
def emptySnapshotIDBCmd
    (P : Program D Γ)
    (X : IDBSym P) :
    Whiel.Cmd D (execSchema P) :=
  .assign (snapshotOf P X) (emptySnapshotExpr P X)

/-
  Apply the grouped immediate-consequence update to one IDB.
-/
def stepIDBCmd
    (P : Program D Γ)
    (X : IDBSym P) :
    Whiel.Cmd D (execSchema P) :=
  .assign (idbExecSym P X) (nextIDBExpr P X).clean

/-
  Apply the first destructive grouped consequence update to
  one live IDB. The right-hand side reads recursive IDBs
  through snapshots and does not union with the current live
  IDB value.
-/
def initialStepIDBCmd
    (P : Program D Γ)
    (X : IDBSym P) :
    Whiel.Cmd D (execSchema P) :=
  .assign (idbExecSym P X) (consequenceExpr P X).clean

/- Snapshot all live IDBs. -/
def snapshotCmd
    (P : Program D Γ) :
    Whiel.Cmd D (execSchema P) :=
  seqList ((idbSymList P).map (snapshotIDBCmd P))

/- Initialize all generated snapshots to empty. -/
def emptySnapshotsCmd
    (P : Program D Γ) :
    Whiel.Cmd D (execSchema P) :=
  seqList ((idbSymList P).map (emptySnapshotIDBCmd P))

/-
  Run one synchronous grouped immediate-consequence step.
-/
def stepCmd
    (P : Program D Γ) :
    Whiel.Cmd D (execSchema P) :=
  seqList ((idbSymList P).map (stepIDBCmd P))

/- Run the initial destructive grouped consequence step. -/
def initialStepCmd
    (P : Program D Γ) :
    Whiel.Cmd D (execSchema P) :=
  seqList ((idbSymList P).map (initialStepIDBCmd P))

/- Equality guard between one live IDB and its snapshot. -/
def equalSnapshotGuard
    (P : Program D Γ)
    (X : IDBSym P) :
    Whiel.Guard D (execSchema P) :=
  .eq (idbRelExpr P X) (snapshotAsIDBExpr P X)

/- Loop guard: at least one IDB changed since snapshot. -/
def changedGuard
    (P : Program D Γ) :
    Whiel.Guard D (execSchema P) :=
  .not
    (andList
      ((idbSymList P).map
        (equalSnapshotGuard P)))

/- One synchronous naive iteration. -/
def iterationCmd
    (P : Program D Γ) :
    Whiel.Cmd D (execSchema P) :=
  seqList
    (((idbSymList P).map (snapshotIDBCmd P)) ++
      ((idbSymList P).map (stepIDBCmd P)))

/-
  Naive command before syntax-directed cleanup. The pre-loop
  phase initializes snapshots to empty and then destructively
  assigns each live IDB from oldified consequences over those
  empty snapshots. The loop body is the shared monotone
  iteration.
-/
def cmdCore
    (P : Program D Γ) :
    Whiel.Cmd D (execSchema P) :=
  seqList
    (((idbSymList P).map (emptySnapshotIDBCmd P)) ++
      ((idbSymList P).map (initialStepIDBCmd P)) ++
      [.while (changedGuard P) (iterationCmd P)])

end Naive

end WhielCompiler

namespace Program

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Method-style access to the naive command translation.
-/
def toWhielCmd
    (P : Program D Γ) :
  Whiel.Cmd D (WhielCompiler.Naive.execSchema P) :=
  (WhielCompiler.Naive.cmdCore P).clean

/-
  Method-style access to the naive Whiel program
  translation.
-/
def toWhielProgram
    (P : Program D Γ) :
    Whiel.Program D P.edbSchema (Γ) where
  execSchema := WhielCompiler.Naive.execSchema P
  extendsInput :=
    WhielCompiler.Naive.execSchema_extension_input P
  extendsOutput :=
    WhielCompiler.Naive.execSchema_extension_output P
  cmd := P.toWhielCmd

end Program

end Datalog

------------------------------------------------------------
-- Naive Execution-Schema Symbol Facts
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  A generated snapshot symbol is distinct from every live
  IDB execution symbol, because snapshots are fresh for the
  program schema and live IDBs are program-schema symbols.
-/
theorem snapshotOf_ne_idbExecSym
    (P : Program D Γ)
    (X Y : IDBSym P) :
    snapshotOf P X ≠ idbExecSym P Y := by
  intro hEq
  have hRaw :
      snapshotRawOf P X = (idbExecSym P Y).1 :=
    congrArg Subtype.val hEq
  have hOut :
      (idbExecSym P Y).1 ∈
        (Γ).syms := by
    change (idbOutputSym P Y).1 ∈
      (Γ).syms
    exact (idbOutputSym P Y).2
  have hSnapOut :
      snapshotRawOf P X ∈
        (Γ).syms := by
    simpa [hRaw] using hOut
  exact (snapshotRawOf_not_prog P X) hSnapOut

/-
  Live IDB execution symbols are injective in their IDB
  argument.
-/
theorem idbExecSym_injective
    (P : Program D Γ) :
    Function.Injective (idbExecSym P) := by
  intro X Y hEq
  have hRaw : X.1.1 = Y.1.1 := by
    have hRawExec :
        (idbExecSym P X).1 = (idbExecSym P Y).1 :=
      congrArg (fun Z : (execSchema P).syms => Z.1) hEq
    simpa [idbExecSym, outputSym, idbOutputSym] using
      hRawExec
  have hSym : X.1 = Y.1 := by
    exact Subtype.ext hRaw
  exact Subtype.ext hSym

/-
  Every typed IDB symbol occurs in the compiler's IDB list.
-/
theorem mem_idbSymList
    (P : Program D Γ)
    (X : IDBSym P) :
    X ∈ idbSymList P := by
  unfold idbSymList IDBSym
  have hList : X.1 ∈ P.idbList := by
    have hHead : X.1 ∈ P.headSymbolList := by
      exact List.mem_toFinset.mp X.2
    simpa [Program.idbList] using
      (List.mem_eraseDups.mpr hHead)
  refine List.mem_map.mpr ?_
  refine ⟨⟨X.1, hList⟩, List.mem_attach _ _, ?_⟩
  exact Subtype.ext rfl

/-
  Looking up an IDB at its compiler index returns that IDB.
-/
theorem idbList_get_idbIndex
    (P : Program D Γ)
    (X : IDBSym P) :
    (idbList P)[idbIndex P X]'(idbIndex_lt P X) = X.1 := by
  have hMem : X.1 ∈ idbList P := by
    have hHead : X.1 ∈ P.headSymbolList := by
      have hFin : X.1 ∈ P.headSymbolList.toFinset := by
        change X.1 ∈ P.headSymbolList.toFinset
        exact X.2
      exact List.mem_toFinset.mp hFin
    simpa [idbList, Program.idbList] using
      (List.mem_eraseDups.mpr hHead)
  simp [idbIndex, List.getElem_idxOf
    (List.idxOf_lt_length_of_mem hMem)]

/- Snapshot symbols are injective in their IDB argument. -/
theorem snapshotOf_injective
    (P : Program D Γ) :
    Function.Injective (snapshotOf P) := by
  intro X Y hEq
  have hRaw :
      snapshotRawOf P X = snapshotRawOf P Y :=
    congrArg Subtype.val hEq
  have hiIdb : idbIndex P X < (idbList P).length :=
    idbIndex_lt P X
  have hjIdb : idbIndex P Y < (idbList P).length :=
    idbIndex_lt P Y
  have hiSnap :
      idbIndex P X < (snapshotNames P).length := by
    rw [snapshotNames_length]
    exact hiIdb
  have hjSnap :
      idbIndex P Y < (snapshotNames P).length := by
    rw [snapshotNames_length]
    exact hjIdb
  have hIdx :
      idbIndex P X = idbIndex P Y := by
    have hGet :
        (snapshotNames P)[idbIndex P X] =
          (snapshotNames P)[idbIndex P Y] := by
      simpa [snapshotRawOf] using hRaw
    exact
      (snapshotNames_nodup P).getElem_inj_iff.mp hGet
  have hSym : X.1 = Y.1 := by
    have hxOpt :
        (idbList P)[idbIndex P X]? = some X.1 := by
      rw [List.getElem?_eq_getElem (idbIndex_lt P X),
        idbList_get_idbIndex]
    have hyOpt :
        (idbList P)[idbIndex P Y]? = some Y.1 := by
      rw [List.getElem?_eq_getElem (idbIndex_lt P Y),
        idbList_get_idbIndex]
    have hOpt :
        (idbList P)[idbIndex P X]? =
          (idbList P)[idbIndex P Y]? := by
      rw [hIdx]
    rw [hxOpt, hyOpt] at hOpt
    injection hOpt
  exact Subtype.ext hSym

/-
  Program-schema symbol viewed as an execution-schema
  symbol.
-/
def progExecSym
    (P : Program D Γ)
    (X : Γ.syms) :
    (execSchema P).syms :=
  let hExt :=
    UnnamedSchema.extensionOf_trans
      (execSchema_extension_output P)
      (UnnamedSchema.extensionOf_refl Γ)
  ⟨X.1, hExt.1 X.2⟩

/-
  A live IDB execution symbol is the program symbol embedded
  into the execution schema.
-/
theorem idbExecSym_eq_progExecSym
    (P : Program D Γ)
    (X : IDBSym P) :
    idbExecSym P X = progExecSym P X.1 := by
  apply Subtype.ext
  simp [idbExecSym, outputSym, idbOutputSym, progExecSym]

/-
  A generated snapshot symbol cannot be a program-schema
  symbol.
-/
theorem snapshotOf_ne_progExecSym
    (P : Program D Γ)
    (X : IDBSym P)
    (Y : Γ.syms) :
    snapshotOf P X ≠ progExecSym P Y := by
  intro hEq
  have hRaw :
      snapshotRawOf P X = Y.1 := by
    have hRawExec :
        (snapshotOf P X).1 =
          (progExecSym P Y).1 :=
      congrArg (fun Z : (execSchema P).syms => Z.1) hEq
    simpa [snapshotOf, progExecSym] using hRawExec
  exact snapshotRawOf_not_prog P X
    (by simpa [← hRaw] using Y.2)

/-
  A live IDB execution symbol cannot equal a non-IDB program
  symbol.
-/
theorem idbExecSym_ne_progExecSym_of_not_idb
    (P : Program D Γ)
    (Y : IDBSym P)
    (X : Γ.syms)
    (hX : X ∉ P.idb) :
    idbExecSym P Y ≠ progExecSym P X := by
  intro hEq
  have hRaw : Y.1.1 = X.1 := by
    have hRawExec :
        (idbExecSym P Y).1 =
          (progExecSym P X).1 :=
      congrArg (fun Z : (execSchema P).syms => Z.1) hEq
    simpa [idbExecSym, outputSym, idbOutputSym,
      progExecSym] using hRawExec
  have hSym : Y.1 = X := Subtype.ext hRaw
  exact hX (by simpa [hSym] using Y.2)

end Naive

end WhielCompiler

end Datalog

/-
  Correctness proof support for the synchronous naive
  Datalog-to-Whiel translation.

  The compiler construction appears above. The declarations
  below are proof-specific state views, oldification facts,
  command facts, and the command-level connection used by the
  final public `Program.toWhielProgram_*` theorems.
-/

------------------------------------------------------------
-- Naive Correctness State Views
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Program-schema view of the live EDB/IDB relations in an
  execution-schema state.
-/
def liveState
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    Instance D Γ :=
  Instance.reduct
    (UnnamedSchema.extensionOf_trans
      (execSchema_extension_output P)
      (UnnamedSchema.extensionOf_refl Γ))
    J

/-
  Live IDB relation viewed at the corresponding
  program-schema arity. The cast is only the arity transport
  induced by the execution-schema embedding.
-/
def liveIDBRel
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (X : IDBSym P) :
    FinRelation D (Γ.arity X.1) :=
  cast
    (congrArg (FinRelation D)
      (idbExecSym_arity P X))
    (J (idbExecSym P X))

/-
  Snapshot IDB relation viewed at the corresponding
  program-schema arity. The cast is only the arity transport
  from the generated snapshot symbol back to its source IDB.
-/
def snapshotIDBRel
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (X : IDBSym P) :
    FinRelation D (Γ.arity X.1) :=
  cast
    (congrArg (FinRelation D)
      (snapshotOf_arity P X))
    (J (snapshotOf P X))

/-
  Program-schema view whose IDBs are read from snapshot
  relations and whose non-IDBs are read from the live state.
-/
def snapshotState
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    Instance D Γ :=
  fun X =>
    if hX : X ∈ P.idb then
      snapshotIDBRel P J ⟨X, hX⟩
    else
      liveState P J X

/-
  IDB lookup in `snapshotState` is exactly the normalized
  snapshot relation.
-/
theorem snapshotState_idb
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (X : IDBSym P) :
    snapshotState P J X.1 = snapshotIDBRel P J X := by
  unfold snapshotState
  exact dif_pos X.2

/-
  Non-IDB lookup in `snapshotState` is exactly the
  live-state relation.
-/
theorem snapshotState_not_idb
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (X : Γ.syms)
    (hX : X ∉ P.idb) :
    snapshotState P J X = liveState P J X := by
  unfold snapshotState
  exact dif_neg hX

/-
  IDB lookup in `liveState` is exactly the normalized live
  IDB relation. This is an arity-transport fact for the
  execution-schema embedding.
-/
theorem liveState_idb
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (X : IDBSym P) :
    liveState P J X.1 = liveIDBRel P J X := by
  unfold liveState liveIDBRel
  let hExt :=
    UnnamedSchema.extensionOf_trans
      (execSchema_extension_output P)
      (UnnamedSchema.extensionOf_refl Γ)
  change
    Instance.reduct hExt J X.1 =
      cast
        (congrArg (FinRelation D)
          (idbExecSym_arity P X))
        (J (idbExecSym P X))
  unfold Instance.reduct
  have hEq := (idbExecSym_eq_progExecSym P X).symm
  change
    cast
        (congrArg (FinRelation D)
          (UnnamedSchema.arity_eq_of_extensionOf hExt X.1))
        (J (progExecSym P X.1)) =
      cast
        (congrArg (FinRelation D)
          (idbExecSym_arity P X))
        (J (idbExecSym P X))
  cases hEq
  exact
    FinRelation.cast_proof_irrel
      (UnnamedSchema.arity_eq_of_extensionOf hExt X.1)
      (idbExecSym_arity P X)
      (J (progExecSym P X.1))

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Restore And Oldification Helpers
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Replace the live execution relation for each listed IDB by
  the value stored in its snapshot relation. This is a proof
  device for relating the oldified RA expression generated
  by the compiler to ordinary evaluation of the Datalog
  `SPJU` query over a program-schema snapshot instance.
-/
def restoreIDBs
    (P : Program D Γ) :
    Instance D (execSchema P) →
      List (IDBSym P) → Instance D (execSchema P)
| J, [] => J
| J, X :: Xs =>
    let J' := restoreIDBs P J Xs
    Instance.update J' (idbExecSym P X)
      ((snapshotAsIDBExpr P X).eval J')

/-
  Evaluating an expression after substituting all live IDB
  reads by snapshot reads is the same as evaluating the
  original expression in the execution state where those
  live IDBs have been restored from their snapshots.
-/
theorem oldifyIDBs_eval_restoreIDBs
    (P : Program D Γ)
    {n : Nat}
    (e : RAExpr D (execSchema P) n)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      (oldifyIDBs P e Xs).eval J =
        e.eval (restoreIDBs P J Xs)
| [] => by
    rfl
| X :: Xs => by
    calc
      (oldifyIDBs P e (X :: Xs)).eval J
          =
        (oldifyOne P e X).eval
          (restoreIDBs P J Xs) := by
            simpa [oldifyIDBs] using
              oldifyIDBs_eval_restoreIDBs
                P (oldifyOne P e X) J Xs
      _ =
        e.eval
          (Instance.update (restoreIDBs P J Xs)
            (idbExecSym P X)
            ((snapshotAsIDBExpr P X).eval
              (restoreIDBs P J Xs))) := by
            by_cases hMem :
                (idbExecSym P X).1 ∈ e.symbols
            · simp [oldifyOne, hMem, RAExpr.subst_eval]
            · have hRawEval :=
                RawRAExpr.eval?_update_no_occur
                  (restoreIDBs P J Xs)
                  (idbExecSym P X)
                  ((snapshotAsIDBExpr P X).eval
                    (restoreIDBs P J Xs))
                  (e := e.expr)
                  (by
                    simpa [RAExpr.symbols] using hMem)
              have hUpdate :
                  e.eval
                      (Instance.update
                        (restoreIDBs P J Xs)
                        (idbExecSym P X)
                        ((snapshotAsIDBExpr P X).eval
                          (restoreIDBs P J Xs))) =
                    e.eval (restoreIDBs P J Xs) := by
                have hOpt :
                    some
                        (⟨n, e.eval
                          (Instance.update
                            (restoreIDBs P J Xs)
                            (idbExecSym P X)
                            ((snapshotAsIDBExpr P X).eval
                              (restoreIDBs P J Xs)))⟩ :
                          Sigma (FinRelation D)) =
                      some
                        ⟨n, e.eval (restoreIDBs P J Xs)⟩ := by
                  calc
                    some
                        (⟨n, e.eval
                          (Instance.update
                            (restoreIDBs P J Xs)
                            (idbExecSym P X)
                            ((snapshotAsIDBExpr P X).eval
                              (restoreIDBs P J Xs)))⟩ :
                          Sigma (FinRelation D))
                        = e.expr.eval?
                            (Instance.update
                              (restoreIDBs P J Xs)
                              (idbExecSym P X)
                              ((snapshotAsIDBExpr P X).eval
                                (restoreIDBs P J Xs))) := by
                          simpa using
                            (RAExpr.raw_eval?_eq_eval e
                              (Instance.update
                                (restoreIDBs P J Xs)
                                (idbExecSym P X)
                                ((snapshotAsIDBExpr P X).eval
                                  (restoreIDBs P J Xs)))).symm
                    _ = e.expr.eval? (restoreIDBs P J Xs) :=
                          hRawEval
                    _ = some
                        ⟨n, e.eval (restoreIDBs P J Xs)⟩ := by
                          simpa using
                            RAExpr.raw_eval?_eq_eval e
                              (restoreIDBs P J Xs)
                injection hOpt with hEq
                injection hEq
              simpa [oldifyOne, hMem] using hUpdate.symm
      _ =
        e.eval (restoreIDBs P J (X :: Xs)) := by
            simp [restoreIDBs]

/-
  Restoring live IDBs does not change any snapshot
  expression: the only updates performed by `restoreIDBs`
  target live IDB symbols, and snapshot symbols are fresh
  for those targets.
-/
theorem snapshotAsIDBExpr_eval_restoreIDBs
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      (snapshotAsIDBExpr P Y).eval
          (restoreIDBs P J Xs) =
        (snapshotAsIDBExpr P Y).eval J
| [] => by
    rfl
| X :: Xs => by
    have hTail :=
      snapshotAsIDBExpr_eval_restoreIDBs P Y J Xs
    have hNe : snapshotOf P Y ≠ idbExecSym P X :=
      snapshotOf_ne_idbExecSym P Y X
    rw [restoreIDBs]
    let J' := restoreIDBs P J Xs
    calc
      (snapshotAsIDBExpr P Y).eval
          (Instance.update J' (idbExecSym P X)
            ((snapshotAsIDBExpr P X).eval J'))
          =
        (snapshotAsIDBExpr P Y).eval J' := by
          let R := (snapshotAsIDBExpr P X).eval J'
          change
            (snapshotAsIDBExpr P Y).eval
                (Instance.update J' (idbExecSym P X) R) =
              (snapshotAsIDBExpr P Y).eval J'
          have hNotMem :
              (idbExecSym P X).1 ∉
                (snapshotAsIDBExpr P Y).expr.symbols := by
            have hRawNe :
                (idbExecSym P X).1 ≠
                  (snapshotOf P Y).1 := by
              intro hRaw
              exact hNe (Subtype.ext hRaw.symm)
            simpa [snapshotAsIDBExpr, snapshotRelExpr,
              RAExpr.castArity, RAExpr.rel,
              RawRAExpr.symbols]
              using hRawNe
          have hRawEval :=
            RawRAExpr.eval?_update_no_occur
              J' (idbExecSym P X)
              R
              (e := (snapshotAsIDBExpr P Y).expr)
              hNotMem
          unfold RAExpr.eval
          rw [hRawEval]
      _ =
        (snapshotAsIDBExpr P Y).eval J := by
          simpa [J'] using hTail

/-
  A snapshot-as-live-IDB expression evaluates to the
  snapshot relation.
-/
theorem snapshotAsIDBExpr_eval
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    (snapshotAsIDBExpr P Y).eval J =
      cast
        (congrArg (FinRelation D)
          ((snapshotOf_arity P Y).trans
            (idbExecSym_arity P Y).symm))
        (J (snapshotOf P Y)) := by
  let hAr :=
    (snapshotOf_arity P Y).trans
      (idbExecSym_arity P Y).symm
  apply Finset.ext
  intro t
  simp [snapshotAsIDBExpr, snapshotRelExpr,
    RAExpr.castArity, RAExpr.eval, RAExpr.rel,
    RawRAExpr.eval?, Instance.relation?, hAr]

/-
  If an IDB occurs in the restoration list, its live
  execution relation after restoration is the snapshot
  relation from the original execution state.
-/
theorem restoreIDBs_lookup_idb_of_mem
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      Y ∈ Xs →
        (restoreIDBs P J Xs) (idbExecSym P Y) =
          (snapshotAsIDBExpr P Y).eval J
| [], hY => by
    cases hY
| X :: Xs, hY => by
    rw [restoreIDBs]
    let J' := restoreIDBs P J Xs
    rcases List.mem_cons.mp hY with hEq | hTail
    · subst hEq
      simp [snapshotAsIDBExpr_eval_restoreIDBs]
    · by_cases hExec :
          idbExecSym P Y = idbExecSym P X
      · have hYX : Y = X :=
          idbExecSym_injective P hExec
        subst hYX
        simp [snapshotAsIDBExpr_eval_restoreIDBs]
      · have hLookup :
            (Instance.update J' (idbExecSym P X)
                ((snapshotAsIDBExpr P X).eval J'))
              (idbExecSym P Y) =
            J' (idbExecSym P Y) := by
          exact
            Instance.update_lookup_ne J' (idbExecSym P X)
              (idbExecSym P Y) hExec
              ((snapshotAsIDBExpr P X).eval J')
        calc
          (Instance.update J' (idbExecSym P X)
              ((snapshotAsIDBExpr P X).eval J'))
              (idbExecSym P Y)
              =
            J' (idbExecSym P Y) := hLookup
          _ =
            (snapshotAsIDBExpr P Y).eval J := by
              simpa [J'] using
                restoreIDBs_lookup_idb_of_mem
                  P Y J Xs hTail

/-
  Restoring live IDBs leaves every non-IDB program-schema
  relation unchanged in the execution state.
-/
theorem restoreIDBs_lookup_progExecSym_of_not_idb
    (P : Program D Γ)
    (Y : Γ.syms)
    (hY : Y ∉ P.idb)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      (restoreIDBs P J Xs) (progExecSym P Y) =
        J (progExecSym P Y)
| [] => by
    rfl
| X :: Xs => by
    rw [restoreIDBs]
    let J' := restoreIDBs P J Xs
    have hNe :
        progExecSym P Y ≠ idbExecSym P X := by
      exact
        (idbExecSym_ne_progExecSym_of_not_idb
          P X Y hY).symm
    have hLookup :
        (Instance.update J' (idbExecSym P X)
            ((snapshotAsIDBExpr P X).eval J'))
          (progExecSym P Y) =
        J' (progExecSym P Y) := by
      exact
        Instance.update_lookup_ne J' (idbExecSym P X)
          (progExecSym P Y) hNe
          ((snapshotAsIDBExpr P X).eval J')
    calc
      (Instance.update J' (idbExecSym P X)
          ((snapshotAsIDBExpr P X).eval J'))
          (progExecSym P Y)
          =
        J' (progExecSym P Y) := hLookup
      _ =
        J (progExecSym P Y) := by
          simpa [J'] using
            restoreIDBs_lookup_progExecSym_of_not_idb
              P Y hY J Xs

/-
  Program-schema reduct of the restored execution instance
  is exactly the snapshot-state view: IDBs come from
  snapshots and non-IDBs come from the live execution state.
-/
theorem reduct_restoreIDBs_eq_snapshotState
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    Instance.reduct
        (UnnamedSchema.extensionOf_trans
          (execSchema_extension_output P)
          (UnnamedSchema.extensionOf_refl Γ))
        (restoreIDBs P J (idbSymList P)) =
      snapshotState P J := by
  let hExt :=
    UnnamedSchema.extensionOf_trans
      (execSchema_extension_output P)
      (UnnamedSchema.extensionOf_refl Γ)
  change
    Instance.reduct hExt
        (restoreIDBs P J (idbSymList P)) =
      snapshotState P J
  apply Instance.ext
  intro X
  apply Finset.ext
  intro t
  by_cases hX : X ∈ P.idb
  · have hLookup :=
      restoreIDBs_lookup_idb_of_mem P ⟨X, hX⟩ J
        (idbSymList P)
        (mem_idbSymList P ⟨X, hX⟩)
    have hLookupExt :
        restoreIDBs P J (idbSymList P)
            (UnnamedSchema.symOfExtension hExt X) =
          (snapshotAsIDBExpr P ⟨X, hX⟩).eval J := by
      simpa [hExt, progExecSym] using hLookup
    have hEval :=
      snapshotAsIDBExpr_eval P ⟨X, hX⟩ J
    have hSnap :
        snapshotState P J X =
          cast
            (congrArg (FinRelation D)
              (snapshotOf_arity P ⟨X, hX⟩))
            (J (snapshotOf P ⟨X, hX⟩)) := by
      unfold snapshotState
      exact dif_pos hX
    rw [Instance.reduct_mem_iff]
    rw [hSnap]
    rw [hLookupExt, hEval]
    let hLiveSnap :=
      (snapshotOf_arity P ⟨X, hX⟩).trans
        (idbExecSym_arity P ⟨X, hX⟩).symm
    let hProgSnap := snapshotOf_arity P ⟨X, hX⟩
    have hLeft :=
      FinRelation.mem_cast_iff hLiveSnap
        (J (snapshotOf P ⟨X, hX⟩))
        (Tuple.toExtension hExt X t)
    have hRight :=
      FinRelation.mem_cast_iff hProgSnap
        (J (snapshotOf P ⟨X, hX⟩))
        t
    have hTuple :
        Tuple.castArity hLiveSnap
            (Tuple.toExtension hExt X t) =
          Tuple.castArity hProgSnap t := by
      have hExtAr :=
        UnnamedSchema.arity_eq_of_extensionOf hExt X
      calc
        Tuple.castArity hLiveSnap
            (Tuple.toExtension hExt X t)
            =
          Tuple.castArity hLiveSnap
            (Tuple.castArity hExtAr t) := by
              rfl
        _ =
          Tuple.castArity (hLiveSnap.trans hExtAr) t :=
            Tuple.castArity_trans hLiveSnap hExtAr t
        _ =
          Tuple.castArity hProgSnap t :=
            Tuple.castArity_proof_irrel
              (hLiveSnap.trans hExtAr) hProgSnap t
    have hMid :
        (Tuple.castArity hLiveSnap
            (Tuple.toExtension hExt X t) ∈
          J (snapshotOf P ⟨X, hX⟩)) ↔
        (Tuple.castArity hProgSnap t ∈
          J (snapshotOf P ⟨X, hX⟩)) := by
      rw [hTuple]
    exact hLeft.trans (hMid.trans hRight.symm)
  · have hLookup :=
      restoreIDBs_lookup_progExecSym_of_not_idb P X hX J
        (idbSymList P)
    have hLookupExt :
        restoreIDBs P J (idbSymList P)
            (UnnamedSchema.symOfExtension hExt X) =
          J (UnnamedSchema.symOfExtension hExt X) := by
      simpa [hExt, progExecSym] using hLookup
    have hSnap :
        snapshotState P J X = liveState P J X := by
      unfold snapshotState
      exact dif_neg hX
    rw [Instance.reduct_mem_iff]
    rw [hSnap]
    unfold liveState
    change
      Tuple.toExtension hExt X t ∈
          restoreIDBs P J (idbSymList P)
            (UnnamedSchema.symOfExtension hExt X) ↔
        t ∈ Instance.reduct hExt J X
    rw [Instance.reduct_mem_iff]
    rw [hLookupExt]

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Consequence Expression Semantics
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Oldified consequence `SPJU` evaluation in an execution
  state is ordinary Datalog `SPJU` evaluation in the
  program-schema snapshot state.
-/
theorem oldifiedConsequenceSPJU_eval_snapshotState
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P)) :
    (oldifiedConsequenceSPJU P X).eval J =
      (P.consequenceSPJU X.1).eval
        (snapshotState P J) := by
  let hExt :=
    UnnamedSchema.extensionOf_trans
      (execSchema_extension_output P)
      (UnnamedSchema.extensionOf_refl Γ)
  have hOld :=
    oldifyIDBs_eval_restoreIDBs P
      ((P.consequenceSPJU X.1).onExtension hExt)
      J (idbSymList P)
  have hRed :
      ((P.consequenceSPJU X.1).onExtension hExt).eval
          (restoreIDBs P J (idbSymList P)) =
        (P.consequenceSPJU X.1).eval
          (snapshotState P J) := by
    haveI : Fact ((execSchema P).extensionOf Γ) :=
      ⟨hExt⟩
    have hRA :=
      RAExpr.reduct_property
        (e := P.consequenceSPJU X.1)
        (I := restoreIDBs P J (idbSymList P))
    have hRestore :=
      reduct_restoreIDBs_eq_snapshotState P J
    have hRA' :
        ((P.consequenceSPJU X.1).onExtension hExt).eval
            (restoreIDBs P J (idbSymList P)) =
          (P.consequenceSPJU X.1).eval
            (Instance.reduct hExt
              (restoreIDBs P J (idbSymList P))) := by
      simpa [RAExpr.eval, hExt] using hRA
    have hRestore' :
        Instance.reduct hExt
            (restoreIDBs P J (idbSymList P)) =
          snapshotState P J := by
      simpa [hExt] using hRestore
    exact hRA'.trans
      (congrArg
        (fun K =>
          (P.consequenceSPJU X.1).eval K)
        hRestore')
  exact hOld.trans hRed

/-
  Membership in the compiled consequence expression is
  membership in the Datalog `IDBConsequence` on the snapshot
  state, after transporting the queried tuple from the live
  execution-symbol arity to the program-symbol arity.
-/
theorem mem_consequenceExpr_eval_iff_IDBConsequence
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (X : IDBSym P) :
    ∀ t : Tuple D ((execSchema P).arity (idbExecSym P X)),
      t ∈ (consequenceExpr P X).eval J ↔
        Tuple.castArity (idbExecSym_arity P X).symm t ∈
          P.IDBConsequence (snapshotState P J) X.1 := by
  intro t
  have hOld :=
    oldifiedConsequenceSPJU_eval_snapshotState
      P X J
  have hCons :=
    P.IDBConsequence_eq_consequenceSPJU_eval
      (snapshotState P J) X.1
  rw [consequenceExpr]
  rw [RAExpr.mem_eval_castArity]
  rw [hOld]
  rw [← hCons]

/-
  A live-IDB relation expression evaluates to the live
  relation.
-/
theorem idbRelExpr_eval
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P)) :
    (idbRelExpr P X).eval J =
      J (idbExecSym P X) := by
  simp [idbRelExpr, RAExpr.eval, RAExpr.rel,
    RawRAExpr.eval?, Instance.relation?]

/-
  The empty-snapshot expression evaluates to the empty
  relation.
-/
theorem emptySnapshotExpr_eval
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P)) :
    (emptySnapshotExpr P X).eval J = ∅ := by
  simp [emptySnapshotExpr, RAExpr.eval, RAExpr.empty,
    RawRAExpr.eval?]

/-
  A live-IDB-as-snapshot expression evaluates to the live
  IDB relation.
-/
theorem idbAsSnapshotExpr_eval
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    (idbAsSnapshotExpr P Y).eval J =
      cast
        (congrArg (FinRelation D)
          ((idbExecSym_arity P Y).trans
            (snapshotOf_arity P Y).symm))
        (J (idbExecSym P Y)) := by
  let hAr :=
    (idbExecSym_arity P Y).trans
      (snapshotOf_arity P Y).symm
  apply Finset.ext
  intro t
  simp [idbAsSnapshotExpr, idbRelExpr,
    RAExpr.castArity, RAExpr.eval, RAExpr.rel,
    RawRAExpr.eval?, Instance.relation?, hAr]

/-
  The compiled next-IDB expression denotes the union of the
  current live IDB relation and the compiled consequence
  expression.
-/
theorem mem_nextIDBExpr_eval_iff
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P))
    (t : Tuple D ((execSchema P).arity (idbExecSym P X))) :
    t ∈ (nextIDBExpr P X).eval J ↔
      t ∈ J (idbExecSym P X) ∨
        t ∈ (consequenceExpr P X).eval J := by
  rw [nextIDBExpr]
  rw [RAExpr.mem_eval_union_iff]
  rw [idbRelExpr_eval]

/-
  Result of the compiled next-IDB expression, normalized to
  the corresponding program-schema IDB arity.
-/
def nextIDBRel
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (X : IDBSym P) :
    FinRelation D (Γ.arity X.1) :=
  cast
    (congrArg (FinRelation D)
      (idbExecSym_arity P X))
    ((nextIDBExpr P X).eval J)

/-
  Result of the compiled first-step consequence expression,
  normalized to the corresponding program-schema IDB arity.
-/
def consequenceRel
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (X : IDBSym P) :
    FinRelation D (Γ.arity X.1) :=
  cast
    (congrArg (FinRelation D)
      (idbExecSym_arity P X))
    ((consequenceExpr P X).eval J)

/-
  The compiled first-step consequence expression denotes
  the Datalog IDB consequence computed from the fixed
  snapshot-state view.
-/
theorem consequenceRel_eq_IDBConsequence
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (X : IDBSym P) :
    consequenceRel P J X =
      P.IDBConsequence (snapshotState P J) X.1 := by
  apply Finset.ext
  intro t
  unfold consequenceRel
  rw [FinRelation.mem_cast_iff (idbExecSym_arity P X)]
  rw [mem_consequenceExpr_eval_iff_IDBConsequence P J X]
  have hRound :
      Tuple.castArity (idbExecSym_arity P X).symm
          (Tuple.castArity (idbExecSym_arity P X) t) =
        t := by
    exact Tuple.castArity_symm (idbExecSym_arity P X) t
  rw [hRound]

/-
  The compiled next-IDB expression denotes the cumulative
  Datalog update for one IDB: old live contents union the
  IDB consequence computed from the snapshot-state view.
-/
theorem nextIDBRel_eq_live_union_IDBConsequence
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (X : IDBSym P) :
    nextIDBRel P J X =
      liveIDBRel P J X ∪
        P.IDBConsequence (snapshotState P J) X.1 := by
  apply Finset.ext
  intro t
  unfold nextIDBRel liveIDBRel
  rw [FinRelation.mem_cast_iff (idbExecSym_arity P X)]
  rw [Finset.mem_union]
  rw [FinRelation.mem_cast_iff (idbExecSym_arity P X)]
  rw [mem_nextIDBExpr_eval_iff]
  rw [mem_consequenceExpr_eval_iff_IDBConsequence
    P J X]
  have hRound :
      Tuple.castArity (idbExecSym_arity P X).symm
          (Tuple.castArity (idbExecSym_arity P X) t) =
            t := by
    exact Tuple.castArity_symm (idbExecSym_arity P X) t
  rw [hRound]

/-
  A single equality guard compares the live IDB to its
  snapshot.
-/
theorem equalSnapshotGuard_eval_iff
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P)) :
    Whiel.Guard.eval (equalSnapshotGuard P X) J ↔
      J (idbExecSym P X) =
        (snapshotAsIDBExpr P X).eval J := by
  simp [equalSnapshotGuard, idbRelExpr_eval]

theorem rawSnapshotEq_iff_liveIDBRel_eq_snapshotIDBRel
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P)) :
    J (idbExecSym P X) =
        (snapshotAsIDBExpr P X).eval J ↔
      liveIDBRel P J X = snapshotIDBRel P J X := by
  constructor
  · intro hRaw
    unfold liveIDBRel snapshotIDBRel
    rw [hRaw, snapshotAsIDBExpr_eval]
    let hSnapLive :=
      (snapshotOf_arity P X).trans
        (idbExecSym_arity P X).symm
    let hLiveProg := idbExecSym_arity P X
    let hSnapProg := snapshotOf_arity P X
    change
      cast (congrArg (FinRelation D) hLiveProg)
          (cast (congrArg (FinRelation D) hSnapLive)
            (J (snapshotOf P X))) =
        cast (congrArg (FinRelation D) hSnapProg)
          (J (snapshotOf P X))
    calc
      cast (congrArg (FinRelation D) hLiveProg)
          (cast (congrArg (FinRelation D) hSnapLive)
            (J (snapshotOf P X)))
          =
        cast (congrArg (FinRelation D)
            (hSnapLive.trans hLiveProg))
          (J (snapshotOf P X)) :=
            FinRelation.cast_trans hSnapLive hLiveProg
              (J (snapshotOf P X))
      _ =
        cast (congrArg (FinRelation D) hSnapProg)
          (J (snapshotOf P X)) :=
            FinRelation.cast_proof_irrel
              (hSnapLive.trans hLiveProg) hSnapProg
              (J (snapshotOf P X))
  · intro hNorm
    apply Finset.ext
    intro t
    rw [snapshotAsIDBExpr_eval]
    let hSnapLive :=
      (snapshotOf_arity P X).trans
        (idbExecSym_arity P X).symm
    let hLiveProg := idbExecSym_arity P X
    let hSnapProg := snapshotOf_arity P X
    let p : Tuple D (Γ.arity X.1) :=
      Tuple.castArity hLiveProg.symm t
    have hNormMem :
        p ∈ liveIDBRel P J X ↔
          p ∈ snapshotIDBRel P J X := by
      rw [hNorm]
    unfold liveIDBRel snapshotIDBRel at hNormMem
    have hLeft :
        p ∈ cast (congrArg (FinRelation D) hLiveProg)
            (J (idbExecSym P X)) ↔
          t ∈ J (idbExecSym P X) := by
      rw [FinRelation.mem_cast_iff hLiveProg]
      have hp :
          Tuple.castArity hLiveProg p = t := by
        dsimp [p]
        exact Tuple.castArity_symm hLiveProg.symm t
      rw [hp]
    have hRightNorm :
        p ∈ cast (congrArg (FinRelation D) hSnapProg)
            (J (snapshotOf P X)) ↔
          Tuple.castArity hSnapLive t ∈
            J (snapshotOf P X) := by
      rw [FinRelation.mem_cast_iff hSnapProg]
      have hp :
          Tuple.castArity hSnapProg p =
            Tuple.castArity hSnapLive t := by
        dsimp [p]
        calc
          Tuple.castArity hSnapProg
              (Tuple.castArity hLiveProg.symm t)
              =
            Tuple.castArity
                (hSnapProg.trans hLiveProg.symm) t :=
              Tuple.castArity_trans
                hSnapProg hLiveProg.symm t
          _ =
            Tuple.castArity hSnapLive t :=
              Tuple.castArity_proof_irrel
                (hSnapProg.trans hLiveProg.symm) hSnapLive t
      rw [hp]
    have hRight :
        p ∈ cast (congrArg (FinRelation D) hSnapProg)
            (J (snapshotOf P X)) ↔
          t ∈ cast (congrArg (FinRelation D) hSnapLive)
            (J (snapshotOf P X)) := by
      rw [hRightNorm]
      exact (FinRelation.mem_cast_iff hSnapLive
        (J (snapshotOf P X)) t).symm
    exact hLeft.symm.trans (hNormMem.trans hRight)

/-
  The loop guard is true exactly when not every live IDB
  agrees with its snapshot.
-/
theorem changedGuard_eval_iff_not_all_equal
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    Whiel.Guard.eval (changedGuard P) J ↔
      ¬ ∀ X : IDBSym P, X ∈ idbSymList P →
        J (idbExecSym P X) =
          (snapshotAsIDBExpr P X).eval J := by
  simp [changedGuard, andList_eval_iff,
    equalSnapshotGuard_eval_iff]

/-
  The raw equalities checked by the generated guard are
  exactly equality between the normalized live program-state
  view and the normalized snapshot-state view.
-/
theorem allRawSnapshots_eq_iff_liveState_eq_snapshotState
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    (∀ X : IDBSym P, X ∈ idbSymList P →
        J (idbExecSym P X) =
          (snapshotAsIDBExpr P X).eval J) ↔
      liveState P J = snapshotState P J := by
  constructor
  · intro hAll
    apply Instance.ext
    intro X
    by_cases hX : X ∈ P.idb
    · have hRaw :=
        hAll ⟨X, hX⟩ (mem_idbSymList P ⟨X, hX⟩)
      have hRel :=
        (rawSnapshotEq_iff_liveIDBRel_eq_snapshotIDBRel
          P ⟨X, hX⟩ J).mp hRaw
      rw [liveState_idb P J ⟨X, hX⟩]
      rw [snapshotState_idb P J ⟨X, hX⟩]
      exact hRel
    · rw [snapshotState_not_idb P J X hX]
  · intro hEq X _hMem
    apply
      (rawSnapshotEq_iff_liveIDBRel_eq_snapshotIDBRel
        P X J).mpr
    have hRel :
        liveState P J X.1 =
          snapshotState P J X.1 := by
      rw [hEq]
    rw [liveState_idb P J X] at hRel
    rw [snapshotState_idb P J X] at hRel
    exact hRel

/-
  The generated changed guard is true exactly when live and
  snapshot program-schema states differ.
-/
theorem changedGuard_eval_iff_liveState_ne_snapshotState
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    Whiel.Guard.eval (changedGuard P) J ↔
      liveState P J ≠ snapshotState P J := by
  rw [changedGuard_eval_iff_not_all_equal]
  rw [allRawSnapshots_eq_iff_liveState_eq_snapshotState]

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Sequential Command State Transformers
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  State transformer denoted by sequentially copying the
  listed live IDBs into their snapshots.
-/
def snapshotIDBsState
    (P : Program D Γ) :
    Instance D (execSchema P) →
      List (IDBSym P) → Instance D (execSchema P)
| J, [] => J
| J, X :: Xs =>
    snapshotIDBsState P
      (Instance.update J (snapshotOf P X)
        ((idbAsSnapshotExpr P X).eval J))
      Xs

/-
  State transformer denoted by sequentially applying each
  generated live-IDB update.
-/
def stepIDBsState
    (P : Program D Γ) :
    Instance D (execSchema P) →
      List (IDBSym P) → Instance D (execSchema P)
| J, [] => J
| J, X :: Xs =>
    stepIDBsState P
      (Instance.update J (idbExecSym P X)
        ((nextIDBExpr P X).eval J))
      Xs

/-
  State transformer denoted by sequentially initializing
  the listed snapshots to empty.
-/
def emptySnapshotsState
    (P : Program D Γ) :
    Instance D (execSchema P) →
      List (IDBSym P) → Instance D (execSchema P)
| J, [] => J
| J, X :: Xs =>
    emptySnapshotsState P
      (Instance.update J (snapshotOf P X)
        ((emptySnapshotExpr P X).eval J))
      Xs

/-
  State transformer denoted by sequentially applying each
  initial destructive live-IDB consequence update.
-/
def initialStepIDBsState
    (P : Program D Γ) :
    Instance D (execSchema P) →
      List (IDBSym P) → Instance D (execSchema P)
| J, [] => J
| J, X :: Xs =>
    initialStepIDBsState P
      (Instance.update J (idbExecSym P X)
        ((consequenceExpr P X).eval J))
      Xs

/-
  Copying live IDBs into snapshots does not change any live
  IDB relation.
-/
theorem snapshotIDBsState_lookup_idbExecSym
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      (snapshotIDBsState P J Xs) (idbExecSym P Y) =
        J (idbExecSym P Y)
| [] => by
    rfl
| X :: Xs => by
    have hNe :
        idbExecSym P Y ≠ snapshotOf P X :=
      (snapshotOf_ne_idbExecSym P X Y).symm
    calc
      (snapshotIDBsState P
          (Instance.update J (snapshotOf P X)
            ((idbAsSnapshotExpr P X).eval J)) Xs)
          (idbExecSym P Y)
          =
        (Instance.update J (snapshotOf P X)
          ((idbAsSnapshotExpr P X).eval J))
          (idbExecSym P Y) := by
            exact
              snapshotIDBsState_lookup_idbExecSym
                P Y
                (Instance.update J (snapshotOf P X)
                  ((idbAsSnapshotExpr P X).eval J))
                Xs
      _ = J (idbExecSym P Y) := by
            exact
              Instance.update_lookup_ne J (snapshotOf P X)
                (idbExecSym P Y) hNe
                ((idbAsSnapshotExpr P X).eval J)

/-
  Copying live IDBs into snapshots does not change any
  program-schema relation viewed in the execution schema.
-/
theorem snapshotIDBsState_lookup_progExecSym
    (P : Program D Γ)
    (Y : Γ.syms)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      (snapshotIDBsState P J Xs) (progExecSym P Y) =
        J (progExecSym P Y)
| [] => by
    rfl
| X :: Xs => by
    have hNe :
        progExecSym P Y ≠ snapshotOf P X :=
      (snapshotOf_ne_progExecSym P X Y).symm
    calc
      (snapshotIDBsState P
          (Instance.update J (snapshotOf P X)
            ((idbAsSnapshotExpr P X).eval J)) Xs)
          (progExecSym P Y)
          =
        (Instance.update J (snapshotOf P X)
          ((idbAsSnapshotExpr P X).eval J))
          (progExecSym P Y) := by
            exact
              snapshotIDBsState_lookup_progExecSym
                P Y
                (Instance.update J (snapshotOf P X)
                  ((idbAsSnapshotExpr P X).eval J))
                Xs
      _ = J (progExecSym P Y) := by
            exact
              Instance.update_lookup_ne J (snapshotOf P X)
                (progExecSym P Y) hNe
                ((idbAsSnapshotExpr P X).eval J)

/-
  Snapshot copying preserves the program-schema live-state
  view.
-/
theorem liveState_snapshotIDBsState
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (Xs : List (IDBSym P)) :
    liveState P (snapshotIDBsState P J Xs) =
      liveState P J := by
  let hExt :=
    UnnamedSchema.extensionOf_trans
      (execSchema_extension_output P)
      (UnnamedSchema.extensionOf_refl Γ)
  unfold liveState
  change
    Instance.reduct hExt (snapshotIDBsState P J Xs) =
      Instance.reduct hExt J
  apply Instance.ext
  intro X
  apply Finset.ext
  intro t
  rw [Instance.reduct_mem_iff]
  rw [Instance.reduct_mem_iff]
  have hLookup :
      (snapshotIDBsState P J Xs)
          (UnnamedSchema.symOfExtension hExt X) =
        J (UnnamedSchema.symOfExtension hExt X) := by
    simpa [hExt, progExecSym] using
      snapshotIDBsState_lookup_progExecSym P X J Xs
  rw [hLookup]

/-
  Emptying snapshots does not change any live IDB relation.
-/
theorem emptySnapshotsState_lookup_idbExecSym
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      (emptySnapshotsState P J Xs) (idbExecSym P Y) =
        J (idbExecSym P Y)
| [] => by
    rfl
| X :: Xs => by
    have hNe :
        idbExecSym P Y ≠ snapshotOf P X :=
      (snapshotOf_ne_idbExecSym P X Y).symm
    calc
      (emptySnapshotsState P
          (Instance.update J (snapshotOf P X)
            ((emptySnapshotExpr P X).eval J)) Xs)
          (idbExecSym P Y)
          =
        (Instance.update J (snapshotOf P X)
          ((emptySnapshotExpr P X).eval J))
          (idbExecSym P Y) := by
            exact
              emptySnapshotsState_lookup_idbExecSym
                P Y
                (Instance.update J (snapshotOf P X)
                  ((emptySnapshotExpr P X).eval J))
                Xs
      _ = J (idbExecSym P Y) := by
            exact
              Instance.update_lookup_ne J (snapshotOf P X)
                (idbExecSym P Y) hNe
                ((emptySnapshotExpr P X).eval J)

/-
  Emptying snapshots does not change any program-schema
  relation viewed in the execution schema.
-/
theorem emptySnapshotsState_lookup_progExecSym
    (P : Program D Γ)
    (Y : Γ.syms)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      (emptySnapshotsState P J Xs) (progExecSym P Y) =
        J (progExecSym P Y)
| [] => by
    rfl
| X :: Xs => by
    have hNe :
        progExecSym P Y ≠ snapshotOf P X :=
      (snapshotOf_ne_progExecSym P X Y).symm
    calc
      (emptySnapshotsState P
          (Instance.update J (snapshotOf P X)
            ((emptySnapshotExpr P X).eval J)) Xs)
          (progExecSym P Y)
          =
        (Instance.update J (snapshotOf P X)
          ((emptySnapshotExpr P X).eval J))
          (progExecSym P Y) := by
            exact
              emptySnapshotsState_lookup_progExecSym
                P Y
                (Instance.update J (snapshotOf P X)
                  ((emptySnapshotExpr P X).eval J))
                Xs
      _ = J (progExecSym P Y) := by
            exact
              Instance.update_lookup_ne J (snapshotOf P X)
                (progExecSym P Y) hNe
                ((emptySnapshotExpr P X).eval J)

/-
  Emptying snapshots preserves the program-schema live-state
  view.
-/
theorem liveState_emptySnapshotsState
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (Xs : List (IDBSym P)) :
    liveState P (emptySnapshotsState P J Xs) =
      liveState P J := by
  let hExt :=
    UnnamedSchema.extensionOf_trans
      (execSchema_extension_output P)
      (UnnamedSchema.extensionOf_refl Γ)
  unfold liveState
  change
    Instance.reduct hExt (emptySnapshotsState P J Xs) =
      Instance.reduct hExt J
  apply Instance.ext
  intro X
  apply Finset.ext
  intro t
  rw [Instance.reduct_mem_iff]
  rw [Instance.reduct_mem_iff]
  have hLookup :
      (emptySnapshotsState P J Xs)
          (UnnamedSchema.symOfExtension hExt X) =
        J (UnnamedSchema.symOfExtension hExt X) := by
    simpa [hExt, progExecSym] using
      emptySnapshotsState_lookup_progExecSym P X J Xs
  rw [hLookup]

/-
  Once a snapshot has been initialized to empty, later
  snapshot-emptying commands preserve that emptiness.
-/
theorem emptySnapshotsState_preserves_empty_snapshot
    (P : Program D Γ)
    (Y : IDBSym P)
    {J : Instance D (execSchema P)}
    (hJ : J (snapshotOf P Y) = ∅) :
    ∀ Xs : List (IDBSym P),
      (emptySnapshotsState P J Xs) (snapshotOf P Y) = ∅
| [] => by
    exact hJ
| X :: Xs => by
    unfold emptySnapshotsState
    by_cases hYX : snapshotOf P Y = snapshotOf P X
    · have hEq : Y = X := snapshotOf_injective P hYX
      subst hEq
      apply emptySnapshotsState_preserves_empty_snapshot
      rw [Instance.update_lookup_eq]
      exact emptySnapshotExpr_eval P Y J
    · apply emptySnapshotsState_preserves_empty_snapshot
      rw [Instance.update_lookup_ne J
        (snapshotOf P X) (snapshotOf P Y) hYX]
      exact hJ

/-
  If a snapshot is in the initialization list, the final
  snapshot relation is empty.
-/
theorem emptySnapshotsState_lookup_snapshot_of_mem
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      Y ∈ Xs →
        (emptySnapshotsState P J Xs) (snapshotOf P Y) = ∅
| [], hY => by
    cases hY
| X :: Xs, hY => by
    rcases List.mem_cons.mp hY with hEq | hTail
    · subst hEq
      unfold emptySnapshotsState
      apply emptySnapshotsState_preserves_empty_snapshot
      rw [Instance.update_lookup_eq]
      exact emptySnapshotExpr_eval P Y J
    · exact
        emptySnapshotsState_lookup_snapshot_of_mem
          P Y
          (Instance.update J (snapshotOf P X)
            ((emptySnapshotExpr P X).eval J))
          Xs hTail

/-
  Updating a snapshot with the live-IDB-as-snapshot
  expression stores exactly the live IDB relation, when both
  sides are viewed at the program-schema arity.
-/
theorem snapshotIDBRel_update_self
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P)) :
    snapshotIDBRel P
        (Instance.update J (snapshotOf P X)
          ((idbAsSnapshotExpr P X).eval J)) X =
      liveIDBRel P J X := by
  unfold snapshotIDBRel liveIDBRel
  rw [Instance.update_lookup_eq]
  rw [idbAsSnapshotExpr_eval]
  let hLiveSnap :=
    (idbExecSym_arity P X).trans
      (snapshotOf_arity P X).symm
  let hSnapProg := snapshotOf_arity P X
  let hLiveProg := idbExecSym_arity P X
  change
    cast (congrArg (FinRelation D) hSnapProg)
        (cast (congrArg (FinRelation D) hLiveSnap)
          (J (idbExecSym P X))) =
      cast (congrArg (FinRelation D) hLiveProg)
        (J (idbExecSym P X))
  calc
    cast (congrArg (FinRelation D) hSnapProg)
        (cast (congrArg (FinRelation D) hLiveSnap)
          (J (idbExecSym P X)))
        =
      cast
        (congrArg (FinRelation D)
          (hLiveSnap.trans hSnapProg))
        (J (idbExecSym P X)) :=
          FinRelation.cast_trans hLiveSnap hSnapProg
            (J (idbExecSym P X))
    _ =
      cast (congrArg (FinRelation D) hLiveProg)
        (J (idbExecSym P X)) :=
          FinRelation.cast_proof_irrel
            (hLiveSnap.trans hSnapProg) hLiveProg
            (J (idbExecSym P X))

/-
  Updating one snapshot relation does not change any other
  snapshot relation, after normalizing both to
  program-schema arities.
-/
theorem snapshotIDBRel_update_ne
    (P : Program D Γ)
    {X Y : IDBSym P}
    (hYX : Y ≠ X)
    (J : Instance D (execSchema P))
    (R : FinRelation D
      ((execSchema P).arity (snapshotOf P X))) :
    snapshotIDBRel P
        (Instance.update J (snapshotOf P X) R) Y =
      snapshotIDBRel P J Y := by
  unfold snapshotIDBRel
  have hNe : snapshotOf P Y ≠ snapshotOf P X := by
    intro hEq
    exact hYX (snapshotOf_injective P hEq)
  rw [Instance.update_lookup_ne J
    (snapshotOf P X) (snapshotOf P Y) hNe R]

/-
  Updating a snapshot relation does not change any live IDB
  relation, after normalizing the live relation to
  program-schema arity.
-/
theorem liveIDBRel_update_snapshot
    (P : Program D Γ)
    (X Y : IDBSym P)
    (J : Instance D (execSchema P))
    (R : FinRelation D
      ((execSchema P).arity (snapshotOf P X))) :
    liveIDBRel P (Instance.update J (snapshotOf P X) R) Y =
      liveIDBRel P J Y := by
  unfold liveIDBRel
  have hNe :
      idbExecSym P Y ≠ snapshotOf P X :=
    (snapshotOf_ne_idbExecSym P X Y).symm
  rw [Instance.update_lookup_ne J
    (snapshotOf P X) (idbExecSym P Y) hNe R]

/-
  Updating a live IDB and then reading that same live IDB,
  normalized to program-schema arity, returns the assigned
  relation with the corresponding arity transport.
-/
theorem liveIDBRel_update_idb_self
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P))
    (R : FinRelation D
      ((execSchema P).arity (idbExecSym P X))) :
    liveIDBRel P
        (Instance.update J (idbExecSym P X) R) X =
      cast (congrArg (FinRelation D) (idbExecSym_arity P X))
        R := by
  unfold liveIDBRel
  rw [Instance.update_lookup_eq]

/-
  Updating one live IDB does not change any other live IDB,
  after normalizing both to program-schema arities.
-/
theorem liveIDBRel_update_idb_ne
    (P : Program D Γ)
    {X Y : IDBSym P}
    (hYX : Y ≠ X)
    (J : Instance D (execSchema P))
    (R : FinRelation D
      ((execSchema P).arity (idbExecSym P X))) :
    liveIDBRel P
        (Instance.update J (idbExecSym P X) R) Y =
      liveIDBRel P J Y := by
  unfold liveIDBRel
  have hNe : idbExecSym P Y ≠ idbExecSym P X := by
    intro hEq
    exact hYX (idbExecSym_injective P hEq)
  rw [Instance.update_lookup_ne J
    (idbExecSym P X) (idbExecSym P Y) hNe R]

/-
  Updating a live IDB does not change a snapshot IDB
  relation, after normalizing the snapshot relation to
  program-schema arity.
-/
theorem snapshotIDBRel_update_liveIDB
    (P : Program D Γ)
    (X Y : IDBSym P)
    (J : Instance D (execSchema P))
    (R : FinRelation D
      ((execSchema P).arity (idbExecSym P X))) :
    snapshotIDBRel P
        (Instance.update J (idbExecSym P X) R) Y =
      snapshotIDBRel P J Y := by
  unfold snapshotIDBRel
  have hNe : snapshotOf P Y ≠ idbExecSym P X :=
    snapshotOf_ne_idbExecSym P Y X
  rw [Instance.update_lookup_ne J
    (idbExecSym P X) (snapshotOf P Y) hNe R]

/-
  Updating a live IDB does not change a non-IDB
  program-schema live-state relation.
-/
theorem liveState_update_liveIDB_not_idb
    (P : Program D Γ)
    (X : IDBSym P)
    (Y : Γ.syms)
    (hY : Y ∉ P.idb)
    (J : Instance D (execSchema P))
    (R : FinRelation D
      ((execSchema P).arity (idbExecSym P X))) :
    liveState P
        (Instance.update J (idbExecSym P X) R) Y =
      liveState P J Y := by
  let hExt :=
    UnnamedSchema.extensionOf_trans
      (execSchema_extension_output P)
      (UnnamedSchema.extensionOf_refl Γ)
  unfold liveState
  change
    Instance.reduct hExt
        (Instance.update J (idbExecSym P X) R) Y =
      Instance.reduct hExt J Y
  apply Finset.ext
  intro t
  rw [Instance.reduct_mem_iff]
  rw [Instance.reduct_mem_iff]
  have hNe :
      UnnamedSchema.symOfExtension hExt Y ≠
        idbExecSym P X := by
    simpa [hExt, progExecSym] using
      (idbExecSym_ne_progExecSym_of_not_idb P X Y hY).symm
  rw [Instance.update_lookup_ne J
    (idbExecSym P X)
    (UnnamedSchema.symOfExtension hExt Y) hNe R]

/-
  Updating any live IDB leaves the snapshot-state view
  unchanged: IDBs are read from snapshots, and non-IDBs are
  unaffected by live-IDB updates.
-/
theorem snapshotState_update_liveIDB
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P))
    (R : FinRelation D
      ((execSchema P).arity (idbExecSym P X))) :
    snapshotState P
        (Instance.update J (idbExecSym P X) R) =
      snapshotState P J := by
  apply Instance.ext
  intro Y
  by_cases hY : Y ∈ P.idb
  · rw [snapshotState_idb P
      (Instance.update J (idbExecSym P X) R) ⟨Y, hY⟩]
    rw [snapshotState_idb P J ⟨Y, hY⟩]
    exact snapshotIDBRel_update_liveIDB P X ⟨Y, hY⟩ J R
  · rw [snapshotState_not_idb P
      (Instance.update J (idbExecSym P X) R) Y hY]
    rw [snapshotState_not_idb P J Y hY]
    exact liveState_update_liveIDB_not_idb P X Y hY J R

/-
  Sequentially applying generated live-IDB step updates
  leaves the snapshot-state view fixed for the whole pass.
-/
theorem snapshotState_stepIDBsState
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      snapshotState P (stepIDBsState P J Xs) =
        snapshotState P J
| [] => by
    rfl
| X :: Xs => by
    let J' :=
      Instance.update J (idbExecSym P X)
        ((nextIDBExpr P X).eval J)
    calc
      snapshotState P (stepIDBsState P J' Xs)
          =
        snapshotState P J' := by
          exact snapshotState_stepIDBsState P J' Xs
      _ =
        snapshotState P J := by
          exact snapshotState_update_liveIDB P X J
            ((nextIDBExpr P X).eval J)

/-
  If a live IDB does not occur in a generated step list, the
  step list leaves that normalized live relation unchanged.
-/
theorem liveIDBRel_stepIDBsState_of_not_mem
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      Y ∉ Xs →
        liveIDBRel P (stepIDBsState P J Xs) Y =
          liveIDBRel P J Y
| [], _hY => by
    rfl
| X :: Xs, hY => by
    let J' :=
      Instance.update J (idbExecSym P X)
        ((nextIDBExpr P X).eval J)
    have hYX : Y ≠ X := by
      intro hEq
      exact hY (by simp [hEq])
    have hTail : Y ∉ Xs := by
      intro hMem
      exact hY (List.mem_cons_of_mem X hMem)
    calc
      liveIDBRel P (stepIDBsState P J' Xs) Y
          =
        liveIDBRel P J' Y := by
          exact liveIDBRel_stepIDBsState_of_not_mem
            P Y J' Xs hTail
      _ =
        liveIDBRel P J Y := by
          exact liveIDBRel_update_idb_ne P hYX J
            ((nextIDBExpr P X).eval J)

/-
  If a live IDB occurs in a generated step list, the final
  normalized live relation is the old live relation union
  the Datalog IDB consequence computed from the fixed
  snapshot state.
-/
theorem liveIDBRel_stepIDBsState_of_mem
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      Y ∈ Xs →
        liveIDBRel P (stepIDBsState P J Xs) Y =
          liveIDBRel P J Y ∪
            P.IDBConsequence (snapshotState P J) Y.1
| [], hY => by
    cases hY
| X :: Xs, hY => by
    let J' :=
      Instance.update J (idbExecSym P X)
        ((nextIDBExpr P X).eval J)
    have hSnap :
        snapshotState P J' = snapshotState P J := by
      exact snapshotState_update_liveIDB P X J
        ((nextIDBExpr P X).eval J)
    rcases List.mem_cons.mp hY with hEq | hTail
    · subst hEq
      have hSelf :
          liveIDBRel P J' Y = nextIDBRel P J Y := by
        unfold J' nextIDBRel
        exact liveIDBRel_update_idb_self P Y J
          ((nextIDBExpr P Y).eval J)
      by_cases hAgain : Y ∈ Xs
      · calc
          liveIDBRel P (stepIDBsState P J' Xs) Y
              =
            liveIDBRel P J' Y ∪
              P.IDBConsequence
                (snapshotState P J') Y.1 := by
              exact liveIDBRel_stepIDBsState_of_mem
                P Y J' Xs hAgain
          _ =
            nextIDBRel P J Y ∪
              P.IDBConsequence
                (snapshotState P J) Y.1 := by
              rw [hSelf, hSnap]
          _ =
            (liveIDBRel P J Y ∪
                P.IDBConsequence
                  (snapshotState P J) Y.1) ∪
              P.IDBConsequence
                (snapshotState P J) Y.1 := by
              rw [nextIDBRel_eq_live_union_IDBConsequence
                P J Y]
          _ =
            liveIDBRel P J Y ∪
              P.IDBConsequence
                (snapshotState P J) Y.1 := by
              apply Finset.ext
              intro t
              simp [Finset.mem_union]
      · calc
          liveIDBRel P (stepIDBsState P J' Xs) Y
              =
            liveIDBRel P J' Y := by
              exact liveIDBRel_stepIDBsState_of_not_mem
                P Y J' Xs hAgain
          _ =
            nextIDBRel P J Y := hSelf
          _ =
            liveIDBRel P J Y ∪
              P.IDBConsequence
                (snapshotState P J) Y.1 := by
              exact nextIDBRel_eq_live_union_IDBConsequence
                P J Y
    · by_cases hYXeq : Y = X
      · subst hYXeq
        have hSelf :
            liveIDBRel P J' Y = nextIDBRel P J Y := by
          unfold J' nextIDBRel
          exact liveIDBRel_update_idb_self P Y J
            ((nextIDBExpr P Y).eval J)
        calc
          liveIDBRel P (stepIDBsState P J' Xs) Y
              =
            liveIDBRel P J' Y ∪
              P.IDBConsequence
                (snapshotState P J') Y.1 := by
              exact liveIDBRel_stepIDBsState_of_mem
                P Y J' Xs hTail
          _ =
            nextIDBRel P J Y ∪
              P.IDBConsequence
                (snapshotState P J) Y.1 := by
              rw [hSelf, hSnap]
          _ =
            (liveIDBRel P J Y ∪
                P.IDBConsequence
                  (snapshotState P J) Y.1) ∪
              P.IDBConsequence
                (snapshotState P J) Y.1 := by
              rw [nextIDBRel_eq_live_union_IDBConsequence
                P J Y]
          _ =
            liveIDBRel P J Y ∪
              P.IDBConsequence
                (snapshotState P J) Y.1 := by
              apply Finset.ext
              intro t
              simp [Finset.mem_union]
      · calc
          liveIDBRel P (stepIDBsState P J' Xs) Y
              =
            liveIDBRel P J' Y ∪
              P.IDBConsequence
                (snapshotState P J') Y.1 := by
              exact liveIDBRel_stepIDBsState_of_mem
                P Y J' Xs hTail
          _ =
            liveIDBRel P J Y ∪
              P.IDBConsequence
                (snapshotState P J) Y.1 := by
              rw [liveIDBRel_update_idb_ne P hYXeq J
                ((nextIDBExpr P X).eval J), hSnap]

/-
  For the full generated step list, every live IDB is
  updated to old live contents union the Datalog IDB
  consequence computed from the fixed snapshot state.
-/
theorem liveIDBRel_stepIDBsState_all
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P)) :
    liveIDBRel P
        (stepIDBsState P J (idbSymList P)) X =
      liveIDBRel P J X ∪
        P.IDBConsequence (snapshotState P J) X.1 :=
  liveIDBRel_stepIDBsState_of_mem
    P X J (idbSymList P) (mem_idbSymList P X)

/-
  Sequentially applying generated live-IDB step updates
  leaves all non-IDB program-schema relations unchanged.
-/
theorem liveState_stepIDBsState_not_idb
    (P : Program D Γ)
    (X : Γ.syms)
    (hX : X ∉ P.idb)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      liveState P (stepIDBsState P J Xs) X =
        liveState P J X
| [] => by
    rfl
| Y :: Ys => by
    let J' :=
      Instance.update J (idbExecSym P Y)
        ((nextIDBExpr P Y).eval J)
    calc
      liveState P (stepIDBsState P J' Ys) X
          =
        liveState P J' X := by
          exact liveState_stepIDBsState_not_idb P X hX J' Ys
      _ =
        liveState P J X := by
          exact liveState_update_liveIDB_not_idb P Y X hX J
            ((nextIDBExpr P Y).eval J)

/-
  For the compiler's full generated step list, non-IDB
  program-schema relations are unchanged.
-/
theorem liveState_stepIDBsState_all_not_idb
    (P : Program D Γ)
    (X : Γ.syms)
    (hX : X ∉ P.idb)
    (J : Instance D (execSchema P)) :
    liveState P (stepIDBsState P J (idbSymList P)) X =
      liveState P J X :=
  liveState_stepIDBsState_not_idb P X hX J (idbSymList P)

/-
  Sequentially applying initial destructive live-IDB updates
  leaves the snapshot-state view fixed for the whole pass.
-/
theorem snapshotState_initialStepIDBsState
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      snapshotState P (initialStepIDBsState P J Xs) =
        snapshotState P J
| [] => by
    rfl
| X :: Xs => by
    let J' :=
      Instance.update J (idbExecSym P X)
        ((consequenceExpr P X).eval J)
    calc
      snapshotState P (initialStepIDBsState P J' Xs)
          =
        snapshotState P J' := by
          exact snapshotState_initialStepIDBsState P J' Xs
      _ =
        snapshotState P J := by
          exact snapshotState_update_liveIDB P X J
            ((consequenceExpr P X).eval J)

/-
  If a live IDB does not occur in an initial-step list, the
  list leaves that normalized live relation unchanged.
-/
theorem liveIDBRel_initialStepIDBsState_of_not_mem
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      Y ∉ Xs →
        liveIDBRel P (initialStepIDBsState P J Xs) Y =
          liveIDBRel P J Y
| [], _hY => by
    rfl
| X :: Xs, hY => by
    let J' :=
      Instance.update J (idbExecSym P X)
        ((consequenceExpr P X).eval J)
    have hYX : Y ≠ X := by
      intro hEq
      exact hY (by simp [hEq])
    have hTail : Y ∉ Xs := by
      intro hMem
      exact hY (List.mem_cons_of_mem X hMem)
    calc
      liveIDBRel P (initialStepIDBsState P J' Xs) Y
          =
        liveIDBRel P J' Y := by
          exact liveIDBRel_initialStepIDBsState_of_not_mem
            P Y J' Xs hTail
      _ =
        liveIDBRel P J Y := by
          exact liveIDBRel_update_idb_ne P hYX J
            ((consequenceExpr P X).eval J)

/-
  If a live IDB occurs in an initial-step list, the final
  normalized live relation is the Datalog IDB consequence
  computed from the fixed snapshot state.
-/
theorem liveIDBRel_initialStepIDBsState_of_mem
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      Y ∈ Xs →
        liveIDBRel P (initialStepIDBsState P J Xs) Y =
          P.IDBConsequence (snapshotState P J) Y.1
| [], hY => by
    cases hY
| X :: Xs, hY => by
    let J' :=
      Instance.update J (idbExecSym P X)
        ((consequenceExpr P X).eval J)
    have hSnap :
        snapshotState P J' = snapshotState P J := by
      exact snapshotState_update_liveIDB P X J
        ((consequenceExpr P X).eval J)
    rcases List.mem_cons.mp hY with hEq | hTail
    · subst hEq
      have hSelf :
          liveIDBRel P J' Y = consequenceRel P J Y := by
        unfold J' consequenceRel
        exact liveIDBRel_update_idb_self P Y J
          ((consequenceExpr P Y).eval J)
      by_cases hAgain : Y ∈ Xs
      · calc
          liveIDBRel P (initialStepIDBsState P J' Xs) Y
              =
            P.IDBConsequence (snapshotState P J') Y.1 := by
              exact liveIDBRel_initialStepIDBsState_of_mem
                P Y J' Xs hAgain
          _ =
            P.IDBConsequence (snapshotState P J) Y.1 := by
              rw [hSnap]
      · calc
          liveIDBRel P (initialStepIDBsState P J' Xs) Y
              =
            liveIDBRel P J' Y := by
              exact liveIDBRel_initialStepIDBsState_of_not_mem
                P Y J' Xs hAgain
          _ =
            consequenceRel P J Y := hSelf
          _ =
            P.IDBConsequence (snapshotState P J) Y.1 := by
              exact consequenceRel_eq_IDBConsequence P J Y
    · by_cases hYXeq : Y = X
      · subst hYXeq
        calc
          liveIDBRel P (initialStepIDBsState P J' Xs) Y
              =
            P.IDBConsequence (snapshotState P J') Y.1 := by
              exact liveIDBRel_initialStepIDBsState_of_mem
                P Y J' Xs hTail
          _ =
            P.IDBConsequence (snapshotState P J) Y.1 := by
              rw [hSnap]
      · calc
          liveIDBRel P (initialStepIDBsState P J' Xs) Y
              =
            P.IDBConsequence (snapshotState P J') Y.1 := by
              exact liveIDBRel_initialStepIDBsState_of_mem
                P Y J' Xs hTail
          _ =
            P.IDBConsequence (snapshotState P J) Y.1 := by
              rw [hSnap]

/-
  For the compiler's full initial-step list, every live IDB
  is destructively assigned the Datalog IDB consequence
  computed from the fixed snapshot state.
-/
theorem liveIDBRel_initialStepIDBsState_all
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P)) :
    liveIDBRel P
        (initialStepIDBsState P J (idbSymList P)) X =
      P.IDBConsequence (snapshotState P J) X.1 :=
  liveIDBRel_initialStepIDBsState_of_mem
    P X J (idbSymList P) (mem_idbSymList P X)

/-
  Sequentially applying initial destructive live-IDB updates
  leaves all non-IDB program-schema relations unchanged.
-/
theorem liveState_initialStepIDBsState_not_idb
    (P : Program D Γ)
    (X : Γ.syms)
    (hX : X ∉ P.idb)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      liveState P (initialStepIDBsState P J Xs) X =
        liveState P J X
| [] => by
    rfl
| Y :: Ys => by
    let J' :=
      Instance.update J (idbExecSym P Y)
        ((consequenceExpr P Y).eval J)
    calc
      liveState P (initialStepIDBsState P J' Ys) X
          =
        liveState P J' X := by
          exact liveState_initialStepIDBsState_not_idb
            P X hX J' Ys
      _ =
        liveState P J X := by
          exact liveState_update_liveIDB_not_idb P Y X hX J
            ((consequenceExpr P Y).eval J)

/-
  For the compiler's full initial-step list, non-IDB
  program-schema relations are unchanged.
-/
theorem liveState_initialStepIDBsState_all_not_idb
    (P : Program D Γ)
    (X : Γ.syms)
    (hX : X ∉ P.idb)
    (J : Instance D (execSchema P)) :
    liveState P (initialStepIDBsState P J (idbSymList P)) X =
      liveState P J X :=
  liveState_initialStepIDBsState_not_idb
    P X hX J (idbSymList P)

/-
  Snapshot copying preserves every live IDB relation when
  viewed at program-schema arity.
-/
theorem liveIDBRel_snapshotIDBsState
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P))
    (Xs : List (IDBSym P)) :
    liveIDBRel P (snapshotIDBsState P J Xs) Y =
      liveIDBRel P J Y := by
  unfold liveIDBRel
  rw [snapshotIDBsState_lookup_idbExecSym]

/-
  If an IDB is not in the snapshot-copy list, its normalized
  snapshot relation is unchanged.
-/
theorem snapshotIDBRel_snapshotIDBsState_of_not_mem
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      Y ∉ Xs →
        snapshotIDBRel P (snapshotIDBsState P J Xs) Y =
          snapshotIDBRel P J Y
| [], _hY => by
    rfl
| X :: Xs, hY => by
    have hYX : Y ≠ X := by
      intro hEq
      exact hY (by simp [hEq])
    have hTail : Y ∉ Xs := by
      intro hMem
      exact hY (List.mem_cons_of_mem X hMem)
    calc
      snapshotIDBRel P
          (snapshotIDBsState P
            (Instance.update J (snapshotOf P X)
              ((idbAsSnapshotExpr P X).eval J)) Xs) Y
          =
        snapshotIDBRel P
          (Instance.update J (snapshotOf P X)
            ((idbAsSnapshotExpr P X).eval J)) Y := by
            exact
              snapshotIDBRel_snapshotIDBsState_of_not_mem
                P Y
                (Instance.update J (snapshotOf P X)
                  ((idbAsSnapshotExpr P X).eval J))
                Xs hTail
      _ = snapshotIDBRel P J Y := by
            exact
              snapshotIDBRel_update_ne P hYX J
                ((idbAsSnapshotExpr P X).eval J)

/-
  If an IDB is in the snapshot-copy list, its normalized
  snapshot relation after copying is the original live IDB
  relation.
-/
theorem snapshotIDBRel_snapshotIDBsState_of_mem
    (P : Program D Γ)
    (Y : IDBSym P)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      Y ∈ Xs →
        snapshotIDBRel P (snapshotIDBsState P J Xs) Y =
          liveIDBRel P J Y
| [], hY => by
    cases hY
| X :: Xs, hY => by
    let J' :=
      Instance.update J (snapshotOf P X)
        ((idbAsSnapshotExpr P X).eval J)
    rcases List.mem_cons.mp hY with hEq | hTail
    · subst hEq
      by_cases hAgain : Y ∈ Xs
      · calc
          snapshotIDBRel P (snapshotIDBsState P J' Xs) Y
              =
            liveIDBRel P J' Y := by
              exact
                snapshotIDBRel_snapshotIDBsState_of_mem
                  P Y J' Xs hAgain
          _ = liveIDBRel P J Y := by
              exact
                liveIDBRel_update_snapshot P Y Y J
                  ((idbAsSnapshotExpr P Y).eval J)
      · calc
          snapshotIDBRel P (snapshotIDBsState P J' Xs) Y
              =
            snapshotIDBRel P J' Y := by
              exact
                snapshotIDBRel_snapshotIDBsState_of_not_mem
                  P Y J' Xs hAgain
          _ = liveIDBRel P J Y := by
              exact snapshotIDBRel_update_self P Y J
    · calc
        snapshotIDBRel P (snapshotIDBsState P J' Xs) Y
            =
          liveIDBRel P J' Y := by
            exact
              snapshotIDBRel_snapshotIDBsState_of_mem
                P Y J' Xs hTail
        _ = liveIDBRel P J Y := by
            exact
              liveIDBRel_update_snapshot P X Y J
                ((idbAsSnapshotExpr P X).eval J)

/-
  After the generated snapshot command has copied every IDB,
  the snapshot-state IDB view contains the previous live IDB
  relation.
-/
theorem snapshotState_snapshotIDBsState_idb
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (X : IDBSym P) :
    snapshotState P
        (snapshotIDBsState P J (idbSymList P)) X.1 =
      liveIDBRel P J X := by
  rw [snapshotState_idb]
  exact
    snapshotIDBRel_snapshotIDBsState_of_mem
      P X J (idbSymList P) (mem_idbSymList P X)

/-
  After the generated snapshot command has copied every IDB,
  the snapshot-state non-IDB view remains the previous live
  program-schema relation.
-/
theorem snapshotState_snapshotIDBsState_not_idb
    (P : Program D Γ)
    (J : Instance D (execSchema P))
    (X : Γ.syms)
    (hX : X ∉ P.idb) :
    snapshotState P
        (snapshotIDBsState P J (idbSymList P)) X =
      liveState P J X := by
  rw [snapshotState_not_idb P
    (snapshotIDBsState P J (idbSymList P)) X hX]
  rw [liveState_snapshotIDBsState]

/-
  After the generated snapshot command has copied every IDB,
  the snapshot-state view is exactly the previous live
  program-schema state.
-/
theorem snapshotState_snapshotIDBsState_eq_liveState
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    snapshotState P
        (snapshotIDBsState P J (idbSymList P)) =
      liveState P J := by
  apply Instance.ext
  intro X
  by_cases hX : X ∈ P.idb
  · rw [snapshotState_snapshotIDBsState_idb
      P J ⟨X, hX⟩]
    rw [liveState_idb P J ⟨X, hX⟩]
  · exact snapshotState_snapshotIDBsState_not_idb P J X hX

/-
  One generated naive iteration, ignoring WHIEL command
  syntax, maps the live program-schema state to the Datalog
  cumulative immediate consequence operator.
-/
theorem liveState_iterationState_immediate
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    liveState P
        (stepIDBsState P
          (snapshotIDBsState P J (idbSymList P))
          (idbSymList P)) =
      P.immediate (liveState P J) := by
  let Jsnap := snapshotIDBsState P J (idbSymList P)
  have hSnap :
      snapshotState P Jsnap = liveState P J := by
    simpa [Jsnap] using
      snapshotState_snapshotIDBsState_eq_liveState P J
  apply Instance.ext
  intro X
  by_cases hX : X ∈ P.idb
  · have hStep :=
      liveIDBRel_stepIDBsState_all
        P ⟨X, hX⟩ Jsnap
    rw [liveState_idb P
      (stepIDBsState P Jsnap (idbSymList P)) ⟨X, hX⟩]
    rw [hStep]
    rw [liveIDBRel_snapshotIDBsState]
    rw [← liveState_idb P J ⟨X, hX⟩]
    rw [hSnap]
    simp [Program.immediate, Program.immediateOn,
      Program.IDBConsequence, hX]
  · rw [liveState_stepIDBsState_all_not_idb P X hX Jsnap]
    rw [liveState_snapshotIDBsState P J (idbSymList P)]
    exact
      (P.immediate_preserves_edb
        (liveState P J) X hX).symm

/-
  Datalog's initial program-schema instance has empty IDB
  relations.
-/
theorem initial_idb_eq_empty
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (X : IDBSym P) :
    P.initial I X.1 = ∅ := by
  have hNotEdb : X.1.1 ∉ P.edbSchema.syms := by
    intro hEdb
    have hEdbName : X.1.1 ∈ P.edbNames := hEdb
    have hIdbName : X.1.1 ∈ P.idbNames :=
      Finset.mem_image.mpr ⟨X.1, X.2, rfl⟩
    exact
      (Finset.disjoint_left.mp P.disjoint_edb_idb)
        hEdbName hIdbName
  simpa [Program.initial] using
    Instance.expandEmpty_eq_empty_of_not_mem
      P.ambient_extension_edbSchema I X.1 hNotEdb

/-
  The generated program's empty-expanded execution input has
  the same program-schema live view as Datalog's empty-IDB
  initial instance.
-/
theorem liveState_initialInstance_initial
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    liveState P
        ((P.toWhielProgram).initialInstance I) =
      P.initial I := by
  apply Instance.ext
  intro X
  by_cases hX : X ∈ P.idb
  · rw [liveState_idb P
      ((P.toWhielProgram).initialInstance I)
      ⟨X, hX⟩]
    rw [initial_idb_eq_empty P I ⟨X, hX⟩]
    unfold liveIDBRel
    have hNotEdb : X.1 ∉ P.edbSchema.syms := by
      intro hEdb
      have hEdbName : X.1 ∈ P.edbNames := hEdb
      have hIdbName : X.1 ∈ P.idbNames :=
        Finset.mem_image.mpr ⟨X, hX, rfl⟩
      exact
        (Finset.disjoint_left.mp P.disjoint_edb_idb)
          hEdbName hIdbName
    have hExecEmpty :
        ((P.toWhielProgram).initialInstance I)
            (idbExecSym P ⟨X, hX⟩) = ∅ := by
      unfold Whiel.Program.initialInstance
        Program.toWhielProgram
      exact
        Instance.expandEmpty_eq_empty_of_not_mem
          (execSchema_extension_input P) I
          (idbExecSym P ⟨X, hX⟩) hNotEdb
    rw [hExecEmpty]
    apply Finset.ext
    intro t
    rw [FinRelation.mem_cast_iff
      (idbExecSym_arity P ⟨X, hX⟩)]
    constructor <;> intro hMem
    · exact False.elim (Finset.notMem_empty _ hMem)
    · exact False.elim (Finset.notMem_empty _ hMem)
  · apply Finset.ext
    intro t
    have hNotIdbName : X.1 ∉ P.idbNames := by
      intro hName
      rcases Finset.mem_image.mp hName with
        ⟨Y, hY, hRaw⟩
      have hYX : Y = X := Subtype.ext hRaw
      subst hYX
      exact hX hY
    have hEdb : X.1 ∈ P.edbSchema.syms :=
      P.edbName_of_schema_not_idbName X.2 hNotIdbName
    unfold liveState
    rw [Instance.reduct_mem_iff]
    unfold Whiel.Program.initialInstance
      Program.toWhielProgram
    rw [Instance.expandEmpty_mem_iff_of_mem
      (execSchema_extension_input P)
      I
      (UnnamedSchema.symOfExtension
        (UnnamedSchema.extensionOf_trans
          (execSchema_extension_output P)
          (UnnamedSchema.extensionOf_refl Γ)) X)
      hEdb]
    unfold Program.initial
    rw [Instance.expandEmpty_mem_iff_of_mem
      P.ambient_extension_edbSchema
      I X hEdb]
    let hProgExec :=
      UnnamedSchema.arity_eq_of_extensionOf
        (UnnamedSchema.extensionOf_trans
          (execSchema_extension_output P)
          (UnnamedSchema.extensionOf_refl Γ)) X
    let hExecInput :=
      UnnamedSchema.arity_eq_of_extension_mem
        (execSchema_extension_input P)
        (UnnamedSchema.symOfExtension
          (UnnamedSchema.extensionOf_trans
            (execSchema_extension_output P)
            (UnnamedSchema.extensionOf_refl Γ)) X)
        hEdb
    let hEdbProg :=
      UnnamedSchema.arity_eq_of_extension_mem
        P.ambient_extension_edbSchema X hEdb
    let lhs : Tuple D
        (P.edbSchema.arity ⟨X.1, hEdb⟩) :=
      Tuple.castArity hExecInput
        (Tuple.castArity hProgExec t)
    change
      lhs ∈ I ⟨X.1, hEdb⟩ ↔
        Tuple.castArity hEdbProg t ∈ I ⟨X.1, hEdb⟩
    have hTuple :
        lhs = Tuple.castArity hEdbProg t := by
      dsimp [lhs]
      calc
        Tuple.castArity hExecInput
            (Tuple.castArity hProgExec t)
            =
          Tuple.castArity (hExecInput.trans hProgExec) t :=
            Tuple.castArity_trans hExecInput hProgExec t
        _ =
          Tuple.castArity hEdbProg t :=
            Tuple.castArity_proof_irrel
              (hExecInput.trans hProgExec)
              hEdbProg t
    rw [hTuple]

/-
  Emptying every generated snapshot in the generated
  program's initial execution state makes the snapshot-state
  view equal to Datalog's empty-IDB initial instance.
-/
theorem snapshotState_emptySnapshotsState_initial
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    snapshotState P
        (emptySnapshotsState P
          ((P.toWhielProgram).initialInstance I)
          (idbSymList P)) =
      P.initial I := by
  apply Instance.ext
  intro X
  by_cases hX : X ∈ P.idb
  · rw [snapshotState_idb P
      (emptySnapshotsState P
        ((P.toWhielProgram).initialInstance I)
        (idbSymList P)) ⟨X, hX⟩]
    rw [initial_idb_eq_empty P I ⟨X, hX⟩]
    unfold snapshotIDBRel
    rw [emptySnapshotsState_lookup_snapshot_of_mem
      P ⟨X, hX⟩
      ((P.toWhielProgram).initialInstance I)
      (idbSymList P)
      (mem_idbSymList P ⟨X, hX⟩)]
    apply Finset.ext
    intro t
    rw [FinRelation.mem_cast_iff
      (snapshotOf_arity P ⟨X, hX⟩)]
    constructor <;> intro hMem
    · exact False.elim (Finset.notMem_empty _ hMem)
    · exact False.elim (Finset.notMem_empty _ hMem)
  · rw [snapshotState_not_idb P
      (emptySnapshotsState P
        ((P.toWhielProgram).initialInstance I)
        (idbSymList P)) X hX]
    have hLiveEmpty :=
      liveState_emptySnapshotsState P
        ((P.toWhielProgram).initialInstance I)
        (idbSymList P)
    rw [hLiveEmpty]
    rw [liveState_initialInstance_initial P I]

/-
  Emptying snapshots preserves the generated program's
  initial live view.
-/
theorem liveState_emptySnapshotsState_initial
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    liveState P
        (emptySnapshotsState P
          ((P.toWhielProgram).initialInstance I)
          (idbSymList P)) =
      P.initial I := by
  rw [liveState_emptySnapshotsState]
  exact liveState_initialInstance_initial P I

/-
  If an execution state has both live and snapshot views
  equal to Datalog's initial instance, the destructive
  initial step reaches the first Datalog immediate-
  consequence state.
-/
theorem liveState_initialStepIDBsState_immediate_initial
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D (execSchema P))
    (hSnap : snapshotState P J = P.initial I)
    (hLive : liveState P J = P.initial I) :
    liveState P
        (initialStepIDBsState P J (idbSymList P)) =
      P.immediate (P.initial I) := by
  apply Instance.ext
  intro X
  by_cases hX : X ∈ P.idb
  · rw [liveState_idb P
      (initialStepIDBsState P J (idbSymList P))
      ⟨X, hX⟩]
    rw [liveIDBRel_initialStepIDBsState_all
      P ⟨X, hX⟩ J]
    rw [hSnap]
    rw [Program.immediate, Program.immediateOn]
    simp [hX, Program.IDBConsequence,
      initial_idb_eq_empty P I ⟨X, hX⟩]
  · rw [liveState_initialStepIDBsState_all_not_idb
      P X hX J]
    rw [hLive]
    simp [Program.immediate, Program.immediateOn, hX]

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Generated Command BigStep Facts
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Semantics of one generated snapshot-copy assignment. -/
theorem snapshotIDBCmd_bigStep
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P)) :
    Whiel.Cmd.BigStep (snapshotIDBCmd P X) J
      (Instance.update J (snapshotOf P X)
        ((idbAsSnapshotExpr P X).eval J)) := by
  simp [snapshotIDBCmd, Whiel.Cmd.bigStep_assign_iff]

/- Semantics of one generated snapshot-empty assignment. -/
theorem emptySnapshotIDBCmd_bigStep
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P)) :
    Whiel.Cmd.BigStep (emptySnapshotIDBCmd P X) J
      (Instance.update J (snapshotOf P X)
        ((emptySnapshotExpr P X).eval J)) := by
  simp [emptySnapshotIDBCmd, Whiel.Cmd.bigStep_assign_iff]

/- Semantics of one generated live-IDB step assignment. -/
theorem stepIDBCmd_bigStep
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P)) :
    Whiel.Cmd.BigStep (stepIDBCmd P X) J
      (Instance.update J (idbExecSym P X)
        ((nextIDBExpr P X).eval J)) := by
  simp [stepIDBCmd, Whiel.Cmd.bigStep_assign_iff]

/-
  Semantics of one generated initial live-IDB step
  assignment.
-/
theorem initialStepIDBCmd_bigStep
    (P : Program D Γ)
    (X : IDBSym P)
    (J : Instance D (execSchema P)) :
    Whiel.Cmd.BigStep (initialStepIDBCmd P X) J
      (Instance.update J (idbExecSym P X)
        ((consequenceExpr P X).eval J)) := by
  simp [initialStepIDBCmd, Whiel.Cmd.bigStep_assign_iff]

theorem snapshotIDBsCmds_bigStep
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      Whiel.Cmd.BigStep
        (seqList (Xs.map (snapshotIDBCmd P)))
        J
        (snapshotIDBsState P J Xs)
| [] => by
    simpa [snapshotIDBsState] using
      (seqList_nil_bigStep (D := D) J)
| X :: Xs => by
    have hHead := snapshotIDBCmd_bigStep P X J
    have hTail :=
      snapshotIDBsCmds_bigStep P
        (Instance.update J (snapshotOf P X)
          ((idbAsSnapshotExpr P X).eval J))
        Xs
    simpa [snapshotIDBsState] using
      seqList_cons_bigStep hHead hTail

theorem emptySnapshotsCmds_bigStep
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      Whiel.Cmd.BigStep
        (seqList (Xs.map (emptySnapshotIDBCmd P)))
        J
        (emptySnapshotsState P J Xs)
| [] => by
    simpa [emptySnapshotsState] using
      (seqList_nil_bigStep (D := D) J)
| X :: Xs => by
    have hHead := emptySnapshotIDBCmd_bigStep P X J
    have hTail :=
      emptySnapshotsCmds_bigStep P
        (Instance.update J (snapshotOf P X)
          ((emptySnapshotExpr P X).eval J))
        Xs
    simpa [emptySnapshotsState] using
      seqList_cons_bigStep hHead hTail

theorem stepIDBsCmds_bigStep
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      Whiel.Cmd.BigStep
        (seqList (Xs.map (stepIDBCmd P)))
        J
        (stepIDBsState P J Xs)
| [] => by
    simpa [stepIDBsState] using
      (seqList_nil_bigStep (D := D) J)
| X :: Xs => by
    have hHead := stepIDBCmd_bigStep P X J
    have hTail :=
      stepIDBsCmds_bigStep P
        (Instance.update J (idbExecSym P X)
          ((nextIDBExpr P X).eval J))
        Xs
    simpa [stepIDBsState] using
      seqList_cons_bigStep hHead hTail

theorem initialStepIDBsCmds_bigStep
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    ∀ Xs : List (IDBSym P),
      Whiel.Cmd.BigStep
        (seqList (Xs.map (initialStepIDBCmd P)))
        J
        (initialStepIDBsState P J Xs)
| [] => by
    simpa [initialStepIDBsState] using
      (seqList_nil_bigStep (D := D) J)
| X :: Xs => by
    have hHead := initialStepIDBCmd_bigStep P X J
    have hTail :=
      initialStepIDBsCmds_bigStep P
        (Instance.update J (idbExecSym P X)
          ((consequenceExpr P X).eval J))
        Xs
    simpa [initialStepIDBsState] using
      seqList_cons_bigStep hHead hTail

theorem snapshotCmd_bigStep_state
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    Whiel.Cmd.BigStep (snapshotCmd P) J
      (snapshotIDBsState P J (idbSymList P)) := by
  simpa [snapshotCmd] using
    snapshotIDBsCmds_bigStep P J (idbSymList P)

theorem emptySnapshotsCmd_bigStep_state
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    Whiel.Cmd.BigStep (emptySnapshotsCmd P) J
      (emptySnapshotsState P J (idbSymList P)) := by
  simpa [emptySnapshotsCmd] using
    emptySnapshotsCmds_bigStep P J (idbSymList P)

theorem stepCmd_bigStep_state
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    Whiel.Cmd.BigStep (stepCmd P) J
      (stepIDBsState P J (idbSymList P)) := by
  simpa [stepCmd] using
    stepIDBsCmds_bigStep P J (idbSymList P)

theorem initialStepCmd_bigStep_state
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    Whiel.Cmd.BigStep (initialStepCmd P) J
      (initialStepIDBsState P J (idbSymList P)) := by
  simpa [initialStepCmd] using
    initialStepIDBsCmds_bigStep P J (idbSymList P)

theorem iterationCmd_bigStep_state
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    Whiel.Cmd.BigStep (iterationCmd P) J
      (stepIDBsState P
        (snapshotIDBsState P J (idbSymList P))
        (idbSymList P)) := by
  have hSnap := snapshotCmd_bigStep_state P J
  have hStep :=
    stepCmd_bigStep_state P
      (snapshotIDBsState P J (idbSymList P))
  simpa [iterationCmd, snapshotCmd, stepCmd] using
    Datalog.WhielCompiler.seqList_append_bigStep hSnap hStep

/-
  Loop correctness after the mandatory first iteration.

  The state `J` is assumed to have snapshots equal to `K`
  and live relations equal to `immediate K`. Under the same
  fuel bound used by operational semantics, the generated
  `while` loop reaches the corresponding `iterateUntilFixed`
  state.
-/
theorem whileCmd_bigStep_iterateUntilFixed_from_iteration
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    ∀ n : Nat,
      ∀ K : Instance D Γ,
        ∀ J : Instance D (execSchema P),
          Instance.BoundedByValues (P.adom I) K →
            P.remainingCapacity (P.adom I) K < n + 1 →
              snapshotState P J = K →
                liveState P J = P.immediate K →
                  ∃ J' : Instance D (execSchema P),
                    Whiel.Cmd.BigStep
                      (.while (changedGuard P)
                        (iterationCmd P)) J J' ∧
                      liveState P J' =
                        P.iterateUntilFixed (P.adom I)
                          (n + 1) K
| 0, K, J, hBound, hFuel, hSnap, hLive => by
    have hInputEq :
        P.immediateOnInputAdom I K = P.immediate K :=
      P.immediateOnInputAdom_eq_immediate (I := I) K hBound
    have hOnEq :
        P.immediateOn (P.adom I) K = P.immediate K := by
      simpa [Program.immediateOnInputAdom] using hInputEq
    by_cases hFixed : P.immediate K = K
    · have hNoGuard :
          ¬ Whiel.Guard.eval (changedGuard P) J := by
        rw
          [changedGuard_eval_iff_liveState_ne_snapshotState]
        intro hNe
        apply hNe
        calc
          liveState P J = P.immediate K := hLive
          _ = K := hFixed
          _ = snapshotState P J := hSnap.symm
      refine
        ⟨J, Whiel.Cmd.BigStep.while_false hNoGuard, ?_⟩
      have hFixedOn :
          P.immediateOn (P.adom I) K = K := by
        exact hOnEq.trans hFixed
      simp [Program.iterateUntilFixed, hFixedOn,
        hLive, hFixed]
    · have hNotFixedOn :
          P.immediateOn (P.adom I) K ≠ K := by
        intro hOn
        apply hFixed
        rw [← hOnEq]
        exact hOn
      have hDecrease :
          P.remainingCapacity (P.adom I) (P.immediate K) <
            P.remainingCapacity (P.adom I) K := by
        simpa [hOnEq] using
          P.remainingCapacity_decreases_of_immediateOn_ne
            (P.adom I) K hBound hNotFixedOn
      have hRemZero :
          P.remainingCapacity (P.adom I) K = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hFuel)
      rw [hRemZero] at hDecrease
      exact False.elim (Nat.not_lt_zero _ hDecrease)
| n + 1, K, J, hBound, hFuel, hSnap, hLive => by
    have hInputEq :
        P.immediateOnInputAdom I K = P.immediate K :=
      P.immediateOnInputAdom_eq_immediate (I := I) K hBound
    have hOnEq :
        P.immediateOn (P.adom I) K = P.immediate K := by
      simpa [Program.immediateOnInputAdom] using hInputEq
    by_cases hFixed : P.immediate K = K
    · have hNoGuard :
          ¬ Whiel.Guard.eval (changedGuard P) J := by
        rw
          [changedGuard_eval_iff_liveState_ne_snapshotState]
        intro hNe
        apply hNe
        calc
          liveState P J = P.immediate K := hLive
          _ = K := hFixed
          _ = snapshotState P J := hSnap.symm
      refine
        ⟨J, Whiel.Cmd.BigStep.while_false hNoGuard, ?_⟩
      have hFixedOn :
          P.immediateOn (P.adom I) K = K := by
        exact hOnEq.trans hFixed
      simp [Program.iterateUntilFixed, hFixedOn,
        hLive, hFixed]
    · have hGuard :
          Whiel.Guard.eval (changedGuard P) J := by
        rw
          [changedGuard_eval_iff_liveState_ne_snapshotState]
        intro hEq
        apply hFixed
        calc
          P.immediate K = liveState P J := hLive.symm
          _ = snapshotState P J := hEq
          _ = K := hSnap
      let Jnext :=
        stepIDBsState P
          (snapshotIDBsState P J (idbSymList P))
          (idbSymList P)
      have hStep :
          Whiel.Cmd.BigStep (iterationCmd P) J Jnext := by
        exact iterationCmd_bigStep_state P J
      have hSnapK :
          snapshotState P Jnext = P.immediate K := by
        dsimp [Jnext]
        calc
          snapshotState P
              (stepIDBsState P
                (snapshotIDBsState P J (idbSymList P))
                (idbSymList P))
              =
            snapshotState P
              (snapshotIDBsState P J (idbSymList P)) := by
              exact snapshotState_stepIDBsState P
                (snapshotIDBsState P J (idbSymList P))
                (idbSymList P)
          _ = liveState P J := by
              exact
                snapshotState_snapshotIDBsState_eq_liveState
                P J
          _ = P.immediate K := hLive
      have hLiveK :
          liveState P Jnext =
            P.immediate (P.immediate K) := by
        dsimp [Jnext]
        calc
          liveState P
              (stepIDBsState P
                (snapshotIDBsState P J (idbSymList P))
              (idbSymList P))
              =
            P.immediate (liveState P J) := by
              exact liveState_iterationState_immediate P J
          _ = P.immediate (P.immediate K) := by
              rw [hLive]
      have hBoundNext :
          Instance.BoundedByValues (P.adom I)
            (P.immediate K) := by
        have hBoundOn :=
          P.immediateOnInputAdom_preserves_boundedByValues
            I hBound
        simpa [hInputEq] using hBoundOn
      have hNotFixedOn :
          P.immediateOn (P.adom I) K ≠ K := by
        intro hOn
        apply hFixed
        rw [← hOnEq]
        exact hOn
      have hDecrease :
          P.remainingCapacity (P.adom I) (P.immediate K) <
            P.remainingCapacity (P.adom I) K := by
        simpa [hOnEq] using
          P.remainingCapacity_decreases_of_immediateOn_ne
            (P.adom I) K hBound hNotFixedOn
      have hFuelLe :
          P.remainingCapacity (P.adom I) K ≤ n + 1 :=
        Nat.le_of_lt_succ hFuel
      have hSuccLe :
          P.remainingCapacity (P.adom I)
              (P.immediate K) + 1 ≤
            P.remainingCapacity (P.adom I) K :=
        Nat.succ_le_of_lt hDecrease
      have hFuelNext :
          P.remainingCapacity (P.adom I) (P.immediate K) <
            n + 1 :=
        Nat.lt_of_succ_le (hSuccLe.trans hFuelLe)
      rcases
          whileCmd_bigStep_iterateUntilFixed_from_iteration
            P I n (P.immediate K) Jnext hBoundNext
            hFuelNext hSnapK hLiveK with
        ⟨J', hLoop, hFinal⟩
      refine
        ⟨J',
          Whiel.Cmd.BigStep.while_true hGuard hStep hLoop,
          ?_⟩
      rw [Program.iterateUntilFixed]
      rw [if_neg hNotFixedOn]
      rw [hOnEq]
      exact hFinal

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Observation Support
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The observed program-schema state is exactly `liveState`.
-/
theorem reduct_observe_eq_liveState
    (P : Program D Γ)
    (J : Instance D (execSchema P)) :
    Instance.reduct (UnnamedSchema.extensionOf_refl Γ)
        ((P.toWhielProgram).observe J) =
      liveState P J := by
  unfold Whiel.Program.observe Program.toWhielProgram liveState
  exact
    Instance.reduct_trans
      (execSchema_extension_output P)
      (UnnamedSchema.extensionOf_refl Γ)
      J

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Internal Command Correctness
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The generated command reaches the operational fixed point
  observationally. The internal final execution state may
  contain arbitrary hidden snapshot relations; only its
  program-schema observation matters here.
-/
theorem toWhielCmd_bigStep_LFP_reduct
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    ∃ J : Instance D (execSchema P),
      (P.toWhielCmd).BigStep (initialInstance P I) J ∧
        reductToProgramSchema P J = P.LFP I := by
  let J₀ : Instance D (execSchema P) :=
    initialInstance P I
  let Jsnap : Instance D (execSchema P) :=
    emptySnapshotsState P J₀ (idbSymList P)
  let Jfirst : Instance D (execSchema P) :=
    initialStepIDBsState P Jsnap (idbSymList P)
  have hEmpty :
      Whiel.Cmd.BigStep (emptySnapshotsCmd P) J₀ Jsnap := by
    dsimp [Jsnap, J₀]
    exact emptySnapshotsCmd_bigStep_state P
      (initialInstance P I)
  have hInitStep :
      Whiel.Cmd.BigStep (initialStepCmd P) Jsnap Jfirst := by
    dsimp [Jfirst]
    exact initialStepCmd_bigStep_state P Jsnap
  have hSnapInitial :
      snapshotState P Jsnap = P.initial I := by
    dsimp [Jsnap, J₀]
    exact snapshotState_emptySnapshotsState_initial P I
  have hLiveInitial :
      liveState P Jsnap = P.initial I := by
    dsimp [Jsnap, J₀]
    exact liveState_emptySnapshotsState_initial P I
  have hFirstSnap :
      snapshotState P Jfirst = P.initial I := by
    dsimp [Jfirst]
    calc
      snapshotState P
          (initialStepIDBsState P Jsnap (idbSymList P))
          =
        snapshotState P Jsnap := by
          exact snapshotState_initialStepIDBsState
            P Jsnap (idbSymList P)
      _ = P.initial I := hSnapInitial
  have hFirstLive :
      liveState P Jfirst =
        P.immediate (P.initial I) := by
    dsimp [Jfirst]
    exact
      liveState_initialStepIDBsState_immediate_initial
        P I Jsnap hSnapInitial hLiveInitial
  have hBoundInitial :
      Instance.BoundedByValues (P.adom I)
        (P.initial I) :=
    P.initial_boundedByValues I
  have hFuel :
      P.remainingCapacity (P.adom I) (P.initial I) <
        P.remainingCapacity (P.adom I) (P.initial I) + 1 :=
    Nat.lt_succ_self _
  rcases
      whileCmd_bigStep_iterateUntilFixed_from_iteration
        P I
        (P.remainingCapacity (P.adom I) (P.initial I))
        (P.initial I) Jfirst hBoundInitial hFuel
        hFirstSnap hFirstLive with
    ⟨Jfinal, hLoop, hFinalLiveIter⟩
  have hCmd :
      (P.toWhielCmd).BigStep J₀ Jfinal := by
    have hLoopList :
        Whiel.Cmd.BigStep
          (seqList
            ([Whiel.Cmd.«while»
              (changedGuard P) (iterationCmd P)] :
              List (Whiel.Cmd D (execSchema P))))
          Jfirst Jfinal :=
      seqList_cons_bigStep hLoop
        (seqList_nil_bigStep (D := D) Jfinal)
    have hInitLoop :
        Whiel.Cmd.BigStep
          (seqList
            (((idbSymList P).map (initialStepIDBCmd P)) ++
              [Whiel.Cmd.«while»
                (changedGuard P) (iterationCmd P)]))
          Jsnap
          Jfinal :=
      seqList_append_bigStep hInitStep hLoopList
    have hCore :
        Whiel.Cmd.BigStep (cmdCore P) J₀ Jfinal := by
      simpa [cmdCore, List.append_assoc] using
        (seqList_append_bigStep hEmpty hInitLoop)
    have hClean :
        Whiel.Cmd.BigStep (cmdCore P).clean
          J₀ Jfinal :=
      (Whiel.Cmd.bigStep_clean_iff
        (cmdCore P) J₀ Jfinal).mpr hCore
    simpa [Program.toWhielCmd] using hClean
  have hFinalLive :
      liveState P Jfinal = P.LFP I := by
    simpa [Program.LFP, Program.lfpFuel]
      using hFinalLiveIter
  have hReduct :
      reductToProgramSchema P Jfinal = P.LFP I := by
    have hRed := reduct_observe_eq_liveState P Jfinal
    simpa [reductToProgramSchema, Whiel.Program.observe,
      Program.toWhielProgram, hFinalLive] using hRed
  exact ⟨Jfinal, by simpa [J₀] using hCmd, by
    simpa using hReduct⟩

theorem toWhielCmd_bigStep_LFP_observe
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    ∃ J : Instance D (execSchema P),
      (P.toWhielCmd).BigStep
        ((P.toWhielProgram).initialInstance I) J ∧
        (P.toWhielProgram).observe J = P.LFP I := by
  rcases toWhielCmd_bigStep_LFP_reduct P I with
    ⟨J, hCmd, hReduct⟩
  refine ⟨J, ?_, ?_⟩
  · simpa [Whiel.Program.initialInstance,
      Program.toWhielProgram,
      initialInstance] using hCmd
  · simpa [reductToProgramSchema, Whiel.Program.observe,
      Program.toWhielProgram]
      using hReduct

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Main Correctness Theorems
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The generated naive Whiel program computes the operational
  LFP.
-/
theorem toWhielProgram_bigStep_LFP
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    (P.toWhielProgram).BigStep I (P.LFP I) := by
  rcases
      WhielCompiler.Naive.toWhielCmd_bigStep_LFP_reduct
        P I with
    ⟨J, hCmd, hReduct⟩
  refine ⟨J, ?_, ?_⟩
  · simpa [Whiel.Program.initialInstance,
      Program.toWhielProgram,
      WhielCompiler.Naive.initialInstance] using hCmd
  · simpa [WhielCompiler.Naive.reductToProgramSchema,
      Whiel.Program.observe, Program.toWhielProgram]
      using hReduct

/-
  The generated naive Whiel program computes the minimal
  model.
-/
theorem toWhielProgram_bigStep_minimalModel
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    (P.toWhielProgram).BigStep I (P.minimalModel I) := by
  rw [← P.LFP_eq_minimalModel I]
  exact P.toWhielProgram_bigStep_LFP I

end Program

end Datalog
