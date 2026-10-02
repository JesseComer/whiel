import Databases.Datalog.ModelSemantics
import Databases.Datalog.RAConsequence
import Whiel.Cmd.Semantics

/-
  This file specifies a first Whiel translation for
  sequential in-place Datalog evaluation.

  Key definitions include:
    * `Datalog.WhielCompiler.GaussSeidelNaive.ruleUpdateCmd?`
    * `Datalog.WhielCompiler.GaussSeidelNaive.unstableGuard?`
    * `Datalog.WhielCompiler.GaussSeidelNaive.program?`

  The generated command uses the Datalog output schema as
  its Whiel execution schema.  Input relations are supplied
  externally; IDB relations start empty via Whiel program
  initialization.  Each pass assigns
  `head := head ∪ translatedRuleBody`.  The loop continues
  while some translated rule body is not contained in the
  corresponding head relation.
-/

------------------------------------------------------------
-- Command and Guard Lists
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace GaussSeidelNaive

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Sequential composition of a command list. -/
def seqList :
    List (Whiel.Cmd D Γ) → Whiel.Cmd D Γ
| [] => .skip
| C :: Cs => .seq C (seqList Cs)

/- Conjunction of a guard list. -/
def andList :
    List (Whiel.Guard D Γ) → Whiel.Guard D Γ
| [] => .«true»
| G :: Gs => .and G (andList Gs)

/- Disjunction of a guard list. -/
def orList :
    List (Whiel.Guard D Γ) → Whiel.Guard D Γ
| [] => .«false»
| G :: Gs => .or G (orList Gs)

end GaussSeidelNaive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Output-Schema Rule References
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace GaussSeidelNaive

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The rule head as a program-schema symbol. -/
def headSym
    (P : Program D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules}) :
    Γ.syms :=
  r.1.head.rel

/- Head arity through `headSym` is definitional. -/
theorem headSym_arity
    (P : Program D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules}) :
    Γ.arity (headSym P r) =
      Γ.arity r.1.head.rel := by
  rfl

/-
  The rule-head relation as typed RA over the program
  schema.
-/
def headRelExpr
    (P : Program D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules}) :
    RAExpr D Γ (Γ.arity (headSym P r)) :=
  RAExpr.rel (headSym P r)

/- A translated rule query at the rule-head arity. -/
def queryOnProgram
    (P : Program D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (e : RAExpr D Γ (Γ.arity r.1.head.rel)) :
    RAExpr D Γ (Γ.arity (headSym P r)) :=
  e

end GaussSeidelNaive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Per-Rule Gauss-Seidel Commands
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace GaussSeidelNaive

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  One Gauss-Seidel update command for a single Datalog
  rule.
-/
def ruleUpdateCmd?
    (P : Program D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules}) :
    Option (Whiel.Cmd D Γ) :=
  let X := headSym P r
  let head := headRelExpr P r
  let query := queryOnProgram P r r.1.consequenceSPJ
  let rhs := RAExpr.union head query
  some (.assign X rhs)

/- Guard saying this rule can still add tuples. -/
def ruleUnstableGuard?
    (P : Program D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules}) :
    Option (Whiel.Guard D Γ) :=
  let head := headRelExpr P r
  let query := queryOnProgram P r r.1.consequenceSPJ
  some (.not (.subset query head))

/- Translate a list of per-rule update commands. -/
def ruleUpdateCmds?
    (P : Program D Γ) :
    List {r : Rule D Γ // r ∈ P.rules} →
      Option (List (Whiel.Cmd D Γ))
| [] => some []
| r :: rs =>
    match ruleUpdateCmd? P r,
        ruleUpdateCmds? P rs with
    | some C, some Cs => some (C :: Cs)
    | _, _ => none

/- Translate a list of per-rule instability guards. -/
def ruleUnstableGuards?
    (P : Program D Γ) :
    List {r : Rule D Γ // r ∈ P.rules} →
      Option (List (Whiel.Guard D Γ))
| [] => some []
| r :: rs =>
    match ruleUnstableGuard? P r,
        ruleUnstableGuards? P rs with
    | some G, some Gs => some (G :: Gs)
    | _, _ => none

end GaussSeidelNaive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Gauss-Seidel Translation Skeleton
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace GaussSeidelNaive

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- One full Gauss-Seidel immediate-consequence pass. -/
def pass?
    (P : Program D Γ) :
    Option (Whiel.Cmd D Γ) :=
  match ruleUpdateCmds? P P.rules.attach with
  | none => none
  | some Cs => some (seqList Cs)

/- Loop guard: at least one rule can add tuples. -/
def unstableGuard?
    (P : Program D Γ) :
    Option (Whiel.Guard D Γ) :=
  match ruleUnstableGuards? P P.rules.attach with
  | none => none
  | some Gs => some (orList Gs)

/- Gauss-Seidel fixed-point command skeleton. -/
def cmd?
    (P : Program D Γ) :
    Option (Whiel.Cmd D Γ) :=
  match unstableGuard? P, pass? P with
  | some G, some C => some (.while G C)
  | _, _ => none

/-
  Translate a Datalog program to a Whiel program skeleton.
-/
def program?
    (P : Program D Γ) :
    Option (Whiel.Program D P.edbSchema Γ) :=
  match cmd? P with
  | none => none
  | some C =>
      some
        { execSchema := Γ
          extendsInput := P.ambient_extension_edbSchema
          extendsOutput := UnnamedSchema.extensionOf_refl Γ
          cmd := C }

end GaussSeidelNaive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Semantic Correctness Goals
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace GaussSeidelNaive

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  End-to-end goal for this translator: it builds a program,
  the program terminates on every valid input, and each run
  computes the model-theoretic Datalog output.
-/
def TranslationCorrect
    (P : Program D Γ) :
    Prop :=
  ∀ Pwh : Whiel.Program D P.edbSchema Γ,
    program? P = some Pwh →
      (∀ (I : Instance D P.edbSchema)
          (J : Instance D Γ),
          Pwh.BigStep I J →
            P.MinimalModel I J) ∧
        ∀ I : Instance D P.edbSchema, Pwh.Terminates I

end GaussSeidelNaive

end WhielCompiler

end Datalog
