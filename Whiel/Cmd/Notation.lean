-- Author: Jesse Comer
import Whiel.Cmd.Syntax
import Whiel.Cmd.Rewrites
import Whiel.Cmd.PrettyPrint
import Whiel.Guard.Notation

/-
  Well-formed notation helpers for Whiel programs.

  This file keeps the generic typed-command program wrapper.
  Surface command parsing is provided by the concrete Whiel
  notation layer, where relation names have a fixed concrete
  syntax.
-/

------------------------------------------------------------
-- Syntactic Construction Helpers
------------------------------------------------------------

namespace Whiel

namespace Cmd

namespace Notation

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Build an assignment from a checked raw RHS. -/
def assignRaw
    (X : A)
    (h : X ∈ Γ.syms := by decide)
    (e : RawRAExpr A D)
    (hE :
      e.arity? Γ = some (Γ.arity (Γ.sym X h)) :=
        by decide) :
    Cmd D Γ :=
  Cmd.assign (Γ.sym X h)
    (RAExpr.Notation.ofRaw
      (Γ := Γ) (n := Γ.arity (Γ.sym X h))
      e (h := hE))

/- Build an assignment to a checked schema symbol. -/
def assignRawSym
    (X : Γ.syms)
    (e : RawRAExpr A D)
    (hE : e.arity? Γ = some (Γ.arity X) := by decide) :
    Cmd D Γ :=
  Cmd.assign X
    (RAExpr.Notation.ofRaw
      (Γ := Γ) (n := Γ.arity X) e (h := hE))

/- Build an assignment from a checked raw name. -/
def assign
    (X : A)
    (h : X ∈ Γ.syms := by decide)
    (e : RAExpr D Γ (Γ.arity (Γ.sym X h))) :
    Cmd D Γ :=
  Cmd.assign (Γ.sym X h) e

end Notation

end Cmd

namespace Program

namespace Notation

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ Δ Λ : UnnamedSchema A}

/- Build a program from explicit interface proofs. -/
def ofExec
    (hIn : Γ.extensionOf Δ)
    (hOut : Γ.extensionOf Λ)
    (C : Cmd D Γ) :
    Program D Δ Λ where
  execSchema := Γ
  extendsInput := hIn
  extendsOutput := hOut
  cmd := C

end Notation

end Program

end Whiel

------------------------------------------------------------
-- Surface Notation
------------------------------------------------------------

macro
  "whiel![" "{" "Input" ":" Δ:term "}"
    "{" C:term "}" "{" "Return" ":" Λ:term "}" "]" :
      term =>
  `(Whiel.Program.Notation.ofExec
      (Δ := $Δ) (Λ := $Λ)
      (by decide) (by decide) $C)
