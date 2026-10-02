-- Author: Jesse Comer
import Databases.Core.PrettyPrint
import Databases.FOL.Entailment

/-
  Pretty-printers for first-order logic syntax.

  Key declarations include:
    * `FOL.Term.pretty`
    * `FOL.TermList.pretty`
    * `FOL.Formula.pretty`
    * `FOL.Formula.display`
-/

namespace FOL

mutual
/- Render a first-order term. -/
  def Term.pretty
      {A F : Type}
      [RelationNames A]
      [FunctionNames F]
      [DBLib.Notation.PrettyLiteral F]
      {Sig : Signature A F} :
      Term Sig → String
  | .var x => DBTPretty.varName x
  | .func f args =>
      let fname := DBLib.Notation.prettyLiteral f.1
      let renderedArgs := args.pretty
      if renderedArgs.isEmpty then
        fname
      else
        fname ++ "(" ++ renderedArgs ++ ")"

/- Render a first-order term list. -/
  def TermList.pretty
      {A F : Type}
      [RelationNames A]
      [FunctionNames F]
      [DBLib.Notation.PrettyLiteral F]
      {Sig : Signature A F} :
      {n : Nat} → TermList Sig n → String
  | _, .nil => ""
  | _, .cons t ts =>
      let head := t.pretty
      let tail := ts.pretty
      if tail.isEmpty then
        head
      else
        head ++ ", " ++ tail
end

namespace Term

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [DBLib.Notation.PrettyLiteral F]
variable {Sig : Signature A F}

/- Render a first-order term directly in `#eval`. -/
def display (t : Term Sig) : DBTPretty.Display :=
  DBTPretty.display t.pretty

end Term

namespace TermList

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [DBLib.Notation.PrettyLiteral F]
variable {Sig : Signature A F}
variable {n : Nat}

/- Render a term list directly in `#eval`. -/
def display (ts : TermList Sig n) : DBTPretty.Display :=
  DBTPretty.display ts.pretty

end TermList

namespace Formula

variable {A F : Type}
variable [RelationNames A] [FunctionNames F]
variable [DBLib.Notation.PrettyLiteral F]
variable {Sig : Signature A F}

/- Render a first-order formula. -/
def pretty : Formula Sig → String
| .top => "⊤"
| .bot => "⊥"
| .eq t₁ t₂ => t₁.pretty ++ " = " ++ t₂.pretty
| .rel X ts =>
    reprStr X.1 ++ "(" ++ ts.pretty ++ ")"
| .and φ ψ =>
    "(" ++ φ.pretty ++ " ∧ " ++ ψ.pretty ++ ")"
| .or φ ψ =>
    "(" ++ φ.pretty ++ " ∨ " ++ ψ.pretty ++ ")"
| .not φ =>
    "¬" ++ φ.pretty
| .imp φ ψ =>
    "(" ++ φ.pretty ++ " → " ++ ψ.pretty ++ ")"
| .iff φ ψ =>
    "(" ++ φ.pretty ++ " ↔ " ++ ψ.pretty ++ ")"
| .forall_ x φ =>
    "∀ " ++ DBTPretty.varName x ++ ". " ++ φ.pretty
| .exists_ x φ =>
    "∃ " ++ DBTPretty.varName x ++ ". " ++ φ.pretty

/- Render a first-order formula directly in `#eval`. -/
def display (φ : Formula Sig) : DBTPretty.Display :=
  DBTPretty.display φ.pretty

end Formula

namespace Sentence

variable {A F : Type}
variable [RelationNames A] [FunctionNames F]
variable [DBLib.Notation.PrettyLiteral F]
variable {Sig : Signature A F}

/- Render a first-order sentence. -/
def pretty (φ : FOL.Sentence Sig) : String :=
  φ.1.pretty

/- Render a first-order sentence directly in `#eval`. -/
def display (φ : FOL.Sentence Sig) : DBTPretty.Display :=
  DBTPretty.display φ.pretty

/-
  Render a list of FOL sentences with blank lines between
  numbered entries.
-/
def prettyList :
    List (FOL.Sentence Sig) → String
| [] => "  <none>"
| φs =>
    DBTPretty.joinSep "\n\n"
      (φs.zipIdx.map
        (fun p =>
          "  " ++ reprStr p.2 ++ ".\n" ++
            "    " ++ p.1.pretty))

/- Render a list of FOL sentences directly in `#eval`. -/
def displayList
    (φs : List (FOL.Sentence Sig)) :
    DBTPretty.Display :=
  DBTPretty.display (FOL.Sentence.prettyList φs)

end Sentence

namespace SentenceEntailment

variable {A F : Type}
variable [RelationNames A] [FunctionNames F]
variable [DBLib.Notation.PrettyLiteral F]
variable {Sig : Signature A F}

/- Render a FOL sentence entailment. -/
def pretty
    (E : FOL.SentenceEntailment Sig) : String :=
  DBTPretty.joinSep "\n\n"
    [
      "axioms:",
      FOL.Sentence.prettyList E.axioms,
      "conjecture:\n  " ++ E.conjecture.pretty
    ]

/- Render a FOL sentence entailment directly in `#eval`. -/
def display
    (E : FOL.SentenceEntailment Sig) : DBTPretty.Display :=
  DBTPretty.display E.pretty

end SentenceEntailment

end FOL
