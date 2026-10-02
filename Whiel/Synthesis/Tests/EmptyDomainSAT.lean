-- Author: Jesse Comer
import Databases.Logic.PropositionalCNF
import Databases.RelCalc.EmptyDomain
import Whiel.Vampire.EmptyDomainLRAT

/- Numeric CNF and empty-domain reduction gates. -/

------------------------------------------------------------
-- Numeric CNF Edge Cases
------------------------------------------------------------

namespace Whiel.Synthesis.Tests.EmptyDomainSAT

open PropositionalCNF

/- An empty conjunction differs from an empty clause. -/
#guard (CNF.number ([] : CNF Nat)).dimacs =
  "p cnf 0 0\n"

#guard (CNF.number ([[]] : CNF Nat)).dimacs =
  "p cnf 0 1\n0\n"

/- False needs a root assertion and its negative unit. -/
#guard (Formula.const (α := Nat) false).encode.dimacs =
  "p cnf 1 2\n1 0\n-1 0\n"

#guard (Formula.const (α := Nat) true).encode.dimacs =
  "p cnf 1 2\n1 0\n1 0\n"

/- Repeated atoms share the same input and gate keys. -/
private def repeated : Formula Nat :=
  .and (.atom 0) (.not (.atom 0))

private def distinct : Formula Nat :=
  .and (.atom 0) (.not (.atom 1))

#guard repeated.encode.variableCount = 4
#guard distinct.encode.variableCount = 6

/- Every numeric literal lies within the DIMACS header. -/
example (p : Formula Nat) : p.encode.WellFormed :=
  CNF.number_wellFormed p.symbolic

/- The encoder never distributes a nested equivalence. -/
private def equivalences : Formula Nat :=
  .iff (.iff (.atom 0) (.atom 1))
    (.iff (.atom 1) (.atom 2))

#guard equivalences.encode.clauses.length = 21

end Whiel.Synthesis.Tests.EmptyDomainSAT

------------------------------------------------------------
-- Verified Constant Folding
------------------------------------------------------------

namespace Whiel.Synthesis.Tests.EmptyDomainSAT

open PropositionalCNF

private def atom0 : Formula Nat := .atom 0
private def atom1 : Formula Nat := .atom 1

private def foldCases : List (Formula Nat × Formula Nat) :=
  [ (.not (.const true), .const false),
    (.not (.const false), .const true),
    (.not atom0, .not atom0),
    (.and (.const false) atom0, .const false),
    (.and atom0 (.const false), .const false),
    (.and (.const true) atom0, atom0),
    (.and atom0 (.const true), atom0),
    (.or (.const true) atom0, .const true),
    (.or atom0 (.const true), .const true),
    (.or (.const false) atom0, atom0),
    (.or atom0 (.const false), atom0),
    (.imp (.const false) atom0, .const true),
    (.imp atom0 (.const true), .const true),
    (.imp (.const true) atom0, atom0),
    (.imp atom0 (.const false), .not atom0),
    (.iff (.const true) atom0, atom0),
    (.iff atom0 (.const true), atom0),
    (.iff (.const false) atom0, .not atom0),
    (.iff atom0 (.const false), .not atom0),
    (.iff (.const false) (.const false), .const true),
    (.and atom0 atom1, .and atom0 atom1),
    (.or atom0 atom1, .or atom0 atom1),
    (.imp atom0 atom1, .imp atom0 atom1),
    (.iff atom0 atom1, .iff atom0 atom1),
    (.imp (.and (.const true) atom0)
      (.or (.const false) (.not (.const true))),
      .not atom0) ]

#guard foldCases.all (fun (p, q) => decide (p.simplify = q))

example (p : Formula Nat) (v : Nat → Bool) :
    p.simplify.eval v = p.eval v :=
  p.eval_simplify v

example (p : Formula Nat) :
    p.simplify.nodeCount ≤ p.nodeCount :=
  p.simplify_nodeCount_le

end Whiel.Synthesis.Tests.EmptyDomainSAT

------------------------------------------------------------
-- Empty-Domain Semantic Edge Cases
------------------------------------------------------------

namespace Whiel.Synthesis.Tests.EmptyDomainSAT

local instance : RelationNames Nat where
  decEq := inferInstance
  repr := inferInstance

local instance : Domain Nat where
  inhabited := inferInstance
  decEq := inferInstance
  repr := inferInstance

private def schema : UnnamedSchema Nat where
  syms := {0, 1, 2}
  arity x := if x.1 = 2 then 1 else 0

private def nullary0 : RelCalc.Formula Nat schema :=
  .rel ⟨⟨0, by decide⟩, #v[]⟩

private def nullary1 : RelCalc.Formula Nat schema :=
  .rel ⟨⟨1, by decide⟩, #v[]⟩

private def unary : RelCalc.Formula Nat schema :=
  .rel ⟨⟨2, by decide⟩, #v[.var 0]⟩

private def valuation : Instance.NullaryAssignment schema :=
  fun x => decide (x.1.1 = 0)

/- Equal arity does not identify different nullary names. -/
#guard nullary0.emptyReduction.eval valuation
#guard !nullary1.emptyReduction.eval valuation
#guard !unary.emptyReduction.eval valuation

private def nested : RelCalc.Formula Nat schema :=
  .iff (.imp nullary0 (.not nullary1))
    (.or (.and nullary0 nullary0) .bot)

#guard nested.emptyReduction.eval valuation

/- Vacuous quantifiers ignore even an open body. -/
#guard (RelCalc.Formula.forall_ 0 unary).emptyReduction.eval
  valuation
#guard !(RelCalc.Formula.exists_ 0
  nullary0).emptyReduction.eval valuation

private def openEq : RelCalc.Formula Nat schema :=
  .eq (.var 0) (.var 1)

/- Raw equality uses the fixed assignment. -/
#guard openEq.emptyReduction.eval valuation
#guard !(RelCalc.Formula.eq (Γ := schema)
  (.const 0) (.const 1)).emptyReduction.eval valuation

/- Typed open formulas retain their free-variable guard. -/
example : ¬ openEq.SatIn
    (Instance.ofNullaryAssignment valuation)
    (fun _ => 0) (∅ : Set Nat) := by
  intro h
  exact h.1 0 (by decide)

private def noSymbols : UnnamedSchema Nat where
  syms := ∅
  arity _ := 0

private def noAxioms :
    RelCalc.SentenceEntailment (D := Nat) noSymbols :=
  ⟨[], ⟨.bot, by decide⟩⟩

/- No nullary symbols and no premises still encode truth. -/
#guard noAxioms.emptyFormula.eval (fun _ => false)

private def constantEntailment :
    RelCalc.SentenceEntailment (D := Nat) schema :=
  ⟨[], ⟨.eq (.const 0) (.const 0), by decide⟩⟩

/- Any source constant rules out an empty active domain. -/
#guard !constantEntailment.emptyFormula.eval valuation
#guard constantEntailment.emptyCNF.dimacs =
  "p cnf 1 2\n1 0\n-1 0\n"

private def repeatedEntailment :
    RelCalc.SentenceEntailment (D := Nat) schema :=
  ⟨[⟨nullary0, by decide⟩, ⟨nullary0, by decide⟩],
    ⟨nullary1, by decide⟩⟩

#guard repeatedEntailment.emptyFormula.eval valuation

private def vacuousEntailment :
    RelCalc.SentenceEntailment (D := Nat) schema :=
  ⟨[⟨.forall_ 0 (.eq (.var 0) (.var 0)), by decide⟩],
    ⟨.exists_ 0 (.eq (.var 0) (.var 0)), by decide⟩⟩

#guard vacuousEntailment.emptyFormula.eval valuation

example (E : RelCalc.SentenceEntailment (D := Nat) schema)
    (h : E.HasEmptyCounterexample) :
    ∃ v, E.emptyCNF.clauses.Satisfies v :=
  E.satisfiable_emptyCNF_of_hasEmptyCounterexample h

end Whiel.Synthesis.Tests.EmptyDomainSAT

------------------------------------------------------------
-- Strict Kernel LRAT Replay
------------------------------------------------------------

namespace Whiel.Synthesis.Tests.EmptyDomainSAT

open Whiel.Vampire.EmptyDomainLRAT

example : (cnfToSat [[.pos 0], [.neg 0]]).proof [] := by
  kernel_cnf_lrat "p cnf 1 2\n1 0\n-1 0\n"
    "3 0 1 2 0\n"

example : (cnfToSat [[]]).proof [] := by
  kernel_cnf_lrat "p cnf 0 1\n0\n" ""

example : (cnfToSat [[.pos 0], [.neg 0]]).proof [] := by
  fail_if_success kernel_cnf_lrat
    "p cnf 0 0\n" ""
  fail_if_success kernel_cnf_lrat
    "p cnf 1 1\n1 0\n" "2 0 1 0\n"
  fail_if_success kernel_cnf_lrat
    "p cnf 2 2\n2 0\n-2 0\n" "3 0 1 2 0\n"
  fail_if_success kernel_cnf_lrat
    "p cnf 1 2\n1 0\n-1 0\ntrailing" "3 0 1 2 0\n"
  fail_if_success kernel_cnf_lrat
    "p cnf 1 2\n1 0\n-1 0\n" "3 0 1 2 0\ntrailing"
  fail_if_success kernel_cnf_lrat
    "p cnf 1 2\n1 0\n-1 0\n" "3 0 1 2"
  fail_if_success kernel_cnf_lrat
    "p cnf 1 2\n1 0\n-1 0\n" "3 0 1 -2 0\n"
  kernel_cnf_lrat "p cnf 1 2\n1 0\n-1 0\n"
    "3 0 1 2 0\n"

example : (cnfToSat [[]]).proof [] := by
  fail_if_success kernel_cnf_lrat
    "p cnf 0 1\n0\n" "malformed"
  fail_if_success kernel_cnf_lrat
    "p cnf 0 2\n0\n1 0\n" ""
  kernel_cnf_lrat "p cnf 0 1\n0\n" ""

local instance : RelationNames Nat where
  decEq := inferInstance
  repr := inferInstance

local instance : Domain Nat where
  inhabited := inferInstance
  decEq := inferInstance
  repr := inferInstance

private def qfValid :
    QFEntailment (D := Nat) noSymbols :=
  ⟨[], .«true»⟩

/-
  The result is the unchanged Boolean theorem, proved
  through the semantic bridge and the kernel refutation.
-/
example : qfValid.emptyCounterexample? = false := by
  apply emptyCounterexample_eq_false
  kernel_cnf_lrat
    "p cnf 1 2\n1 0\n-1 0\n"
    "3 0 1 2 0\n"

end Whiel.Synthesis.Tests.EmptyDomainSAT
