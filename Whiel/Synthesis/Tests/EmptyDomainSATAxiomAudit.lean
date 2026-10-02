-- Author: Jesse Comer
import Databases.Logic.PropositionalCNF
import Databases.RelCalc.EmptyDomain
import Whiel.Vampire.EmptyDomainLRAT

/- Axiom closure of the constructive CNF bridge. -/

/--
info: 'PropositionalCNF.Formula.satisfiable_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PropositionalCNF.Formula.satisfiable_encode

/--
info: 'PropositionalCNF.CNF.number_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PropositionalCNF.CNF.number_wellFormed

/--
info: 'RelCalc.Formula.emptyReduction_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RelCalc.Formula.emptyReduction_correct
/--
info: 'RelCalc.Sentence.emptyReduction_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RelCalc.Sentence.emptyReduction_correct
/--
info: 'RelCalc.SentenceEntailment.satisfiable_emptyCNF_of_hasEmptyCounterexample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RelCalc.SentenceEntailment.satisfiable_emptyCNF_of_hasEmptyCounterexample

/--
info: 'Whiel.Vampire.EmptyDomainLRAT.unsatisfiable_of_kernel_proof' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Whiel.Vampire.EmptyDomainLRAT.unsatisfiable_of_kernel_proof
/--
info: 'Whiel.Vampire.EmptyDomainLRAT.emptyCounterexample_eq_false' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Whiel.Vampire.EmptyDomainLRAT.emptyCounterexample_eq_false

/--
info: 'PropositionalCNF.Formula.eval_simplify' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms PropositionalCNF.Formula.eval_simplify

/--
info: 'PropositionalCNF.Formula.simplify_nodeCount_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PropositionalCNF.Formula.simplify_nodeCount_le
