-- Author: Jesse Comer
import Databases.RelCalc.EmptyDomain
import Whiel.Vampire.QFEntailment
import Mathlib.Tactic.Sat.FromLRAT
import Lean.Elab.Tactic

/-
  Convert the certifier's numeric CNF into Mathlib's SAT
  semantics and replay LRAT with kernel proof terms.
  Parsed resources select proof construction only: the
  resulting term must have the exact generated CNF type.
-/

------------------------------------------------------------
-- Kernel SAT Semantics Bridge
------------------------------------------------------------

namespace Whiel.Vampire.EmptyDomainLRAT

open PropositionalCNF RelCalc.SentenceEntailment

def literalToSat : Literal Nat → Sat.Literal
  | .pos n => .pos n
  | .neg n => .neg n

def clauseToSat (c : Clause Nat) : Sat.Clause :=
  c.map literalToSat

def cnfToSat (cs : CNF Nat) : Sat.Fmla :=
  cs.map clauseToSat

def valuationToSat (v : Nat → Bool) : Sat.Valuation :=
  fun n => v n = true

private theorem literal_true_not_neg
    (v : Nat → Bool) (l : Literal Nat)
    (h : l.eval v = true) :
    ¬ (valuationToSat v).neg (literalToSat l) := by
  cases l with
  | pos n =>
    exact fun hn => hn h
  | neg n =>
    intro hn
    change v n = true at hn
    change (!v n) = true at h
    rw [hn] at h
    cases h

theorem clause_satisfied
    (v : Nat → Bool) (c : Clause Nat)
    (h : c.eval v = true) :
    (valuationToSat v).satisfies (clauseToSat c) := by
  induction c with
  | nil => simp [Clause.eval] at h
  | cons l c ih =>
    simp only [Clause.eval, List.any_cons,
      Bool.or_eq_true] at h
    intro hn
    rcases h with hl | hc
    · exact False.elim (literal_true_not_neg v l hl hn)
    · exact ih hc

theorem cnf_satisfied
    (v : Nat → Bool) (cs : CNF Nat)
    (h : cs.Satisfies v) :
    (valuationToSat v).satisfies_fmla (cnfToSat cs) := by
  constructor
  intro c hc
  obtain ⟨source, hsource, rfl⟩ :=
    List.mem_map.mp hc
  exact clause_satisfied v source (h source hsource)

theorem unsatisfiable_of_kernel_proof
    (cs : CNF Nat)
    (h : (cnfToSat cs).proof []) :
    ¬ ∃ v, cs.Satisfies v := by
  rintro ⟨v, hv⟩
  exact h (valuationToSat v) (cnf_satisfied v cs hv)

theorem emptyCounterexample_eq_false
    {A D : Type} [RelationNames A] [Domain D]
    {Γ : UnnamedSchema A} [Fintype Γ.syms]
    (E : QFEntailment (D := D) Γ)
    (h : (cnfToSat
      E.toRelCalcEntailment.emptyCNF.clauses).proof []) :
    E.emptyCounterexample? = false := by
  apply
    (QFEntailment.emptyCounterexample?_eq_false_iff E).mpr
  intro counterexample
  exact unsatisfiable_of_kernel_proof _ h
    (satisfiable_emptyCNF_of_hasEmptyCounterexample
        E.toRelCalcEntailment counterexample)

end Whiel.Vampire.EmptyDomainLRAT

------------------------------------------------------------
-- Strict Resource Parsing and Kernel Replay
------------------------------------------------------------

namespace Whiel.Vampire.EmptyDomainLRAT

open Lean Meta Elab Tactic
open Std.Internal

private def parseResources
    (cnf lrat : String) :
    MetaM (Array (Array Int) ×
      Array Mathlib.Tactic.Sat.LRATStep) := do
  let parseCNF :=
    Mathlib.Tactic.Sat.Parser.parseDimacs <*
      Parsec.String.ws <* Parsec.eof
  let .success _ (variableCount, clauses) :=
      parseCNF ⟨_, cnf.startPos⟩
    | throwError "invalid or trailing CNF input"
  if clauses.isEmpty then
    throwError "a CNF with no clauses is satisfiable"
  for clause in clauses do
    for literal in clause do
      if literal == 0 || literal.natAbs > variableCount then
        throwError "CNF literal outside its variable bound"
  let parseLRAT :=
    Mathlib.Tactic.Sat.Parser.parseLRAT <*
      Parsec.String.ws <* Parsec.eof
  let .success _ steps := parseLRAT ⟨_, lrat.startPos⟩
    | throwError "invalid or trailing LRAT input"
  for step in steps do
    match step with
    | .del _ => pure ()
    | .add _ literals hints =>
      if hints.any (fun hint => hint < 0) then
        throwError "RAT steps are unsupported"
      for literal in literals do
        if literal == 0 ||
            literal.natAbs > variableCount then
          throwError
            "LRAT literal outside its variable bound"
  return (clauses, steps)

private def replayProof
    (cnf lrat : String) : MetaM Expr := do
  let (clauses, _) ← parseResources cnf lrat
  match clauses.findIdx? Array.isEmpty with
  | some index =>
    let context := Mathlib.Tactic.Sat.buildConj
      clauses 0 clauses.size
    let self := mkApp (mkConst ``Sat.Fmla.subsumes_self)
      context
    let proofs := (Mathlib.Tactic.Sat.buildClauses
      clauses context 0 clauses.size context self
      default).2
    let some clause := proofs[index + 1]?
      | throwError "missing initial empty-clause proof"
    return clause.proof
  | none =>
    let name ← mkFreshUserName `emptyDomainLRAT
    let (_, _, _, proof) ←
      Mathlib.Tactic.Sat.fromLRATAux cnf lrat name
    return proof

elab "kernel_cnf_lrat " cnf:term:max
    ppSpace lrat:term:max : tactic => do
  let cnf ← unsafe Term.evalTerm String
    (mkConst ``String) cnf
  let lrat ← unsafe Term.evalTerm String
    (mkConst ``String) lrat
  let proof ← replayProof cnf lrat
  let goal ← getMainGoal
  goal.withContext do
    let expected ← goal.getType
    let actual ← inferType proof
    unless ← isDefEq expected actual do
      throwError
        "LRAT evidence does not prove the exact CNF"
    goal.assign proof
  replaceMainGoal []

end Whiel.Vampire.EmptyDomainLRAT
