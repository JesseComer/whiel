-- Author: Jesse Comer
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Lean.Elab.Tactic.Omega

/-
  A propositional formula has a linear-size Tseitin CNF.
  The proof constructs a satisfying extension of any
  satisfying input assignment; it never searches for one.
  Symbolic auxiliary names are numbered only after the
  gate clauses have been generated.
-/

------------------------------------------------------------
-- Propositional Syntax and Clauses
------------------------------------------------------------

namespace PropositionalCNF

inductive Formula (α : Type) where
  | const : Bool → Formula α
  | atom : α → Formula α
  | not : Formula α → Formula α
  | and : Formula α → Formula α → Formula α
  | or : Formula α → Formula α → Formula α
  | imp : Formula α → Formula α → Formula α
  | iff : Formula α → Formula α → Formula α
deriving DecidableEq, Repr

def Formula.eval {α : Type} (v : α → Bool) :
    Formula α → Bool
  | .const b => b
  | .atom a => v a
  | .not p => !(p.eval v)
  | .and p q => p.eval v && q.eval v
  | .or p q => p.eval v || q.eval v
  | .imp p q => !(p.eval v) || q.eval v
  | .iff p q => p.eval v == q.eval v

def Formula.nodeCount {α : Type} : Formula α → Nat
  | .const _ | .atom _ => 1
  | .not p => 1 + p.nodeCount
  | .and p q | .or p q | .imp p q | .iff p q =>
      1 + p.nodeCount + q.nodeCount

inductive Literal (α : Type) where
  | pos : α → Literal α
  | neg : α → Literal α
deriving DecidableEq, Repr

def Literal.atom {α : Type} : Literal α → α
  | .pos a | .neg a => a

def Literal.eval {α : Type} (v : α → Bool) :
    Literal α → Bool
  | .pos a => v a
  | .neg a => !(v a)

def Literal.map {α β : Type} (f : α → β) :
    Literal α → Literal β
  | .pos a => .pos (f a)
  | .neg a => .neg (f a)

abbrev Clause (α : Type) := List (Literal α)

abbrev CNF (α : Type) := List (Clause α)

def Clause.eval {α : Type}
    (v : α → Bool) (c : Clause α) : Bool :=
  c.any (Literal.eval v)

def CNF.Satisfies {α : Type}
    (v : α → Bool) (cs : CNF α) : Prop :=
  ∀ c ∈ cs, c.eval v = true

theorem CNF.satisfies_append {α : Type}
    (v : α → Bool) (cs ds : CNF α) :
    (cs ++ ds).Satisfies v ↔
      cs.Satisfies v ∧ ds.Satisfies v := by
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left _ hc),
      fun c hc => h c (List.mem_append_right _ hc)⟩
  · rintro ⟨hc, hd⟩ c h
    rcases List.mem_append.mp h with h | h
    · exact hc c h
    · exact hd c h

end PropositionalCNF

------------------------------------------------------------
-- Verified Constant Folding
------------------------------------------------------------

namespace PropositionalCNF.Formula

variable {α : Type}

private def foldNot : Formula α → Formula α
  | .const b => .const (!b)
  | p => .not p

private def foldAnd : Formula α → Formula α → Formula α
  | .const false, _ | _, .const false => .const false
  | .const true, q => q
  | p, .const true => p
  | p, q => .and p q

private def foldOr : Formula α → Formula α → Formula α
  | .const true, _ | _, .const true => .const true
  | .const false, q => q
  | p, .const false => p
  | p, q => .or p q

private def foldImp : Formula α → Formula α → Formula α
  | .const false, _ | _, .const true => .const true
  | .const true, q => q
  | p, .const false => foldNot p
  | p, q => .imp p q

private def foldIff : Formula α → Formula α → Formula α
  | .const true, q => q
  | .const false, q => foldNot q
  | p, .const true => p
  | p, .const false => foldNot p
  | p, q => .iff p q

/- Bottom-up folding never searches input assignments. -/
def simplify : Formula α → Formula α
  | .const b => .const b
  | .atom a => .atom a
  | .not p => foldNot p.simplify
  | .and p q => foldAnd p.simplify q.simplify
  | .or p q => foldOr p.simplify q.simplify
  | .imp p q => foldImp p.simplify q.simplify
  | .iff p q => foldIff p.simplify q.simplify

private theorem eval_foldNot
    (p : Formula α) (v : α → Bool) :
    (foldNot p).eval v = !(p.eval v) := by
  cases p <;> rfl

private theorem eval_foldAnd
    (p q : Formula α) (v : α → Bool) :
    (foldAnd p q).eval v = (p.eval v && q.eval v) := by
  unfold foldAnd
  split <;> simp_all [eval]

private theorem eval_foldOr
    (p q : Formula α) (v : α → Bool) :
    (foldOr p q).eval v = (p.eval v || q.eval v) := by
  unfold foldOr
  split <;> simp_all [eval]

private theorem eval_foldImp
    (p q : Formula α) (v : α → Bool) :
    (foldImp p q).eval v = (!(p.eval v) || q.eval v) := by
  unfold foldImp
  split <;> simp_all [eval, eval_foldNot]

private theorem eval_foldIff
    (p q : Formula α) (v : α → Bool) :
    (foldIff p q).eval v = (p.eval v == q.eval v) := by
  unfold foldIff
  split <;> simp_all [eval, eval_foldNot]

theorem eval_simplify (p : Formula α) (v : α → Bool) :
    p.simplify.eval v = p.eval v := by
  induction p <;>
    simp_all only [simplify, eval_foldNot, eval_foldAnd,
      eval_foldOr, eval_foldImp, eval_foldIff, eval]

private theorem foldNot_nodeCount (p : Formula α) :
    (foldNot p).nodeCount ≤ 1 + p.nodeCount := by
  cases p <;> simp [foldNot, nodeCount]

private theorem foldAnd_nodeCount (p q : Formula α) :
    (foldAnd p q).nodeCount ≤
      1 + p.nodeCount + q.nodeCount := by
  unfold foldAnd
  split <;> simp_all [nodeCount] <;> omega

private theorem foldOr_nodeCount (p q : Formula α) :
    (foldOr p q).nodeCount ≤
      1 + p.nodeCount + q.nodeCount := by
  unfold foldOr
  split <;> simp_all [nodeCount] <;> omega

private theorem foldImp_nodeCount (p q : Formula α) :
    (foldImp p q).nodeCount ≤
      1 + p.nodeCount + q.nodeCount := by
  unfold foldImp
  split <;> simp_all only [nodeCount]
  all_goals first
    | omega
    | exact Nat.le_trans (foldNot_nodeCount _) (by omega)

private theorem foldIff_nodeCount (p q : Formula α) :
    (foldIff p q).nodeCount ≤
      1 + p.nodeCount + q.nodeCount := by
  unfold foldIff
  split <;> simp_all only [nodeCount]
  all_goals first
    | omega
    | exact Nat.le_trans (foldNot_nodeCount _) (by omega)

theorem simplify_nodeCount_le (p : Formula α) :
    p.simplify.nodeCount ≤ p.nodeCount := by
  induction p with
  | const b | atom a => simp [simplify, nodeCount]
  | not p ih =>
      simpa only [simplify, nodeCount] using
        Nat.le_trans (foldNot_nodeCount p.simplify)
          (Nat.add_le_add_left ih 1)
  | and p q hp hq =>
      have h := foldAnd_nodeCount p.simplify q.simplify
      simp only [simplify, nodeCount]
      omega
  | or p q hp hq =>
      have h := foldOr_nodeCount p.simplify q.simplify
      simp only [simplify, nodeCount]
      omega
  | imp p q hp hq =>
      have h := foldImp_nodeCount p.simplify q.simplify
      simp only [simplify, nodeCount]
      omega
  | iff p q hp hq =>
      have h := foldIff_nodeCount p.simplify q.simplify
      simp only [simplify, nodeCount]
      omega

end PropositionalCNF.Formula

------------------------------------------------------------
-- Symbolic Tseitin Gates
------------------------------------------------------------

namespace PropositionalCNF

variable {α : Type}

/- An auxiliary key names its exact input subformula. -/
abbrev Key (α : Type) := Sum α (Formula α)

private def positive (p : Formula α) : Literal (Key α) :=
  .pos (.inr p)

private def negative (p : Formula α) : Literal (Key α) :=
  .neg (.inr p)

private def gate : Formula α → CNF (Key α)
  | .const true => [[positive (.const true)]]
  | .const false => [[negative (.const false)]]
  | .atom a =>
      [[negative (.atom a), .pos (.inl a)],
        [positive (.atom a), .neg (.inl a)]]
  | .not p =>
      [[negative (.not p), negative p],
        [positive (.not p), positive p]]
  | .and p q =>
      [[negative (.and p q), positive p],
        [negative (.and p q), positive q],
        [positive (.and p q), negative p, negative q]]
  | .or p q =>
      [[positive (.or p q), negative p],
        [positive (.or p q), negative q],
        [negative (.or p q), positive p, positive q]]
  | .imp p q =>
      [[positive (.imp p q), positive p],
        [positive (.imp p q), negative q],
        [negative (.imp p q), negative p, positive q]]
  | .iff p q =>
      [[negative (.iff p q), negative p, positive q],
        [negative (.iff p q), positive p, negative q],
        [positive (.iff p q), positive p, positive q],
        [positive (.iff p q), negative p, negative q]]

private def definitions (p : Formula α) : CNF (Key α) :=
  gate p ++ match p with
    | .const _ | .atom _ => []
    | .not q => definitions q
    | .and q r | .or q r | .imp q r | .iff q r =>
        definitions q ++ definitions r

/- Assert the root in addition to defining every gate. -/
def Formula.symbolic (p : Formula α) : CNF (Key α) :=
  [positive p] :: definitions p

/- A witness evaluates one assignment, not all choices. -/
private def keyValue (v : α → Bool) : Key α → Bool
  | .inl a => v a
  | .inr p => p.eval v

private theorem gate_satisfied
    (v : α → Bool) (p : Formula α) :
    (gate p).Satisfies (keyValue v) := by
  cases p with
  | const b =>
      cases b <;>
        simp [gate, CNF.Satisfies, Clause.eval,
          Literal.eval, positive, negative, keyValue,
          Formula.eval]
  | atom a =>
      cases h : v a <;>
        simp [gate, CNF.Satisfies, Clause.eval,
          Literal.eval, positive, negative, keyValue,
          Formula.eval, h]
  | not p =>
      cases h : p.eval v <;>
        simp [gate, CNF.Satisfies, Clause.eval,
          Literal.eval, positive, negative, keyValue,
          Formula.eval, h]
  | and p q | or p q | imp p q | iff p q =>
      cases hp : p.eval v <;> cases hq : q.eval v <;>
        simp [gate, CNF.Satisfies, Clause.eval,
          Literal.eval, positive, negative, keyValue,
          Formula.eval, hp, hq]

private theorem definitions_satisfied
    (v : α → Bool) (p : Formula α) :
    (definitions p).Satisfies (keyValue v) := by
  induction p with
  | const b | atom b =>
      simpa [definitions] using gate_satisfied v _
  | not p ih =>
      exact (CNF.satisfies_append _ _ _).mpr
        ⟨gate_satisfied v _, ih⟩
  | and p q hp hq =>
      exact (CNF.satisfies_append _ _ _).mpr
        ⟨gate_satisfied v _,
          (CNF.satisfies_append _ _ _).mpr ⟨hp, hq⟩⟩
  | or p q hp hq =>
      exact (CNF.satisfies_append _ _ _).mpr
        ⟨gate_satisfied v _,
          (CNF.satisfies_append _ _ _).mpr ⟨hp, hq⟩⟩
  | imp p q hp hq =>
      exact (CNF.satisfies_append _ _ _).mpr
        ⟨gate_satisfied v _,
          (CNF.satisfies_append _ _ _).mpr ⟨hp, hq⟩⟩
  | iff p q hp hq =>
      exact (CNF.satisfies_append _ _ _).mpr
        ⟨gate_satisfied v _,
          (CNF.satisfies_append _ _ _).mpr ⟨hp, hq⟩⟩

theorem Formula.symbolic_satisfied
    (p : Formula α) (v : α → Bool)
    (h : p.eval v = true) :
    p.symbolic.Satisfies (keyValue v) := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · simpa [Clause.eval, positive, Literal.eval,
      keyValue] using h
  · exact definitions_satisfied v p c hc

private theorem gate_length (p : Formula α) :
    (gate p).length ≤ 4 := by
  cases p <;> simp [gate]
  split <;> simp

private theorem definitions_length (p : Formula α) :
    (definitions p).length ≤ 4 * p.nodeCount := by
  induction p with
  | const b | atom b =>
      simpa [definitions, Formula.nodeCount] using
        gate_length (α := α) _
  | not p ih =>
      simp only [definitions, gate, List.length_append,
        List.length_cons, List.length_nil,
        Formula.nodeCount]
      omega
  | and p q hp hq =>
      simp only [definitions, gate, List.length_append,
        List.length_cons, List.length_nil,
        Formula.nodeCount]
      omega
  | or p q hp hq =>
      simp only [definitions, gate, List.length_append,
        List.length_cons, List.length_nil,
        Formula.nodeCount]
      omega
  | imp p q hp hq =>
      simp only [definitions, gate, List.length_append,
        List.length_cons, List.length_nil,
        Formula.nodeCount]
      omega
  | iff p q hp hq =>
      simp only [definitions, gate, List.length_append,
        List.length_cons, List.length_nil,
        Formula.nodeCount]
      omega

end PropositionalCNF

------------------------------------------------------------
-- Deterministic Numeric Encoding
------------------------------------------------------------

namespace PropositionalCNF

variable {α : Type} [DecidableEq α]

/- All symbolic keys occur in the emitted clauses. -/
private def keys (cs : CNF α) : List α :=
  (cs.flatMap (fun c => c.map Literal.atom)).dedup

private theorem mem_keys
    {cs : CNF α} {c : Clause α} {l : Literal α}
    (hc : c ∈ cs) (hl : l ∈ c) :
    l.atom ∈ keys cs := by
  simp only [keys, List.mem_dedup, List.mem_flatMap,
    List.mem_map]
  exact ⟨c, hc, l, hl, rfl⟩

structure Encoding where
  variableCount : Nat
  clauses : CNF Nat
deriving Repr

def Encoding.WellFormed (e : Encoding) : Prop :=
  ∀ c ∈ e.clauses, ∀ l ∈ c, l.atom < e.variableCount

def CNF.number (cs : CNF α) : Encoding :=
  let ks := keys cs
  ⟨ks.length,
    cs.map (fun c => c.map
      (Literal.map (fun a => ks.idxOf a)))⟩

theorem CNF.number_wellFormed (cs : CNF α) :
    cs.number.WellFormed := by
  intro c hc l hl
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
  have h := List.idxOf_lt_length_iff.mpr
    (mem_keys hd hk)
  cases k <;> simpa [Literal.map, Literal.atom,
    CNF.number] using h

private def numberedValue
    (cs : CNF α) (v : α → Bool) (n : Nat) : Bool :=
  match (keys cs)[n]? with
  | some a => v a
  | none => false

private theorem numberedValue_key
    (cs : CNF α) (v : α → Bool)
    {a : α} (ha : a ∈ keys cs) :
    numberedValue cs v ((keys cs).idxOf a) = v a := by
  simp [numberedValue, List.getElem?_idxOf ha]

omit [DecidableEq α] in
private theorem literal_eval_map
    {β : Type} (v : α → Bool) (w : β → Bool)
    (f : α → β) (l : Literal α)
    (h : w (f l.atom) = v l.atom) :
    (l.map f).eval w = l.eval v := by
  cases l <;> simp_all [Literal.map, Literal.atom,
    Literal.eval]

omit [DecidableEq α] in
private theorem clause_eval_map
    {β : Type} (v : α → Bool) (w : β → Bool)
    (f : α → β) (c : Clause α)
    (h : ∀ l ∈ c, w (f l.atom) = v l.atom) :
    Clause.eval w (c.map (Literal.map f)) =
      c.eval v := by
  induction c with
  | nil => rfl
  | cons l c ih =>
      have hl := literal_eval_map v w f l
        (h l (List.mem_cons_self ..))
      have hc := ih (fun k hk =>
        h k (List.mem_cons_of_mem _ hk))
      simpa [Clause.eval] using congrArg₂ Bool.or hl hc

theorem CNF.number_satisfied
    (cs : CNF α) (v : α → Bool)
    (h : cs.Satisfies v) :
    cs.number.clauses.Satisfies (numberedValue cs v) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  rw [clause_eval_map v (numberedValue cs v)
    (fun a => (keys cs).idxOf a) d]
  · exact h d hd
  · intro l hl
    exact numberedValue_key cs v (mem_keys hd hl)

def Formula.encode (p : Formula α) : Encoding :=
  p.symbolic.number

theorem Formula.satisfiable_encode
    (p : Formula α) (v : α → Bool)
    (h : p.eval v = true) :
    ∃ w, p.encode.clauses.Satisfies w := by
  exact ⟨_, CNF.number_satisfied _ _
    (p.symbolic_satisfied v h)⟩

theorem Formula.encode_clause_bound (p : Formula α) :
    p.encode.clauses.length ≤ 4 * p.nodeCount + 1 := by
  have h := definitions_length p
  simpa [Formula.encode, CNF.number, Formula.symbolic]
    using Nat.add_le_add_right h 1

end PropositionalCNF

------------------------------------------------------------
-- DIMACS Transport
------------------------------------------------------------

namespace PropositionalCNF

def Literal.dimacs : Literal Nat → String
  | .pos n => toString (n + 1)
  | .neg n => "-" ++ toString (n + 1)

def Encoding.dimacs (e : Encoding) : String :=
  "p cnf " ++ toString e.variableCount ++ " " ++
    toString e.clauses.length ++ "\n" ++
    String.join (e.clauses.map fun c =>
      String.join (c.map (fun l => l.dimacs ++ " ")) ++
        "0\n")

end PropositionalCNF
