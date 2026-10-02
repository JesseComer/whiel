-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  SPARQL 1.1 property paths: the W3C evaluation procedure
  for `?x p* ?y` and `?x p+ ?y` (the ALP function with a
  visited set) against the Datalog transitive closure, with
  the reflexive pairs that `p*` adds over every term of the
  graph.

  Inputs: `G(s, o)` holds the subject/object pair of every
  triple of the active graph and `P(s, o)` the pairs of the
  triples whose predicate is the path's IRI `p`, so `P ⊆ G`
  is the precondition.

  Side 1, the W3C procedure (SPARQL 1.1 Query, section 18.4,
  "Definition: Function ALP", "Evaluation of ZeroOrMorePath"
  and "Evaluation of OneOrMorePath", read 2026-09-15).  For
  `?x p* ?y` with both ends variables the specification lets
  the start `t` range over nodes(G), the terms occurring as
  subject or object of any triple of G, and returns `(t, n)`
  for every `n` in ALP(t, path).  ALP adds the start to the
  visited set V before taking a step, so `(t, t)` is always
  returned, and it never revisits a node ("if x in V return").
  Set-at-a-time, with all starts run together and the visited
  set indexed by its start: `Alp` is the visited set, seeded
  with the reflexive pairs over nodes(G); `Front` holds the
  pairs visited in the last round; `Next` the pairs reached
  by one more `P` step that were not visited yet.  The order
  in which ALP explores the successors does not affect the
  visited set, so the recursion is rendered as a frontier
  loop.  The specification's OneOrMorePath ("we take one
  step of the path then start recording nodes") is one `P`
  step followed by ALP from the node reached, which on the
  visited sets already computed is `P ∘ Alp`, the expression
  `π[0, 3] (σ[#1 = #2] (P × Alp))` of the postcondition (a
  trailing assignment would make the preprocessor serialise
  the two loops).

  Side 2, Datalog (compiled by the repository's naive
  compiler from)
    `Tc(x, y)   :- P(x, y)`
    `Tc(x, z)   :- Tc(x, y), P(y, z)`
    `Star(x, x) :- G(x, y)`
    `Star(y, y) :- G(x, y)`
    `Star(x, y) :- Tc(x, y)`
  `Tc_aux` and `Star_aux` are the compiler's snapshots.

  Precondition `P ⊆ G`; postcondition
  `(Alp = Star) ∧ (P ∘ Alp = Tc)`.

  Expected verdict: valid.  The visited set of ALP started
  at `t` is the set of nodes reachable from `t` by zero or
  more `p` steps, so `Alp` is the identity on nodes(G) plus
  the closure of `P`, which is `Star`; and `P ∘ Alp` is
  `P ∪ P ∘ Tc = Tc`.  The two loops are independent and the
  preprocessor merges them side by side; both advance one
  `p` step per round (`Front = Star ∖ Star_aux` after every
  round), so the expected obstruction is none: anchored,
  lockstep frontiers.  The `p+` conjunct needs the closure
  inclusions `P ⊆ Tc`, `P ∘ Tc ⊆ Tc` and `Tc ⊆ P ∪ P ∘ Tc`,
  which are inductive for the compiled loop.

  Why it matters: section 9.4 of the same recommendation
  fixes set semantics for connectivity matching ("does not
  introduce duplicates"), and engines implement `p*`/`p+`
  either by a visited-set traversal as in the specification
  or by a recursive query; the equivalence is what licenses
  the second implementation.  The reflexive part is the
  standard trap: `p*` is not the closure of the `p` triples
  plus the identity on their endpoints, because a term that
  occurs only in triples with other predicates is still in
  nodes(G) and matches `?x p* ?x`.  Example5015 is that
  misreading and is invalid.

  Sources: W3C SPARQL 1.1 Query Language, Recommendation
  21 March 2013, https://www.w3.org/TR/sparql11-query/,
  sections 9.1 (ZeroOrMorePath, OneOrMorePath), 9.4 and
  18.4 (Definition: Node set of a graph; Definition:
  Function ALP; Evaluation of ZeroOrMorePath; Evaluation of
  OneOrMorePath), read 2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5014

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {G, P, Alp, Front, Next, Tc, Tc_aux, Star, Star_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ (P ⊆ G) ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Alp := (π[0, 0] G ∪ π[1, 1] G);
      Front := Alp;
      WHILE (Front ≠ ∅) DO
        Next := (π[0, 3] (σ[#1 = #2] (Front × P)) ∖ Alp);
        Alp := (Alp ∪ Next);
        Front := Next
      END;
      Tc_aux := ∅[2];
      Star_aux := ∅[2];
      Tc := (P ∪ π[0,3] (σ[#1 = #2] ((Tc_aux × P))));
      Star := (π[0,0] (G) ∪ (π[1,1] (G) ∪ Tc_aux));
      WHILE (¬(((Tc = Tc_aux) ∧ (Star = Star_aux)))) DO
        Tc_aux := Tc;
        Star_aux := Star;
        Tc := (Tc ∪ (P ∪ π[0,3] (σ[#1 = #2] ((Tc_aux × P)))));
        Star := (Star ∪ (π[0,0] (G) ∪ (π[1,1] (G) ∪ Tc_aux)))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((Alp = Star) ∧ (π[0, 3] (σ[#1 = #2] (P × Alp)) = Tc))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5014
end Benchmark
end Whiel
