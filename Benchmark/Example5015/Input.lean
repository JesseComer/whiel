-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  SPARQL 1.1 property paths, the invalid twin of Example5014:
  the W3C procedure for `?x p* ?y` against the closure of the
  `p` triples plus the identity on their own endpoints, the
  common misreading of the zero-length case.

  Inputs and side 1 are those of Example5015: `G(s, o)` is
  the subject/object pair of every triple of the active
  graph, `P(s, o)` the pairs of the triples with predicate
  `p` (`P ⊆ G`), and `Alp`/`Front`/`Next` run the ALP
  procedure of SPARQL 1.1 Query section 18.4 set-at-a-time
  from every term in nodes(G); `P ∘ Alp`, the OneOrMorePath
  result, is the expression of the postcondition's second
  conjunct.

  Side 2 differs in the zero-length rules only: the reflexive
  pairs are taken over the endpoints of `P` instead of over
  nodes(G) (compiled by the naive compiler from)
    `Tc(x, y)   :- P(x, y)`
    `Tc(x, z)   :- Tc(x, y), P(y, z)`
    `Star(x, x) :- P(x, y)`
    `Star(y, y) :- P(x, y)`
    `Star(x, y) :- Tc(x, y)`
  This is what one gets by evaluating `p*` on the subgraph of
  the `p` triples alone, or by translating `p*` to "closure
  plus identity" over that subgraph.

  Precondition `P ⊆ G`; postcondition
  `(Alp = Star) ∧ (P ∘ Alp = Tc)`.

  Expected verdict: invalid.  Section 18.4 defines
  nodes(G) as the terms "used as a subject or object of a
  triple of G", with no restriction to the path's predicate,
  and the var/var case of ZeroOrMorePath ranges over
  nodes(G); so a term that occurs only in a triple with
  another predicate matches `?x p* ?x` under the
  specification but has no `Star` pair here.  Witness: G =
  {(0, 1), (2, 3)}, P = {(0, 1)}: ALP returns (2, 2) and
  (3, 3), the closure side does not (kernel-checked in
  Certificate/Invalid.lean).  The control G = P =
  {(0, 1), (1, 2)} is not a counterexample.  The `p+`
  conjunct holds on every instance; only the reflexive part
  fails.

  Why it matters: as for Example5015; this twin pins the
  reflexive-domain subtlety that separates the W3C `p*` from
  "transitive closure plus identity" over the `p` triples.

  Sources: W3C SPARQL 1.1 Query Language, Recommendation
  21 March 2013, https://www.w3.org/TR/sparql11-query/,
  sections 9.1, 9.4 and 18.4 (Definition: Node set of a
  graph; Definition: Function ALP; Evaluation of
  ZeroOrMorePath; Evaluation of OneOrMorePath), read
  2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5015

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
      Star := (π[0,0] (P) ∪ (π[1,1] (P) ∪ Tc_aux));
      WHILE (¬(((Tc = Tc_aux) ∧ (Star = Star_aux)))) DO
        Tc_aux := Tc;
        Star_aux := Star;
        Tc := (Tc ∪ (P ∪ π[0,3] (σ[#1 = #2] ((Tc_aux × P)))));
        Star := (Star ∪ (π[0,0] (P) ∪ (π[1,1] (P) ∪ Tc_aux)))
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

end Example5015
end Benchmark
end Whiel
