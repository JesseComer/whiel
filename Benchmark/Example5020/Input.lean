-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  RDFS entailment computed by two rule sets: the minimal
  rho-df system of Munoz, Perez and Gutierrez against the
  full RDFS entailment patterns of the W3C, on the same
  input.  The two closures agree on triples and on typing,
  and differ exactly by the reflexive subPropertyOf and
  subClassOf triples that RDFS derives for every property
  and class.

  Inputs, one relation per rho-df predicate (the vocabulary
  is not data, so the RDFS terms never occur as subjects or
  objects: these are the mrdf-graphs of Munoz et al.,
  Definition 15, "ground rho-df triples having no rho-df
  vocabulary as subject or object"): `TypeOf(x, c)` for
  (x, rdf:type, c), `SubClass(c, d)`, `SubProp(p, q)`,
  `Dom(p, c)`, `Range(p, c)`, and `Triple(s, p, o)` for the
  triples whose predicate is not RDFS vocabulary.

  Side 1, rho-df (Munoz, Perez, Gutierrez, "Simple and
  Efficient Minimal RDFS", JWS 2009, Table 1 and Definition
  15, read 2026-09-15): the system ⊢mrdf uses rules (1b),
  (2), (3), (4) only; rule (5) (implicit typing) is
  redundant on ground graphs and rules (6), (7) (reflexivity
  of sp and sc) are dropped on purpose.  As Datalog, with
  the W3C names of the same patterns:
    `SubPropM(p, q)    :- SubProp(p, q)`
    `SubPropM(p, r)    :- SubPropM(p, q), SubPropM(q, r)`       (2a) = rdfs5
    `TripleM(s, p, o)  :- Triple(s, p, o)`
    `TripleM(s, q, o)  :- SubPropM(p, q), TripleM(s, p, o)`     (2b) = rdfs7
    `SubClassM(c, d)   :- SubClass(c, d)`
    `SubClassM(c, e)   :- SubClassM(c, d), SubClassM(d, e)`     (3a) = rdfs11
    `TypeM(x, c)       :- TypeOf(x, c)`
    `TypeM(x, d)       :- SubClassM(c, d), TypeM(x, c)`         (3b) = rdfs9
    `TypeM(x, c)       :- Dom(p, c), TripleM(x, p, o)`          (4a) = rdfs2
    `TypeM(o, c)       :- Range(p, c), TripleM(x, p, o)`        (4b) = rdfs3

  Side 2, the W3C rule set (RDF 1.1 Semantics, section 9.2.1
  "Patterns of RDFS entailment", section 8.1.1 pattern
  rdfD2, and the RDFS axiomatic triples of section 9,
  read 2026-09-15; the same rules as Apache Jena's
  `etc/rdfs.rules`, which lists the axiomatic triples and
  the closure rules under its own numbering, read
  2026-09-15).  The six patterns above, plus the typing that
  the axiomatic triples force and the two reflexivity
  patterns; typing by the built-in classes is kept in the
  unary relations `IsProp` (rdf:type rdf:Property) and
  `IsClass` (rdf:type rdfs:Class) since the built-in classes
  are not data values:
    `SubPropF(p, p)    :- IsProp(p)`                             rdfs6
    `SubClassF(c, c)   :- IsClass(c)`                            rdfs10
    `IsProp(p)   :- TripleF(s, p, o)`                            rdfD2
    `IsProp(p)   :- SubPropF(p, q)`   rdfs2 on (rdfs:subPropertyOf rdfs:domain rdf:Property)
    `IsProp(q)   :- SubPropF(p, q)`   rdfs3 on (rdfs:subPropertyOf rdfs:range rdf:Property)
    `IsProp(p)   :- Dom(p, c)`        rdfs2 on (rdfs:domain rdfs:domain rdf:Property)
    `IsProp(p)   :- Range(p, c)`      rdfs2 on (rdfs:range rdfs:domain rdf:Property)
    `IsClass(c)  :- TypeF(x, c)`      rdfs3 on (rdf:type rdfs:range rdfs:Class)
    `IsClass(c)  :- SubClassF(c, d)`  rdfs2 on (rdfs:subClassOf rdfs:domain rdfs:Class)
    `IsClass(d)  :- SubClassF(c, d)`  rdfs3 on (rdfs:subClassOf rdfs:range rdfs:Class)
    `IsClass(c)  :- Dom(p, c)`        rdfs3 on (rdfs:domain rdfs:range rdfs:Class)
    `IsClass(c)  :- Range(p, c)`      rdfs3 on (rdfs:range rdfs:range rdfs:Class)
  together with the F copies of the six shared patterns
  (`SubPropF`, `TripleF`, `SubClassF`, `TypeF`).  Omitted,
  because their conclusions only mention rdfs:Resource,
  rdfs:Literal, rdfs:Datatype or rdfs:member (outside the
  rho-df vocabulary, hence outside these relations): rdfs1,
  rdfs4a, rdfs4b, rdfs8, rdfs12, rdfs13, and the axiomatic
  triples not listed above.  Both sides are compiled by the
  repository's naive compiler (snapshots `…_aux`).

  Precondition `true`; postcondition
    `TripleM = TripleF ∧ TypeM = TypeF ∧`
    `SubPropM ∪ π[0,0] IsProp = SubPropF ∧`
    `SubClassM ∪ π[0,0] IsClass = SubClassF`.

  Expected verdict: valid; it sharpens Corollary 18 of Munoz
  et al. (G ⊢mrdf H iff G RDFS-entails H for mrdf-graphs
  when H has no (x, sp, x) or (x, sc, x) triple) to a
  statement of what the full closure adds: exactly one
  reflexive pair per property and per class, and those
  pairs feed nothing new into rdfs5, rdfs7, rdfs9, rdfs11.
  Expected obstruction: anchored.  The two loops are
  independent and merged side by side, and both apply one
  round of the same six patterns per iteration, so the
  invariant is round-by-round: `TripleF = TripleM`,
  `TypeF = TypeM`, `SubPropF = SubPropM ∪ π[0,0] IsProp_aux`,
  `SubClassF = SubClassM ∪ π[0,0] IsClass_aux` (the
  reflexive pairs lag one round behind the typing that
  produces them), with the second loop possibly running
  longer while `IsProp`, `IsClass` settle.

  Why it matters: triple stores compute RDFS closures with
  rule sets of their own choosing (Jena ships several
  `rdfs*.rules` files, RDFox and GraphDB their own
  profiles); the rho-df result says which rules may be
  dropped without changing entailment on ordinary data, and
  this case states the exact residue the dropped rules
  leave.  Example5021, which forgets that rdfs10 makes
  every class a subclass of itself, is invalid.

  Sources: S. Munoz, J. Perez, C. Gutierrez, "Simple and
  Efficient Minimal RDFS", Journal of Web Semantics 7(3),
  2009, https://doi.org/10.1016/j.websem.2009.07.003, read
  2026-09-15 from https://users.dcc.uchile.cl/~cgutierr/papers/jws09.pdf
  (Definition 3, Table 1, Definition 15, Proposition 17,
  Corollary 18).  W3C RDF 1.1 Semantics, Recommendation
  25 February 2014, https://www.w3.org/TR/rdf11-mt/, section
  8.1.1 (rdfD2), section 9 (RDFS axiomatic triples), section
  9.2.1 (rdfs1-rdfs13), read 2026-09-15.  Apache Jena,
  jena-core/src/main/resources/etc/rdfs.rules, main at
  commit f9eed353614c178b80b1e099ea2598e648014074
  (2026-09-14), read 2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5020

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {TypeOf, SubClass, SubProp, Dom, Range, TypeM, SubClassM, SubPropM, TypeM_aux,
      SubClassM_aux, SubPropM_aux, TypeF, SubClassF, SubPropF, TypeF_aux, SubClassF_aux,
      SubPropF_aux} (arity: 2),
    {Triple, TripleM, TripleM_aux, TripleF, TripleF_aux} (arity: 3),
    {IsProp, IsClass, IsProp_aux, IsClass_aux} (arity: 1)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      SubPropM_aux := ∅[2];
      TripleM_aux := ∅[3];
      SubClassM_aux := ∅[2];
      TypeM_aux := ∅[2];
      SubPropM := (SubProp ∪ π[0,3] (σ[#1 = #2] ((SubPropM_aux × SubPropM_aux))));
      TripleM := (Triple ∪ π[2,1,4] (σ[#0 = #3] ((SubPropM_aux × TripleM_aux))));
      SubClassM := (SubClass ∪ π[0,3] (σ[#1 = #2] ((SubClassM_aux × SubClassM_aux))));
      TypeM := (TypeOf ∪ (π[2,1] (σ[#0 = #3] ((SubClassM_aux × TypeM_aux))) ∪ (π[2,1] (σ[#0 = #3] ((Dom × TripleM_aux))) ∪ π[4,1] (σ[#0 = #3] ((Range × TripleM_aux))))));
      WHILE (¬(((SubPropM = SubPropM_aux) ∧ ((TripleM = TripleM_aux) ∧ ((SubClassM = SubClassM_aux) ∧ (TypeM = TypeM_aux)))))) DO
      SubPropM_aux := SubPropM;
      TripleM_aux := TripleM;
      SubClassM_aux := SubClassM;
      TypeM_aux := TypeM;
      SubPropM := (SubPropM ∪ (SubProp ∪ π[0,3] (σ[#1 = #2] ((SubPropM_aux × SubPropM_aux)))));
      TripleM := (TripleM ∪ (Triple ∪ π[2,1,4] (σ[#0 = #3] ((SubPropM_aux × TripleM_aux)))));
      SubClassM := (SubClassM ∪ (SubClass ∪ π[0,3] (σ[#1 = #2] ((SubClassM_aux × SubClassM_aux)))));
      TypeM := (TypeM ∪ (TypeOf ∪ (π[2,1] (σ[#0 = #3] ((SubClassM_aux × TypeM_aux))) ∪ (π[2,1] (σ[#0 = #3] ((Dom × TripleM_aux))) ∪ π[4,1] (σ[#0 = #3] ((Range × TripleM_aux)))))))
      END;
      SubPropF_aux := ∅[2];
      TripleF_aux := ∅[3];
      SubClassF_aux := ∅[2];
      TypeF_aux := ∅[2];
      IsProp_aux := ∅[1];
      IsClass_aux := ∅[1];
      SubPropF := (SubProp ∪ (π[0,3] (σ[#1 = #2] ((SubPropF_aux × SubPropF_aux))) ∪ π[0,0] (IsProp_aux)));
      TripleF := (Triple ∪ π[2,1,4] (σ[#0 = #3] ((SubPropF_aux × TripleF_aux))));
      SubClassF := (SubClass ∪ (π[0,3] (σ[#1 = #2] ((SubClassF_aux × SubClassF_aux))) ∪ π[0,0] (IsClass_aux)));
      TypeF := (TypeOf ∪ (π[2,1] (σ[#0 = #3] ((SubClassF_aux × TypeF_aux))) ∪ (π[2,1] (σ[#0 = #3] ((Dom × TripleF_aux))) ∪ π[4,1] (σ[#0 = #3] ((Range × TripleF_aux))))));
      IsProp := (π[1] (TripleF_aux) ∪ (π[0] (SubPropF_aux) ∪ (π[1] (SubPropF_aux) ∪ (π[0] (Dom) ∪ π[0] (Range)))));
      IsClass := (π[1] (TypeF_aux) ∪ (π[0] (SubClassF_aux) ∪ (π[1] (SubClassF_aux) ∪ (π[1] (Dom) ∪ π[1] (Range)))));
      WHILE (¬(((SubPropF = SubPropF_aux) ∧ ((TripleF = TripleF_aux) ∧ ((SubClassF = SubClassF_aux) ∧ ((TypeF = TypeF_aux) ∧ ((IsProp = IsProp_aux) ∧ (IsClass = IsClass_aux)))))))) DO
      SubPropF_aux := SubPropF;
      TripleF_aux := TripleF;
      SubClassF_aux := SubClassF;
      TypeF_aux := TypeF;
      IsProp_aux := IsProp;
      IsClass_aux := IsClass;
      SubPropF := (SubPropF ∪ (SubProp ∪ (π[0,3] (σ[#1 = #2] ((SubPropF_aux × SubPropF_aux))) ∪ π[0,0] (IsProp_aux))));
      TripleF := (TripleF ∪ (Triple ∪ π[2,1,4] (σ[#0 = #3] ((SubPropF_aux × TripleF_aux)))));
      SubClassF := (SubClassF ∪ (SubClass ∪ (π[0,3] (σ[#1 = #2] ((SubClassF_aux × SubClassF_aux))) ∪ π[0,0] (IsClass_aux))));
      TypeF := (TypeF ∪ (TypeOf ∪ (π[2,1] (σ[#0 = #3] ((SubClassF_aux × TypeF_aux))) ∪ (π[2,1] (σ[#0 = #3] ((Dom × TripleF_aux))) ∪ π[4,1] (σ[#0 = #3] ((Range × TripleF_aux)))))));
      IsProp := (IsProp ∪ (π[1] (TripleF_aux) ∪ (π[0] (SubPropF_aux) ∪ (π[1] (SubPropF_aux) ∪ (π[0] (Dom) ∪ π[0] (Range))))));
      IsClass := (IsClass ∪ (π[1] (TypeF_aux) ∪ (π[0] (SubClassF_aux) ∪ (π[1] (SubClassF_aux) ∪ (π[1] (Dom) ∪ π[1] (Range))))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (((TripleM = TripleF) ∧ (TypeM = TypeF)) ∧
      (((SubPropM ∪ π[0, 0] IsProp) = SubPropF) ∧ ((SubClassM ∪ π[0, 0] IsClass) = SubClassF)))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5020
end Benchmark
end Whiel
