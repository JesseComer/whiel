-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  RDFS entailment by the rho-df rules against the full W3C
  rule set, with the reflexive subClassOf triples forgotten:
  the invalid twin of Example5020.

  Inputs, sides and encoding are those of Example5020: the
  rho-df system ⊢mrdf of Munoz, Perez and Gutierrez (rules
  (2)-(4)) computing `TypeM`, `SubClassM`, `SubPropM`,
  `TripleM`, and the W3C RDFS entailment patterns restricted
  to mrdf-graphs computing `TypeF`, `SubClassF`, `SubPropF`,
  `TripleF` with the built-in typing in `IsProp`, `IsClass`,
  both compiled by the naive compiler.

  The claim accounts for rdfs6 (every property is a
  subproperty of itself) but not for rdfs10 (every class is
  a subclass of itself):
    `TripleM = TripleF ∧ TypeM = TypeF ∧`
    `SubPropM ∪ π[0,0] IsProp = SubPropF ∧ SubClassM = SubClassF`.

  Expected verdict: invalid.  Witness: the single triple
  (20, rdf:type, 10), `TypeOf = {(20, 10)}`: the axiomatic
  triple (rdf:type rdfs:range rdfs:Class) with rdfs3 types
  10 as a class, and rdfs10 derives (10, rdfs:subClassOf,
  10), which rho-df does not (kernel-checked in
  Certificate/Invalid.lean).  Controls: a graph with
  properties but no classes, `Triple = {(20, 1, 21)}`,
  `SubProp = {(1, 2)}`, and the empty graph are not
  counterexamples.

  Why it matters: as for Example5020; this is the residue
  of the dropped rule (7) of Munoz et al. that an engine
  comparing closures across rule sets has to account for.

  Sources: as Example5020 (Munoz, Perez, Gutierrez, JWS
  2009; W3C RDF 1.1 Semantics sections 8.1.1, 9, 9.2.1;
  Apache Jena etc/rdfs.rules; all read 2026-09-15).
-/

namespace Whiel
namespace Benchmark
namespace Example5021

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
      (((SubPropM ∪ π[0, 0] IsProp) = SubPropF) ∧ (SubClassM = SubClassF)))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5021
end Benchmark
end Whiel
