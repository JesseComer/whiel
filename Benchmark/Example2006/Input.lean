-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  containment_04:
  Policy-filtered connectivity is contained in raw
  topological connectivity.

  Pair: transitive_closure_12 (Kubernetes/Cilium
  network-policy reachability: multi-hop connectivity over
  LinkE ∖ Denied) against plain transitive closure of the
  unfiltered topology LinkE (the reachability question
  Batfish answers on raw configurations).  Production
  meaning: network policies only ever remove connectivity.

  Method (equ.pdf, §Containment): run the filtered-closure
  program only, framed by a fresh relation RBound
  constrained to be a pre-fixpoint of the raw operator
      F1(X) = LinkE ∪ (X ∘ LinkE).
  The postcondition Conn ⊆ RBound bounds the filtered
  connectivity by lfp(F1) = TC(LinkE).  This mirrors the
  red-blue-alternating-paths ⊆ TC(R ∪ B) example worked
  out in equ.pdf.

  Provenance note (2026-09-15): the sources cited are
  documentation, not code. Network policies are modeled as a set
  of denied links; real Cilium policies are per flow and
  direction, and Batfish reachability is per flow over routing and
  ACLs. The claim survives the coarsening: policies only remove
  connectivity.


  Canonical form of the earlier single-level encoding of this
  case: the same schema, precondition, command and postcondition;
  the snapshot relation Conn_2 is now Conn_aux.

  Datalog program(s) recorded for this case:
  * prog_p (production check):
      ConnC(x1, y1) :- AllowedC(x1, y1).
      ConnC(x1, z1) :- ConnC(x1, y1), AllowedC(y1, z1).
-/

namespace Whiel
namespace Benchmark
namespace Example2006

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {LinkE, Denied, AllowedE, Conn, Conn_aux, RBound} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((LinkE ∪ (π[0, 3] (σ[#1 = #2] (RBound × LinkE)))) ⊆ RBound)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Conn_aux := ∅;
      AllowedE := (LinkE ∖ Denied);
      Conn := (LinkE ∖ Denied);
      WHILE Conn ≠ Conn_aux DO
        Conn_aux := Conn;
        Conn := (AllowedE ∪
          (π[0, 3] (σ[#1 = #2] (Conn_aux × AllowedE))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (Conn ⊆ RBound)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example2006
end Benchmark
end Whiel
