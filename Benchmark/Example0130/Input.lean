-- Benchmark contributors: Fangzhu Shen, Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Example0130: the even/odd/ambiguous-depth path-system program is
  contained in every set closed under the basic path-system rules.

  Path systems (Cook): unary axioms A and ternary rules R(x,y,z), read as
  "if y and z are accessible then x is accessible". The basic program
    T(x) :- A(x).
    T(x) :- R(x,y,z), T(y), T(z).
  computes the accessible nodes T.

  The executed program refines T by the depth parity of derivation trees
  (an axiom is a leaf at depth 0):
    EH(x) :- A(x).                     x has a derivation whose leaves all lie at even depth
    OH(x) :- R(x,y,z), EH(y), EH(z).   ... all at odd depth
    EH(x) :- R(x,y,z), OH(y), OH(z).
    AH(x) :- R(x,y,z), Y(y), Z(z)      for every other pair (Y,Z) over EH/OH/AH:
                                       leaves at both parities (seven rules, (AH,AH) included)
  Every derivation of an accessible node is covered by one of these rules,
  so EH ∪ OH ∪ AH = T. The source path_systems_height.dl calls the three
  classes "even, odd and ambiguous height".

  Claim (containment by pre-fixpoint reasoning). Closed is a free unary
  relation the program never assigns. The precondition says Closed is
  closed under the basic rules,
    A ⊆ Closed   and   R(x,y,z) ∧ Closed(y) ∧ Closed(z) → Closed(x),
  and the postcondition says the three outputs lie inside it,
    AH ⊆ Closed ∧ EH ⊆ Closed ∧ OH ⊆ Closed.
  Closed ranges over all closed sets and T is the least of them, so the
  triple states EH ∪ OH ∪ AH ⊆ T. Expected verdict: valid, since every rule
  of the executed program derives x from A(x) or from R(x,y,z) and two
  facts already inside Closed.

  Encoding. Naive evaluation: AHNext/EHNext/OHNext hold the next round,
  AH/EH/OH the current one; at exit they agree and are the least fixpoint.
  A rule body R(x,y,z), Y(y), Z(z) is the expression
    π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × Y) × Z)))
  with columns 0..2 from R, 3 from Y and 4 from Z.

  Renaming from the legacy file, which reused the letter R for the closed
  set, called the rule relation RX, and named the outputs Ta/Tb/Tc:
    RX → R,  R → Closed,  Ta → AH, Sa → AHNext,  Tb → EH, Sb → EHNext,
    Tc → OH, Sc → OHNext.
  The legacy certificate (eight clauses: the two precondition conjuncts and
  Sa, Sb, Sc, Ta, Tb, Tc ⊆ R) certifies this same triple under the old
  names; it has not yet been regenerated under the new ones.


  Canonical form of the earlier single-level encoding of this case: the
  same schema, precondition, command and postcondition.

  Datalog program(s) recorded for this case:
  * rules as stated in the header comment of Input.lean (header comment):
      T(x) :- A(x).
      T(x) :- R(x,y,z), T(y), T(z).
      EH(x) :- A(x). x has a derivation whose leaves all lie at even depth
      OH(x) :- R(x,y,z), EH(y), EH(z). ... all at odd depth
      EH(x) :- R(x,y,z), OH(y), OH(z).
      AH(x) :- R(x,y,z), Y(y), Z(z) for every other pair (Y,Z) over EH/OH/AH:
-/

namespace Whiel
namespace Benchmark
namespace Example0130

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {A, Closed, AH, EH, OH, AHNext, EHNext, OHNext} (arity: 1),
    {R} (arity: 3)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((A ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × Closed) × Closed))))) ⊆ Closed)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      AH := ∅;
      EH := ∅;
      OH := ∅;
      AHNext :=
        (((((((π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × EH) × OH))))   -- AH(x) :- R(x,y,z), EH(y), OH(z)
        ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × OH) × EH)))))   -- AH(x) :- R(x,y,z), OH(y), EH(z)
        ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × AH) × OH)))))   -- AH(x) :- R(x,y,z), AH(y), OH(z)
        ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × OH) × AH)))))   -- AH(x) :- R(x,y,z), OH(y), AH(z)
        ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × AH) × EH)))))   -- AH(x) :- R(x,y,z), AH(y), EH(z)
        ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × EH) × AH)))))   -- AH(x) :- R(x,y,z), EH(y), AH(z)
        ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × AH) × AH)))));   -- AH(x) :- R(x,y,z), AH(y), AH(z)
      EHNext := (A ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × OH) × OH)))));   -- EH(x) :- A(x).   EH(x) :- R(x,y,z), OH(y), OH(z)
      OHNext := (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × EH) × EH))));   -- OH(x) :- R(x,y,z), EH(y), EH(z)
      WHILE ¬(((AHNext = AH) ∧ ((EHNext = EH) ∧ (OHNext = OH)))) DO
        AH := AHNext;
        EH := EHNext;
        OH := OHNext;
        AHNext :=
          (((((((π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × EH) × OH))))   -- AH(x) :- R(x,y,z), EH(y), OH(z)
          ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × OH) × EH)))))   -- AH(x) :- R(x,y,z), OH(y), EH(z)
          ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × AH) × OH)))))   -- AH(x) :- R(x,y,z), AH(y), OH(z)
          ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × OH) × AH)))))   -- AH(x) :- R(x,y,z), OH(y), AH(z)
          ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × AH) × EH)))))   -- AH(x) :- R(x,y,z), AH(y), EH(z)
          ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × EH) × AH)))))   -- AH(x) :- R(x,y,z), EH(y), AH(z)
          ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × AH) × AH)))));   -- AH(x) :- R(x,y,z), AH(y), AH(z)
        EHNext := (A ∪ (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × OH) × OH)))));   -- EH(x) :- A(x).   EH(x) :- R(x,y,z), OH(y), OH(z)
        OHNext := (π[0] (σ[#2 = #4] (σ[#1 = #3] ((R × EH) × EH))))   -- OH(x) :- R(x,y,z), EH(y), EH(z)
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((AH ⊆ Closed) ∧ ((EH ⊆ Closed) ∧ (OH ⊆ Closed)))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0130
end Benchmark
end Whiel
