-- Author: Jesse Comer
import Whiel.Concrete.Notation
import Whiel.Hoare.Preproc

open Whiel.Concrete

/-
  Synthesis-facing input for Example0012.
-/

namespace Whiel
namespace Benchmark
namespace Example0012

def programSchema : UnnamedSchema IndexAlphaName :=
  whielSch![
    {E, T, T_2, TBound} (arity: 2),
    _ (arity: 0)
  ]

def inputPre : AssertExpr Data programSchema :=
  assert![
    (E ∪
      (π[0, 3] (σ[#1 = #2] (TBound × E)))) ⊆ TBound
  ]

def inputCmd : Cmd Data programSchema :=
  whielCmd![
    { ExecSchema: programSchema }
    {
      T_2 := ∅;
      T := E ∪ (π[0, 3] (σ[#1 = #2] (T_2 × E)));
      WHILE T ≠ T_2 DO
        T_2 := T;
        T := T ∪ (E ∪
              (π[0, 3] (σ[#1 = #2] (T_2 × E))))
      END
    }
  ]

def inputPost : AssertExpr Data programSchema :=
  assert![
    ((E ∪ (π[0, 3] (σ[#1 = #2] (T × E)))) ⊆ T) ∧
      (T ⊆ TBound)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocessWithSupply inputPre inputCmd inputPost

end Example0012
end Benchmark
end Whiel
