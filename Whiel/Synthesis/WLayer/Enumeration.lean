-- Author: Jesse Comer
import Whiel.Synthesis.WLayer.Spec

/-
  Readable enumeration of a finite W-layer slice.

  Natural-number indices are retained as compact outputs.
  Full QF formulas are constructed only by `decode`.

  Main declarations:
    * `indices`, `decode`, and `clauses`
    * `mem_indices_iff`
    * `mem_clauses_iff`
-/

------------------------------------------------------------
-- Compact Index Enumeration
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace WLayer

namespace Enumeration

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- Compact representation used by this realization. -/
abbrev Representation := Nat

/- Enumerate the inclusive range of requested indices. -/
def indices
    (parameters : Parameters) :
    List Representation :=
  List.range (parameters.maxWIndex + 1)

/- Decode one compact index to its W formula. -/
def decode
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (index : Representation) :
    Clause D P.outSchema :=
  formula P index

/- Decode the readable compact enumeration. -/
def clauses
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (parameters : Parameters) :
    List (Clause D P.outSchema) :=
  (indices parameters).map (decode P)

@[simp] theorem mem_indices_iff
    (parameters : Parameters)
    (index : Representation) :
    index ∈ indices parameters ↔
      index ≤ parameters.maxWIndex := by
  simp [indices, Nat.lt_succ_iff]

theorem indices_nodup
    (parameters : Parameters) :
    (indices parameters).Nodup :=
  List.nodup_range

@[simp] theorem decode_eq
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (index : Representation) :
    decode P index = formula P index :=
  rfl

@[simp] theorem mem_clauses_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (parameters : Parameters)
    (clause : Clause D P.outSchema) :
    clause ∈ clauses P parameters ↔
      clause ∈
        (upTo P
          parameters.maxWIndex).clauses := by
  simp only [clauses, List.mem_map,
    mem_upTo_iff]
  constructor
  · rintro ⟨index, hMember, rfl⟩
    exact
      ⟨index,
        (mem_indices_iff
          parameters index).mp hMember,
        rfl⟩
  · rintro ⟨index, hBound, rfl⟩
    exact
      ⟨index,
        (mem_indices_iff
          parameters index).mpr hBound,
        rfl⟩

theorem clauses_sound
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (parameters : Parameters)
    {clause : Clause D P.outSchema}
    (hMember :
      clause ∈ clauses P parameters) :
    clause ∈
      (upTo P
        parameters.maxWIndex).clauses :=
  (mem_clauses_iff
    P parameters clause).mp hMember

theorem clauses_complete
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (parameters : Parameters)
    {clause : Clause D P.outSchema}
    (hMember :
      clause ∈
        (upTo P
          parameters.maxWIndex).clauses) :
    clause ∈ clauses P parameters :=
  (mem_clauses_iff
    P parameters clause).mpr hMember

end Enumeration

end WLayer

end Synthesis

end Whiel
