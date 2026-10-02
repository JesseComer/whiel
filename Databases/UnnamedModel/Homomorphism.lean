-- Author: Jesse Comer
import Databases.UnnamedModel.Instance
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi

/-
  This file defines homomorphisms and core instances for
  unnamed database instances over the same schema.

  Key definitions include:
    * `Instance.Hom`
    * `Instance.Hom.id`
    * `Instance.Hom.comp`
    * `Instance.HomomorphicTo`
    * `Instance.subinstances`
    * `Instance.IsCore`

  Key theorems include:
    * `Instance.Hom.mem_of_mem`
    * `Instance.Hom.maps_Adom`
-/

------------------------------------------------------------
-- Instance Homomorphisms
------------------------------------------------------------

namespace Instance

variable {A D E F : Type}
variable {_ : RelationNames A}
variable [Domain D] [Domain E] [Domain F]
variable {Γ : UnnamedSchema A}

/-
  A homomorphism between same-schema instances maps domain
  values and preserves every relation tuple.
-/
structure Hom
    (I : Instance D Γ)
    (J : Instance E Γ) where
  toFun : D → E
  map_mem :
    ∀ X : Γ.syms,
      ∀ t : Tuple D (Γ.arity X),
        t ∈ I X →
          t.map toFun ∈ J X

namespace Hom

variable {I : Instance D Γ}
variable {J : Instance E Γ}
variable {K : Instance F Γ}

/- Map a tuple coordinatewise along a homomorphism. -/
def mapTuple
    (h : Hom I J)
    {n : Nat}
    (t : Tuple D n) :
    Tuple E n :=
  t.map h.toFun

@[simp] theorem mapTuple_get
    (h : Hom I J)
    {n : Nat}
    (t : Tuple D n)
    (i : Fin n) :
    (h.mapTuple t).get i = h.toFun (t.get i) := by
  change (h.mapTuple t)[i.1] = h.toFun t[i.1]
  simp [mapTuple, Vector.getElem_map]

/- Relation membership is preserved by a homomorphism. -/
theorem mem_of_mem
    (h : Hom I J)
    (X : Γ.syms)
    {t : Tuple D (Γ.arity X)}
    (ht : t ∈ I X) :
    h.mapTuple t ∈ J X := by
  exact h.map_mem X t ht

/- The identity map is an instance homomorphism. -/
def id
    (I : Instance D Γ) :
    Hom I I where
  toFun := fun d => d
  map_mem := by
    intro X t ht
    simpa using ht

/- Homomorphisms compose. -/
def comp
    (g : Hom J K)
    (h : Hom I J) :
    Hom I K where
  toFun := fun d => g.toFun (h.toFun d)
  map_mem := by
    intro X t ht
    simpa [mapTuple] using
      g.mem_of_mem X (h.mem_of_mem X ht)

/-
  Homomorphisms send active-domain elements to
  active-domain elements.
-/
theorem maps_Adom
    (h : Hom I J)
    {d : D}
    (hd : d ∈ I.Adom) :
    h.toFun d ∈ J.Adom := by
  rw [Instance.in_Adom_iff_in_Relation] at hd
  rw [Instance.in_Adom_iff_in_Relation]
  rcases hd with ⟨X, t, ht, hdMem⟩
  refine ⟨X, h.mapTuple t, h.mem_of_mem X ht, ?_⟩
  have hdList : d ∈ t.toList := by
    simpa using hdMem
  have hList :
      h.toFun d ∈ (h.mapTuple t).toList := by
    rw [mapTuple, Vector.toList_map]
    exact List.mem_map.mpr ⟨d, hdList, rfl⟩
  simpa using hList

end Hom

end Instance

------------------------------------------------------------
-- Homomorphism Existence
------------------------------------------------------------

namespace Instance

variable {A D E F : Type}
variable {_ : RelationNames A}
variable [Domain D] [Domain E] [Domain F]
variable {Γ : UnnamedSchema A}

/- A map from the active domain of `I` to that of `J`. -/
abbrev AdomMap
    (I : Instance D Γ)
    (J : Instance E Γ) : Type :=
  {d : D // d ∈ I.Adom} →
    {e : E // e ∈ J.Adom}

namespace AdomMap

variable {I : Instance D Γ}
variable {J : Instance E Γ}

/-
  Coordinatewise tuple image under an active-domain map.
-/
def mapTuple
    (f : AdomMap I J)
    {X : Γ.syms}
    (t : Tuple D (Γ.arity X))
    (ht : t ∈ I X) :
    Tuple E (Γ.arity X) :=
  Vector.ofFn
    (fun i =>
      (f
        ⟨t.get i,
          I.isTupleOver_Adom_of_mem ht i⟩).1)

end AdomMap

/-
  An active-domain map preserves all relation tuples from
  the source instance.
-/
def AdomMap.Preserves
    {I : Instance D Γ}
    {J : Instance E Γ}
    (f : AdomMap I J) : Prop :=
  ∀ X : Γ.syms,
    ∀ t : {t : Tuple D (Γ.arity X) // t ∈ I X},
      AdomMap.mapTuple f t.1 t.2 ∈ J X

instance
    {I : Instance D Γ}
    {J : Instance E Γ}
    (f : AdomMap I J) :
    Decidable f.Preserves := by
  unfold AdomMap.Preserves
  let _ : Fintype {X : A // X ∈ Γ.syms} :=
    Fintype.ofFinset Γ.syms
      (by intro X; simp)
  let _ :
      ∀ X : Γ.syms,
        Fintype {t : Tuple D (Γ.arity X) // t ∈ I X} := by
    intro X
    exact
      Fintype.ofFinset (I X)
        (by intro t; simp)
  infer_instance

/-
  There is a homomorphism from `I` to `J`. This is stated
  using finite active-domain maps, so it is decidable for
  finite instances without requiring `Fintype D`.
-/
def HomomorphicTo
    (I : Instance D Γ)
    (J : Instance E Γ) : Prop :=
  ∃ f : AdomMap I J, f.Preserves

instance
    (I : Instance D Γ)
    (J : Instance E Γ) :
    Decidable (I.HomomorphicTo J) := by
  unfold HomomorphicTo
  let _ : Fintype {d : D // d ∈ I.Adom} :=
    Fintype.ofFinset I.Adom
      (by intro d; simp)
  let _ : Fintype {e : E // e ∈ J.Adom} :=
    Fintype.ofFinset J.Adom
      (by intro e; simp)
  let _ : Fintype (AdomMap I J) := by
    infer_instance
  infer_instance

namespace HomomorphicTo

variable {I : Instance D Γ}
variable {J : Instance E Γ}
variable {K : Instance F Γ}

/- An explicit homomorphism gives homomorphism existence. -/
theorem of_hom
    (h : Hom I J) :
    I.HomomorphicTo J := by
  refine
    ⟨fun d => ⟨h.toFun d.1, h.maps_Adom d.2⟩,
      ?_⟩
  intro X t
  have hEq :
      AdomMap.mapTuple
          (fun d : {d : D // d ∈ I.Adom} =>
            ⟨h.toFun d.1, h.maps_Adom d.2⟩)
          t.1 t.2 =
        h.mapTuple t.1 := by
    apply Vector.ext
    intro i hi
    simp only [AdomMap.mapTuple, Hom.mapTuple,
      Vector.getElem_ofFn, Vector.getElem_map]
    rfl
  rw [hEq]
  exact h.mem_of_mem X t.2

/-
  Homomorphism existence yields an explicit homomorphism.
-/
theorem to_hom
    (h : I.HomomorphicTo J) :
    Nonempty (Hom I J) := by
  rcases h with ⟨f, hPres⟩
  let g : D → E :=
    fun d =>
      if hd : d ∈ I.Adom then
        (f ⟨d, hd⟩).1
      else
        default
  refine
    ⟨{ toFun := g
       map_mem := ?_ }⟩
  intro X t ht
  have hEq :
      t.map g = AdomMap.mapTuple f t ht := by
    apply Vector.ext
    intro i hi
    simp only [AdomMap.mapTuple, Vector.getElem_ofFn,
      Vector.getElem_map]
    have hd :
        t.get ⟨i, hi⟩ ∈ I.Adom :=
      I.isTupleOver_Adom_of_mem ht ⟨i, hi⟩
    change
      g (t.get ⟨i, hi⟩) =
        (f
          ⟨t.get ⟨i, hi⟩,
            I.isTupleOver_Adom_of_mem ht ⟨i, hi⟩⟩).1
    unfold g
    rw [dif_pos hd]
  rw [hEq]
  exact hPres X ⟨t, ht⟩

/- Active-domain existence agrees with explicit hom data. -/
theorem iff_nonempty_hom :
    I.HomomorphicTo J ↔ Nonempty (Hom I J) := by
  constructor
  · exact to_hom
  · rintro ⟨h⟩
    exact of_hom h

/- Homomorphism existence is reflexive. -/
theorem refl
    (I : Instance D Γ) :
    I.HomomorphicTo I :=
  of_hom (Hom.id I)

/- Homomorphism existence is transitive. -/
theorem trans
    (hIJ : I.HomomorphicTo J)
    (hJK : J.HomomorphicTo K) :
    I.HomomorphicTo K := by
  rcases to_hom hIJ with ⟨f⟩
  rcases to_hom hJK with ⟨g⟩
  exact of_hom (Hom.comp g f)

end HomomorphicTo

end Instance

------------------------------------------------------------
-- Finite Subinstances
------------------------------------------------------------

namespace Instance

variable {A D : Type}
variable {_ : RelationNames A}
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- A typed relation fact of a schema. -/
abbrev Fact
    (D : Type)
    [Domain D]
    (Γ : UnnamedSchema A) : Type :=
  Sigma (fun X : Γ.syms => Tuple D (Γ.arity X))

/- Finite set of all typed facts present in an instance. -/
def facts
    (I : Instance D Γ) :
    Finset (Fact D Γ) :=
  Γ.syms.attach.biUnion
    (fun X =>
      (I X).image
        (fun t => Sigma.mk X t))

/- Build an instance from a finite set of typed facts. -/
def instanceOfFacts
    (S : Finset (Fact D Γ)) :
    Instance D Γ :=
  fun X =>
    (S.1.filterMap
      (fun f =>
        match f with
        | ⟨Y, t⟩ =>
            if h : Y = X then
              some (Tuple.castArity (by rw [h]) t)
            else
              none)).toFinset

/- Finite enumeration of relation-wise subinstances. -/
def subinstances
    (I : Instance D Γ) :
    Finset (Instance D Γ) :=
  I.facts.powerset.image Instance.instanceOfFacts

end Instance

------------------------------------------------------------
-- Core Instances
------------------------------------------------------------

namespace Instance

variable {A D : Type}
variable {_ : RelationNames A}
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  An instance is a core when no enumerated proper
  subinstance receives a homomorphism from it.
-/
def IsCore
    (I : Instance D Γ) : Prop :=
  ∀ J : {J : Instance D Γ // J ∈ I.subinstances},
    ProperSubinstance J.1 I →
      ¬ HomomorphicTo I J.1

instance
    (I : Instance D Γ) :
    Decidable I.IsCore := by
  unfold IsCore
  let _ :
      Fintype
        {J : Instance D Γ // J ∈ I.subinstances} :=
    Fintype.ofFinset I.subinstances
      (by intro J; simp)
  infer_instance

/-
  Core instances have no homomorphism to an enumerated
  proper subinstance.
-/
theorem IsCore.no_hom
    {I J : Instance D Γ}
    (hCore : I.IsCore)
    (hMem : J ∈ I.subinstances)
    (hProper : ProperSubinstance J I) :
    ¬ HomomorphicTo I J :=
  hCore ⟨J, hMem⟩ hProper

end Instance
