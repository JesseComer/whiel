-- Author: Jesse Comer
import Databases.Core.UnnamedSchema
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Pi

/-
  This file defines finite database instances over unnamed
  relational schemas. It contains the active-domain
  construction, schema extension/reduct operations, and
  update operations used by unnamed relational languages.

  Key definitions include:
    * `Instance`
    * `Instance.Subset`
    * `Instance.agreeOn`
    * `Instance.agreeOnRelations`
    * `Instance.Adom`
    * `Instance.AdomEmpty`
    * `Instance.NullaryAssignment`
    * `Instance.ofNullaryAssignment`
    * `Instance.Extends`
    * `Instance.reduct`
    * `Instance.expandEmpty`
    * `Instance.update`

  Key theorems include:
    * `Instance.in_Adom_iff_in_Relation`
    * `Instance.adomEmpty_iff_exists_nullaryAssignment`
    * `Instance.Extends_iff_relation_tuple`
-/

------------------------------------------------------------
-- Instance Type
------------------------------------------------------------

/-
  An instance over schema `Γ` assigns each name in `Γ` a
  relation of that name's arity in `Γ`.
-/
def Instance
  {A : Type} {_ : RelationNames A}
  (D : Type) [Domain D]
  (Γ : UnnamedSchema A) :=
  (s : {sym : A // sym ∈ Γ.syms}) →
    FinRelation D (Γ.arity s)

------------------------------------------------------------
-- Basic Instance Relations
------------------------------------------------------------

namespace Instance

variable {A D : Type} {_ : RelationNames A} [Domain D]
variable {Γ : UnnamedSchema A}

instance
    {Γ : UnnamedSchema A} :
    DecidableEq (Instance D Γ) := by
  unfold Instance
  infer_instance

/-
  Instances over the same schema which agree on all
  relation names are identical.
-/
@[ext] theorem ext {I J : Instance D Γ}
    (h : ∀ s, I s = J s) : I = J := by
  funext s
  exact h s

/-
  Pointwise inclusion between two instances over the same
  schema.
-/
def Subset (I J : Instance D Γ) : Prop :=
  ∀ s : Γ.syms, I s ⊆ J s

/-
  Strict pointwise inclusion between two instances over the
  same schema.
-/
def ProperSubinstance (J I : Instance D Γ) : Prop :=
  J.Subset I ∧ ¬ I.Subset J

instance
    (I J : Instance D Γ) :
    Decidable (I.Subset J) := by
  unfold Subset
  infer_instance

instance
    (J I : Instance D Γ) :
    Decidable (J.ProperSubinstance I) := by
  unfold ProperSubinstance
  infer_instance

/- Pointwise inclusion is reflexive. -/
theorem Subset.refl
    (I : Instance D Γ) :
    I.Subset I := by
  intro X t ht
  exact ht

/- Pointwise inclusion is transitive. -/
theorem Subset.trans
    {I J K : Instance D Γ}
    (hIJ : I.Subset J)
    (hJK : J.Subset K) :
    I.Subset K := by
  intro X t ht
  exact hJK X (hIJ X ht)

/-
  Mutual pointwise inclusion is equivalent to extensional
  equality of instances.
-/
theorem Subset.antisymm_iff
    {I J : Instance D Γ} :
    I.Subset J ∧ J.Subset I ↔ I = J := by
  constructor
  · intro h
    apply Instance.ext
    intro X
    apply Finset.Subset.antisymm
    · exact h.1 X
    · exact h.2 X
  · intro h
    subst h
    exact ⟨Subset.refl I, Subset.refl I⟩

/-
  A proper subinstance is a subinstance which is not
  extensionally equal to the ambient instance.
-/
theorem ProperSubinstance_iff_subset_ne
    {J I : Instance D Γ} :
    J.ProperSubinstance I ↔ J.Subset I ∧ J ≠ I := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro hEq
    apply h.2
    subst hEq
    exact Subset.refl _
  · intro h
    refine ⟨h.1, ?_⟩
    intro hIJ
    exact h.2 ((Subset.antisymm_iff).mp ⟨h.1, hIJ⟩)

/- Agreement on symbols whose raw names lie in `S`. -/
def agreeOn
    (S : Finset A)
    (I J : Instance D Γ) : Prop :=
  ∀ X : Γ.syms, X.1 ∈ S → I X = J X

/- Agreement on `S` transfers to subsets. -/
theorem agreeOn_of_subset
    {S T : Finset A}
    {I J : Instance D Γ}
    (hSub : T ⊆ S)
    (hAgree : agreeOn S I J) :
    agreeOn T I J := by
  intro X hX
  exact hAgree X (hSub hX)

/- Agreement is symmetric. -/
theorem agreeOn_symm
    {S : Finset A}
    {I J : Instance D Γ}
    (hAgree : agreeOn S I J) :
    agreeOn S J I := by
  intro X hX
  exact (hAgree X hX).symm

/-
  Partial raw-name lookup for the relation assigned by an
  instance.
-/
def relation?
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    (X : A) :
    Option (Sigma (FinRelation D)) :=
  if hX : X ∈ Γ.syms then
    some ⟨Γ.arity ⟨X, hX⟩, I ⟨X, hX⟩⟩
  else
    none

/-
  Cross-schema relation agreement on a finite set of raw
  relation names.
-/
def agreeOnRelations
    {Γ Δ : UnnamedSchema A}
    (S : Finset A)
    (I : Instance D Γ)
    (J : Instance D Δ) : Prop :=
  ∀ X, X ∈ S → I.relation? X = J.relation? X

instance
    {Γ Δ : UnnamedSchema A}
    (S : Finset A)
    (I : Instance D Γ)
    (J : Instance D Δ) :
    Decidable (I.agreeOnRelations S J) := by
  dsimp [agreeOnRelations]
  infer_instance

/- Relation agreement on `S` transfers to subsets. -/
theorem agreeOnRelations_of_subset
    {Γ Δ : UnnamedSchema A}
    {S T : Finset A}
    {I : Instance D Γ}
    {J : Instance D Δ}
    (hSub : T ⊆ S)
    (hAgree : I.agreeOnRelations S J) :
    I.agreeOnRelations T J := by
  intro X hX
  exact hAgree X (hSub hX)

/- Relation agreement is symmetric. -/
theorem agreeOnRelations_symm
    {Γ Δ : UnnamedSchema A}
    {S : Finset A}
    {I : Instance D Γ}
    {J : Instance D Δ}
    (hAgree : I.agreeOnRelations S J) :
    J.agreeOnRelations S I := by
  intro X hX
  exact (hAgree X hX).symm

/- Same-schema agreement implies raw relation agreement. -/
theorem agreeOnRelations_of_agreeOn
    {S : Finset A}
    {I J : Instance D Γ}
    (hAgree : I.agreeOn S J) :
    I.agreeOnRelations S J := by
  intro X hX
  unfold relation?
  by_cases hMem : X ∈ Γ.syms
  · simp [hMem, hAgree ⟨X, hMem⟩ hX]
  · simp [hMem]

end Instance

------------------------------------------------------------
-- Empty Instances And Active Domains
------------------------------------------------------------

namespace Instance

variable {A D : Type} {_ : RelationNames A} [Domain D]
variable {Γ : UnnamedSchema A}

/- The empty instance: every relation is empty. -/
def empty (Γ : UnnamedSchema A) : Instance D Γ :=
  fun _ => ∅

/-
  The empty instance maps every relation name to the empty
  relation.
-/
@[simp] theorem empty_apply
    (Γ : UnnamedSchema A)
    (s : {sym : A // sym ∈ Γ.syms}) :
    (empty (A := A) (D := D) Γ) s = ∅ := rfl

/-
  Active domain of an instance: all values occurring in
  some tuple of some interpreted relation.
-/
def Adom (I : Instance D Γ) : Finset D :=
  Finset.fold (op := (· ∪ ·)) ∅
    (fun s : Γ.syms =>
      Finset.fold (op := (· ∪ ·)) ∅
        (fun t => t.toList.toFinset) (I s))
    Γ.syms.attach

/- An instance has no values in its active domain. -/
def AdomEmpty (I : Instance D Γ) : Prop :=
  I.Adom = ∅

instance
    (I : Instance D Γ) :
    Decidable I.AdomEmpty := by
  unfold AdomEmpty
  infer_instance

/- A relation symbol whose arity is zero. -/
def NullarySymbol (Γ : UnnamedSchema A) :=
  {X : Γ.syms // Γ.arity X = 0}

instance
    [Fintype Γ.syms] :
    Fintype (NullarySymbol Γ) := by
  unfold NullarySymbol
  infer_instance

/-
  Boolean interpretations of exactly the nullary symbols.
-/
def NullaryAssignment (Γ : UnnamedSchema A) :=
  NullarySymbol Γ → Bool

instance
    [Fintype Γ.syms] :
    Fintype (NullaryAssignment Γ) := by
  unfold NullaryAssignment NullarySymbol
  infer_instance

/- Instance represented by a nullary assignment. -/
def ofNullaryAssignment
    (χ : NullaryAssignment Γ) : Instance D Γ :=
  fun X =>
    if hAr : Γ.arity X = 0 then
      if χ ⟨X, hAr⟩ then
        {cast (congrArg (Tuple D) hAr.symm) Tuple.empty}
      else
        ∅
    else
      ∅

/- Extract the nullary truth values of an instance. -/
def toNullaryAssignment
    (I : Instance D Γ) : NullaryAssignment Γ :=
  fun X => decide (I X.1).Nonempty

theorem in_Adom_iff_in_Relation
    (I : Instance D Γ)
    {d : D} :
    d ∈ I.Adom ↔
      ∃ s : Γ.syms,
        ∃ t ∈ I s, d ∈ t.toList.toFinset := by
  let _ : Std.Associative
      (fun x y : Finset D => x ∪ y) :=
    ⟨fun x y z => Finset.union_assoc x y z⟩
  let _ : Std.Commutative
      (fun x y : Finset D => x ∪ y) :=
    ⟨fun x y => Finset.union_comm x y⟩
  have hRel :
      ∀ {n : Nat} (R : FinRelation D n),
        d ∈ Finset.fold
            (op := (· ∪ ·)) ∅
            (fun t => t.toList.toFinset) R ↔
          ∃ t ∈ R, d ∈ t.toList.toFinset := by
    intro n R
    induction R using Finset.induction_on with
    | empty =>
        simp
    | @insert t R ht ih =>
        rw [Finset.fold_insert ht]
        rw [Finset.mem_union, ih]
        constructor
        · intro h
          rcases h with h | h
          · exact ⟨t, Finset.mem_insert_self _ _,
              by simpa using h⟩
          · rcases h with ⟨u, huR, hud⟩
            exact ⟨u, Finset.mem_insert_of_mem huR, hud⟩
        · rintro ⟨u, hu, hud⟩
          rcases Finset.mem_insert.mp hu with rfl | huR
          · exact Or.inl (by simpa using hud)
          · exact Or.inr ⟨u, huR, hud⟩
  have hOuter :
      ∀ (S : Finset Γ.syms),
        d ∈ Finset.fold
            (op := (· ∪ ·)) ∅
            (fun s : Γ.syms =>
              Finset.fold
                (op := (· ∪ ·)) ∅
                (fun t => t.toList.toFinset)
                (I s)) S ↔
          ∃ s ∈ S,
            ∃ t ∈ I s, d ∈ t.toList.toFinset := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simp
    | @insert s S hs ih =>
        rw [Finset.fold_insert hs]
        rw [Finset.mem_union]
        rw [hRel, ih]
        constructor
        · intro h
          rcases h with h | h
          · rcases h with ⟨t, ht, hd⟩
            exact
              ⟨s, Finset.mem_insert_self _ _, t, ht, hd⟩
          · rcases h with ⟨u, huS, t, ht, hd⟩
            exact ⟨u, Finset.mem_insert_of_mem huS,
              t, ht, hd⟩
        · rintro ⟨u, hu, t, ht, hd⟩
          rcases Finset.mem_insert.mp hu with rfl | huS
          · exact Or.inl ⟨t, ht, hd⟩
          · exact Or.inr ⟨u, huS, t, ht, hd⟩
  simpa [Instance.Adom] using
    hOuter Γ.syms.attach

/- The canonical empty instance is adom-empty. -/
theorem empty_adomEmpty
    (Γ : UnnamedSchema A) :
    (empty (A := A) (D := D) Γ).AdomEmpty := by
  apply Finset.ext
  intro d
  rw [in_Adom_iff_in_Relation]
  simp

/- Membership in a nullary-assignment instance. -/
theorem mem_ofNullaryAssignment_iff
    (χ : NullaryAssignment Γ)
    (X : Γ.syms)
    (t : Tuple D (Γ.arity X)) :
    t ∈ ofNullaryAssignment χ X ↔
      ∃ hAr : Γ.arity X = 0,
        χ ⟨X, hAr⟩ = true := by
  unfold ofNullaryAssignment
  by_cases hAr : Γ.arity X = 0
  · simp only [dif_pos hAr]
    by_cases hχ : χ ⟨X, hAr⟩ = true
    · simp only [if_pos hχ, Finset.mem_singleton]
      constructor
      · intro _ht
        exact ⟨hAr, hχ⟩
      · intro _h
        apply Vector.ext
        intro i hi
        have hiZero : i < 0 := by
          rw [hAr] at hi
          exact hi
        exact False.elim (Nat.not_lt_zero i hiZero)
    · simp [hAr, hχ]
  · simp [hAr]

/-
  Positive-arity relations represented this way are empty.
-/
theorem ofNullaryAssignment_eq_empty_of_pos
    (χ : NullaryAssignment Γ)
    (X : Γ.syms)
    (hAr : Γ.arity X ≠ 0) :
    ofNullaryAssignment (D := D) χ X = ∅ := by
  unfold ofNullaryAssignment
  simp [hAr]

/- Every nullary-assignment instance is adom-empty. -/
theorem ofNullaryAssignment_adomEmpty
    (χ : NullaryAssignment Γ) :
    (ofNullaryAssignment (D := D) χ).AdomEmpty := by
  apply Finset.ext
  intro d
  constructor
  · intro hd
    rw [in_Adom_iff_in_Relation] at hd
    rcases hd with ⟨X, t, ht, hdt⟩
    rw [mem_ofNullaryAssignment_iff] at ht
    rcases ht with ⟨hAr, _hχ⟩
    have hLen : t.toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp [Vector.length_toList, hAr]
    simp [hLen] at hdt
  · intro hd
    simp at hd

/-
  Positive-arity relations of an adom-empty instance vanish.
-/
theorem relation_eq_empty_of_adomEmpty
    (I : Instance D Γ)
    (hI : I.AdomEmpty)
    (X : Γ.syms)
    (hAr : Γ.arity X ≠ 0) :
    I X = ∅ := by
  apply Finset.ext
  intro t
  constructor
  · intro ht
    let i : Fin (Γ.arity X) :=
      ⟨0, Nat.pos_of_ne_zero hAr⟩
    have hCoord : t.get i ∈ I.Adom := by
      rw [in_Adom_iff_in_Relation]
      exact ⟨X, t, ht,
        Tuple.mem_toList_toFinset_of_get t i⟩
    rw [hI] at hCoord
    exact False.elim
      (Finset.notMem_empty (t.get i) hCoord)
  · intro ht
    exact False.elim (Finset.notMem_empty t ht)

/-
  Reconstruct an adom-empty instance from its assignment.
-/
theorem eq_ofNullaryAssignment_toNullaryAssignment
    (I : Instance D Γ)
    (hI : I.AdomEmpty) :
    I = ofNullaryAssignment I.toNullaryAssignment := by
  apply Instance.ext
  intro X
  apply Finset.ext
  intro t
  rw [mem_ofNullaryAssignment_iff]
  constructor
  · intro ht
    have hAr : Γ.arity X = 0 := by
      by_contra hAr
      have hEmpty :=
        relation_eq_empty_of_adomEmpty I hI X hAr
      rw [hEmpty] at ht
      exact Finset.notMem_empty t ht
    refine ⟨hAr, ?_⟩
    exact decide_eq_true ⟨t, ht⟩
  · rintro ⟨hAr, hChoice⟩
    have hNonempty : (I X).Nonempty := by
      exact of_decide_eq_true hChoice
    rcases hNonempty with ⟨u, hu⟩
    have hEq : t = u := by
      apply Vector.ext
      intro i hi
      have hiZero : i < 0 := by
        rw [hAr] at hi
        exact hi
      exact False.elim (Nat.not_lt_zero i hiZero)
    simpa [hEq] using hu

/- Characterization of adom-empty instances. -/
theorem adomEmpty_iff_exists_nullaryAssignment
    (I : Instance D Γ) :
    I.AdomEmpty ↔
      ∃ χ : NullaryAssignment Γ,
        I = ofNullaryAssignment χ := by
  constructor
  · intro hI
    exact
      ⟨I.toNullaryAssignment,
        eq_ofNullaryAssignment_toNullaryAssignment I hI⟩
  · rintro ⟨χ, rfl⟩
    exact ofNullaryAssignment_adomEmpty χ

/- Without nullary symbols, adom-empty means empty. -/
theorem eq_empty_of_adomEmpty
    (I : Instance D Γ)
    (hI : I.AdomEmpty)
    (hPos : ∀ X : Γ.syms, Γ.arity X ≠ 0) :
    I = empty Γ := by
  apply Instance.ext
  intro X
  rw [relation_eq_empty_of_adomEmpty I hI X (hPos X)]
  rfl

theorem isTupleOver_Adom_of_mem
    (I : Instance D Γ)
    {s : Γ.syms}
    {t : Tuple D (Γ.arity s)}
    (ht : t ∈ I s) :
    t.isTupleOver I.Adom := by
  intro i
  rw [in_Adom_iff_in_Relation]
  exact ⟨s, t, ht,
    Tuple.mem_toList_toFinset_of_get t i⟩

end Instance

------------------------------------------------------------
-- Schema Extension Helpers
------------------------------------------------------------

namespace Instance

variable {A D : Type} {_ : RelationNames A} [Domain D]
variable {Γ : UnnamedSchema A}

omit [Domain D] in
private theorem mem_castFinRelation_iff
    {m n : Nat}
    (h : m = n)
    (R : FinRelation D m)
    (t : Tuple D n) :
    t ∈ cast (congrArg (FinRelation D) h) R ↔
      Tuple.castArity h t ∈ R := by
  cases h
  rfl

/-
  The relation of a symbol from `Γ`, transported to the
  corresponding arity in an extension schema `Δ`.
-/
def relationOfExtension
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Γ)
    (X : Δ.syms)
    (hX : X.1 ∈ Γ.syms) :
    FinRelation D (Δ.arity X) :=
  cast
    (congrArg (FinRelation D)
      (UnnamedSchema.arity_eq_of_extension_mem hExt X hX))
    (I ⟨X.1, hX⟩)

/-
  Membership in `relationOfExtension` is just membership in
  the original relation after transporting the tuple arity.
-/
theorem relationOfExtension_mem_iff
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Γ)
    (X : Δ.syms)
    (hX : X.1 ∈ Γ.syms)
    (t : Tuple D (Δ.arity X)) :
    t ∈ relationOfExtension hExt I X hX ↔
      Tuple.castArity
          (UnnamedSchema.arity_eq_of_extension_mem
            hExt X hX) t ∈
        I ⟨X.1, hX⟩ := by
  exact
    mem_castFinRelation_iff
      (UnnamedSchema.arity_eq_of_extension_mem hExt X hX)
      (I ⟨X.1, hX⟩) t

/-
  `J.Extends hExt I` means that the larger-schema instance
  `J` agrees with `I` on the smaller schema.
-/
def Extends
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Γ)
    (J : Instance D Δ) : Prop :=
  ∀ X : Δ.syms,
    ∀ hX : X.1 ∈ Γ.syms,
      J X = relationOfExtension hExt I X hX

instance
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Γ)
    (J : Instance D Δ) :
    Decidable (Extends hExt I J) := by
  unfold Extends
  infer_instance

/-
  Characterization of extension in tuple-membership terms.
-/
theorem Extends_iff_relation_tuple
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Γ)
    (J : Instance D Δ) :
    Extends hExt I J ↔
      ∀ X : Δ.syms,
        ∀ hX : X.1 ∈ Γ.syms,
          ∀ t : Tuple D (Δ.arity X),
            t ∈ J X ↔
              Tuple.castArity
                  (UnnamedSchema.arity_eq_of_extension_mem
                    hExt X hX) t ∈
                I ⟨X.1, hX⟩ := by
  constructor
  · intro hExtends X hX t
    rw [hExtends X hX]
    exact relationOfExtension_mem_iff hExt I X hX t
  · intro hRel X hX
    apply Finset.ext
    intro t
    exact (hRel X hX t).trans
      (relationOfExtension_mem_iff hExt I X hX t).symm

end Instance

------------------------------------------------------------
-- Reducts And Expansions
------------------------------------------------------------

namespace Instance

variable {A D : Type} {_ : RelationNames A} [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Reduct along schema extension: interpret an instance on a
  larger schema `Δ` as one on smaller schema `Γ`,
  forgetting extra names.
-/
def reduct
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Δ) :
    Instance D Γ := by
  intro s
  exact cast
    (congrArg
      (FinRelation D)
      (UnnamedSchema.arity_eq_of_extensionOf hExt s))
    (I ⟨s.1, hExt.1 s.2⟩)

/-
  Membership in a reduct is membership in the larger
  instance after transporting the tuple to the larger arity.
-/
theorem reduct_mem_iff
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Δ)
    (X : Γ.syms)
    (t : Tuple D (Γ.arity X)) :
    t ∈ reduct hExt I X ↔
      Tuple.toExtension hExt X t ∈
        I (UnnamedSchema.symOfExtension hExt X) := by
  exact
    mem_castFinRelation_iff
      (UnnamedSchema.arity_eq_of_extensionOf hExt X)
      (I (UnnamedSchema.symOfExtension hExt X)) t

/- A reduct cannot introduce active-domain elements. -/
theorem Adom_reduct_subset
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Δ) :
    (reduct hExt I).Adom ⊆ I.Adom := by
  intro d hd
  rw [Instance.in_Adom_iff_in_Relation] at hd
  rw [Instance.in_Adom_iff_in_Relation]
  rcases hd with ⟨X, t, ht, hdt⟩
  refine
    ⟨UnnamedSchema.symOfExtension hExt X,
      Tuple.toExtension hExt X t, ?_, ?_⟩
  · exact (reduct_mem_iff hExt I X t).mp ht
  · have hList :
        (Tuple.toExtension hExt X t).toList =
          t.toList := by
      unfold Tuple.toExtension
      exact Tuple.castArity_toList
        (UnnamedSchema.arity_eq_of_extensionOf
          hExt X) t
    rw [hList]
    exact hdt

/-
  Reducing an extending instance recovers the smaller
  instance.
-/
theorem reduct_eq_of_extends
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    {I : Instance D Γ}
    {J : Instance D Δ}
    (hJ : Extends hExt I J) :
    reduct hExt J = I := by
  apply Instance.ext
  intro X
  apply Finset.ext
  intro t
  rw [reduct_mem_iff]
  rw [hJ (UnnamedSchema.symOfExtension hExt X) X.2]
  rw [relationOfExtension_mem_iff]
  have hCast :
      Tuple.castArity
          (UnnamedSchema.arity_eq_of_extension_mem hExt
            (UnnamedSchema.symOfExtension hExt X) X.2)
          (Tuple.toExtension hExt X t) = t := by
    let hAr := UnnamedSchema.arity_eq_of_extensionOf hExt X
    let hMem :=
      UnnamedSchema.arity_eq_of_extension_mem hExt
        (UnnamedSchema.symOfExtension hExt X) X.2
    change Tuple.castArity hMem (Tuple.castArity hAr t) = t
    rw [Tuple.castArity_proof_irrel hMem hAr.symm]
    exact Tuple.castArity_symm hAr t
  have hXEq :
      (⟨(UnnamedSchema.symOfExtension hExt X).1, X.2⟩ :
        Γ.syms) = X := by
    exact Subtype.ext rfl
  rw [hCast]
  cases hXEq
  rfl

/-
  If a reduct is equal to a smaller instance, the larger
  instance extends it.
-/
theorem extends_of_reduct_eq
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    {I : Instance D Γ}
    {J : Instance D Δ}
    (hReduct : reduct hExt J = I) :
    Extends hExt I J := by
  intro Y hY
  let X : Γ.syms := ⟨Y.1, hY⟩
  have hSym : UnnamedSchema.symOfExtension hExt X = Y := by
    exact Subtype.ext rfl
  cases hSym
  apply Finset.ext
  intro t
  rw [relationOfExtension_mem_iff]
  rw [← hReduct]
  rw [reduct_mem_iff hExt J X]
  have hCast :
      Tuple.toExtension hExt X
          (Tuple.castArity
            (UnnamedSchema.arity_eq_of_extension_mem hExt
              Y hY)
            t) = t := by
    let hAr := UnnamedSchema.arity_eq_of_extensionOf hExt X
    let hMem :=
      UnnamedSchema.arity_eq_of_extension_mem hExt Y hY
    change Tuple.castArity hAr (Tuple.castArity hMem t) = t
    rw [Tuple.castArity_trans]
    rw [Tuple.castArity_proof_irrel (hAr.trans hMem) rfl]
    rfl
  change t ∈ J Y ↔
    Tuple.toExtension hExt X
        (Tuple.castArity
          (UnnamedSchema.arity_eq_of_extension_mem
            hExt Y hY)
          t) ∈ J Y
  constructor
  · intro ht
    simpa [hCast] using ht
  · intro ht
    simpa [hCast] using ht

/- Reduct along the reflexive extension is the identity. -/
@[simp] theorem reduct_refl
    (I : Instance D Γ) :
    reduct (UnnamedSchema.extensionOf_refl Γ) I = I := by
  ext X
  unfold reduct
  simp

/-
  Expansion along schema extension: interpret an instance on
  a smaller schema `Γ` as one on larger schema `Δ`,
  mapping names not in `Γ` to the empty relation.
-/
def expandEmpty
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Γ) :
    Instance D Δ := by
  intro t
  by_cases ht : t.1 ∈ Γ.syms
  · exact relationOfExtension hExt I t ht
  · exact ∅

/-
  Membership in an empty expansion at an old symbol is
  membership in the original relation after transporting the
  tuple arity.
-/
theorem expandEmpty_mem_iff_of_mem
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Γ)
    (X : Δ.syms)
    (hX : X.1 ∈ Γ.syms)
    (t : Tuple D (Δ.arity X)) :
    t ∈ expandEmpty hExt I X ↔
      Tuple.castArity
          (UnnamedSchema.arity_eq_of_extension_mem
            hExt X hX) t ∈
        I ⟨X.1, hX⟩ := by
  unfold expandEmpty
  simp [hX, relationOfExtension_mem_iff]

/- Empty expansion sends new symbols to ∅. -/
theorem expandEmpty_eq_empty_of_not_mem
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Γ)
    (X : Δ.syms)
    (hX : X.1 ∉ Γ.syms) :
    expandEmpty hExt I X = ∅ := by
  unfold expandEmpty
  simp [hX]

/-
  Reducing the empty-expansion of an instance along the same
  extension proof recovers the original instance.
-/
theorem reduct_expandEmpty
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (I : Instance D Γ) :
    reduct hExt (expandEmpty hExt I) = I := by
  apply Instance.ext
  intro s
  unfold reduct expandEmpty relationOfExtension
  simp [s.2]

/-
  `I.reductOf J` means `I` is obtained from `J` by
  reducing along some schema extension.
-/
def reductOf
    {Γ Δ : UnnamedSchema A}
    (I : Instance D Γ)
    (J : Instance D Δ) : Prop :=
  ∃ hExt : Δ.extensionOf Γ, reduct hExt J = I

instance
    {Γ Δ : UnnamedSchema A}
    (I : Instance D Γ)
    (J : Instance D Δ) :
    Decidable (I.reductOf J) := by
  dsimp [reductOf]
  infer_instance

/-
  Characterization of `reductOf` in tuple-membership terms.
-/
theorem reductOf_iff_reduct_tuple
    {Γ Δ : UnnamedSchema A}
    (I : Instance D Γ)
    (J : Instance D Δ) :
    I.reductOf J ↔
      ∃ hExt : Δ.extensionOf Γ,
        ∀ X : Γ.syms,
          ∀ t : Tuple D (Γ.arity X),
            t ∈ I X ↔
              Tuple.toExtension hExt X t ∈
                J
                  (UnnamedSchema.symOfExtension
                    hExt X) := by
  constructor
  · rintro ⟨hExt, hReduct⟩
    refine ⟨hExt, ?_⟩
    intro X t
    have hMem := reduct_mem_iff hExt J X t
    simpa [hReduct] using hMem
  · rintro ⟨hExt, hRel⟩
    refine ⟨hExt, ?_⟩
    apply Instance.ext
    intro X
    apply Finset.ext
    intro t
    exact (reduct_mem_iff hExt J X t).trans
      (hRel X t).symm

/-
  `J.expansionOf I` means `J` is obtained from `I` by
  empty-expanding along some extension.
-/
def expansionOf
    {Γ Δ : UnnamedSchema A}
    (J : Instance D Δ)
    (I : Instance D Γ) : Prop :=
  ∃ hExt : Δ.extensionOf Γ, expandEmpty hExt I = J

/-
  Characterization of `expansionOf`: old symbols agree with
  the source instance after arity transport, while new
  symbols are empty.
-/
theorem expansionOf_iff_expandEmpty_tuple
    {Γ Δ : UnnamedSchema A}
    (J : Instance D Δ)
    (I : Instance D Γ) :
    J.expansionOf I ↔
      ∃ hExt : Δ.extensionOf Γ,
        (∀ X : Δ.syms,
          ∀ hX : X.1 ∈ Γ.syms,
            ∀ t : Tuple D (Δ.arity X),
              t ∈ J X ↔
                Tuple.castArity
                    (UnnamedSchema.arity_eq_of_extension_mem
                      hExt X hX) t ∈
                  I ⟨X.1, hX⟩) ∧
        (∀ X : Δ.syms,
          X.1 ∉ Γ.syms → J X = ∅) := by
  constructor
  · rintro ⟨hExt, hExpand⟩
    refine ⟨hExt, ?_, ?_⟩
    · intro X hX t
      have hMem :=
        expandEmpty_mem_iff_of_mem hExt I X hX t
      simpa [hExpand] using hMem
    · intro X hX
      simpa [← hExpand] using
        expandEmpty_eq_empty_of_not_mem hExt I X hX
  · rintro ⟨hExt, hOld, hNew⟩
    refine ⟨hExt, ?_⟩
    apply Instance.ext
    intro X
    by_cases hX : X.1 ∈ Γ.syms
    · apply Finset.ext
      intro t
      exact (expandEmpty_mem_iff_of_mem
        hExt I X hX t).trans
        (hOld X hX t).symm
    · rw [expandEmpty_eq_empty_of_not_mem hExt I X hX,
        hNew X hX]

end Instance

------------------------------------------------------------
-- Instance Update Operations
------------------------------------------------------------

namespace Instance

variable {A D : Type} {_ : RelationNames A} [Domain D]
variable {Γ : UnnamedSchema A}

/- Update one relation name's relation in an instance. -/
def update
    (I : Instance D Γ)
    (X : {sym : A // sym ∈ Γ.syms})
    (R : FinRelation D (Γ.arity X)) :
    Instance D Γ := by
  intro Y
  by_cases h : Y = X
  · exact cast (by cases h; rfl) R
  · exact I Y

/-
  Looking up the updated name returns exactly the new
  relation.
-/
@[simp] theorem update_lookup_eq
    (I : Instance D Γ)
    (X : {sym : A // sym ∈ Γ.syms})
    (R : FinRelation D (Γ.arity X)) :
    (update I X R) X = R := by
  simp [update]

/-
  Looking up a different name after an update is unchanged.
-/
@[simp] theorem update_lookup_ne
    (I : Instance D Γ)
    (X Y : {sym : A // sym ∈ Γ.syms})
    (h : Y ≠ X)
    (R : FinRelation D (Γ.arity X)) :
    (update I X R) Y = I Y := by
  simp [update, h]

/- Updates at distinct relation names commute. -/
theorem update_comm
    {X Y : {sym : A // sym ∈ Γ.syms}}
    (hXY : X ≠ Y)
    (R₁ : FinRelation D (Γ.arity X))
    (R₂ : FinRelation D (Γ.arity Y))
    (I : Instance D Γ) :
    update (update I Y R₂) X R₁ =
    update (update I X R₁) Y R₂ := by
  ext Z
  by_cases hZX : Z = X
  · subst hZX
    simp [update, hXY]
  · by_cases hZY : Z = Y
    · subst hZY
      simp [update, hZX]
    · simp [update, hZX, hZY]

/-
  If we update the same relation name twice,
  the last update wins.
-/
theorem update_shadowing
    (X : {sym : A // sym ∈ Γ.syms})
    (R₁ R₂ : FinRelation D (Γ.arity X))
    (I : Instance D Γ) :
    update (update I X R₂) X R₁ =
    update I X R₁ := by
  ext Y
  by_cases h : Y = X
  · subst h
    simp [update]
  · simp [update, h]

/-
  Updating twice with the same relation is the
  same as one update.
-/
theorem update_idempotent
    (X : {sym : A // sym ∈ Γ.syms})
    (R : FinRelation D (Γ.arity X))
    (I : Instance D Γ) :
    update (update I X R) X R =
    update I X R :=
  update_shadowing X R R I

/-
  Updating a relation name with its current value
  is a no-op.
-/
theorem update_cancel
    (X : {sym : A // sym ∈ Γ.syms})
    (I : Instance D Γ) :
    update I X (I X) = I := by
  ext Y
  by_cases h : Y = X
  · subst h
    simp [update]
  · simp [update, h]

theorem reduct_update_of_not_mem
    {Λ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Λ)
    (J : Instance D Δ)
    (Y : Δ.syms)
    (R : FinRelation D (Δ.arity Y))
    (hY : Y.1 ∉ Λ.syms) :
    Instance.reduct hExt (Instance.update J Y R) =
      Instance.reduct hExt J := by
  apply Instance.ext
  intro X
  unfold Instance.reduct
  have hNe :
      (⟨X.1, hExt.1 X.2⟩ : Δ.syms) ≠ Y := by
    intro hEq
    apply hY
    have hRaw : X.1 = Y.1 := by
      exact congrArg Subtype.val hEq
    simpa [hRaw] using X.2
  simp [Instance.update_lookup_ne, hNe]

theorem reduct_expandEmpty_trans
    {Θ Λ Δ : UnnamedSchema A}
    (hΘΛ : Θ.extensionOf Λ)
    (hΛΔ : Λ.extensionOf Δ)
    (I : Instance D Λ) :
    Instance.reduct
        (UnnamedSchema.extensionOf_trans hΘΛ hΛΔ)
        (Instance.expandEmpty hΘΛ I) =
      Instance.reduct hΛΔ I := by
  apply Instance.ext
  intro X
  have hIn : X.1 ∈ Λ.syms := hΛΔ.1 X.2
  unfold Instance.reduct Instance.expandEmpty
    Instance.relationOfExtension
  simp [hIn]

/-
  Reducing first along `Θ → Λ` and then along
  `Λ → Δ` agrees with reducing once along the
  composed extension.
-/
theorem reduct_trans
    {Θ Λ Δ : UnnamedSchema A}
    (hΘΛ : Θ.extensionOf Λ)
    (hΛΔ : Λ.extensionOf Δ)
    (J : Instance D Θ) :
    Instance.reduct hΛΔ
        (Instance.reduct hΘΛ J) =
      Instance.reduct
        (UnnamedSchema.extensionOf_trans hΘΛ hΛΔ)
        J := by
  apply Instance.ext
  intro X
  unfold Instance.reduct
  let hComp := UnnamedSchema.extensionOf_trans hΘΛ hΛΔ
  let hOuter :=
    UnnamedSchema.arity_eq_of_extensionOf hΛΔ X
  let Y : Λ.syms := UnnamedSchema.symOfExtension hΛΔ X
  let hInner :=
    UnnamedSchema.arity_eq_of_extensionOf hΘΛ Y
  let hDirect :=
    UnnamedSchema.arity_eq_of_extensionOf hComp X
  change
    cast (congrArg (FinRelation D) hOuter)
        (cast (congrArg (FinRelation D) hInner)
          (J (UnnamedSchema.symOfExtension hΘΛ Y))) =
      cast (congrArg (FinRelation D) hDirect)
        (J (UnnamedSchema.symOfExtension hComp X))
  have hSym :
      UnnamedSchema.symOfExtension hΘΛ Y =
        UnnamedSchema.symOfExtension hComp X := by
    exact Subtype.ext rfl
  cases hSym
  calc
    cast (congrArg (FinRelation D) hOuter)
        (cast (congrArg (FinRelation D) hInner)
          (J (UnnamedSchema.symOfExtension hComp X)))
        =
      cast (congrArg (FinRelation D)
          (hInner.trans hOuter))
        (J (UnnamedSchema.symOfExtension hComp X)) := by
          exact FinRelation.cast_trans hInner hOuter
            (J (UnnamedSchema.symOfExtension hComp X))
    _ =
      cast (congrArg (FinRelation D) hDirect)
        (J (UnnamedSchema.symOfExtension hComp X)) := by
          exact FinRelation.cast_proof_irrel
            (hInner.trans hOuter) hDirect
            (J (UnnamedSchema.symOfExtension hComp X))

end Instance
