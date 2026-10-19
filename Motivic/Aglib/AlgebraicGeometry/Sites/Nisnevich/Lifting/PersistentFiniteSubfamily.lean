/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteSubfamily

/-! # Finite residue-splitting families near persistent generizations -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u v
namespace AlgebraicGeometry.Nisnevich

private theorem exists_generic_specializes_of_mem_closure_range
    {Y X : Scheme.{u}} [IsNoetherian Y] (f : Y ⟶ X) (x : X)
    (hx : x ∈ closure (Set.range f)) :
    ∃ η : genericPoints Y, f η ⤳ x := by
  have hfin := genericPoints.finite
    (NoetherianSpace.finite_irreducibleComponents (α := Y))
  have hd : closure (f '' genericPoints Y) = closure (Set.range f) := by
    rw [← closure_image_closure f.continuous, genericPoints.closure, Set.image_univ]
  have he : f '' genericPoints Y = ⋃ η ∈ genericPoints Y, {f η} := by
    ext y
    simp [eq_comm]
  rw [← hd, he, hfin.closure_biUnion] at hx
  obtain ⟨η, hη, hx⟩ := Set.mem_iUnion₂.mp hx
  exact ⟨⟨η, hη⟩, specializes_iff_mem_closure.mpr hx⟩

private theorem lift_field_of_persistent_residue_lifting
    {U X : Scheme.{u}} (g : U ⟶ X) (x : X)
    {ι : Type v} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ U)
    (hf : ∀ z : U, g z ⤳ x → ∃ (i : ι) (y : Y i),
      f i y = z ∧ IsIso ((f i).residueFieldMap y))
    (K : Type u) [Field K] (a : Spec (.of K) ⟶ U)
    (ha : g (a (IsLocalRing.closedPoint K)) ⤳ x) :
    ∃ (i : ι) (b : Spec (.of K) ⟶ Y i), b ≫ f i = a := by
  obtain ⟨⟨z, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField K U).symm.surjective a
  have hz : g z ⤳ x := by
    change g (U.fromSpecResidueField z (Spec.map a _)) ⤳ x at ha
    simpa only [Scheme.fromSpecResidueField_apply] using ha
  obtain ⟨i, y, rfl, hi⟩ := hf z hz
  let := hi
  refine ⟨i, Spec.map (inv ((f i).residueFieldMap y) ≫ a) ≫
    (Y i).fromSpecResidueField y, ?_⟩
  rw [Category.assoc, ← (f i).SpecMap_residueFieldMap_fromSpecResidueField y,
    ← Spec.map_comp_assoc]
  simp [Scheme.SpecToEquivOfField]

/-- Residue-splitting over the points persistent near `x` spreads to a finite
residue-splitting family over an actual open neighborhood of `x`.
This is ordinary-open covering reflection, not pro-Nis cohomological descent. -/
theorem exists_open_finset_persistent_residueFieldLifting
    {U X : Scheme.{u}} [IsNoetherian U] (g : U ⟶ X) (x : X)
    {ι : Type v} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ U)
    [∀ i, LocallyOfFiniteType (f i)]
    (hf : ∀ z : U, g z ⤳ x → ∃ (i : ι) (y : Y i),
      f i y = z ∧ IsIso ((f i).residueFieldMap y)) :
    ∃ (W : X.Opens), x ∈ W ∧ ∃ s : Finset ι,
      ∀ z : U, g z ∈ W → ∃ i ∈ s, ∃ y : Y i,
        f i y = z ∧ IsIso ((f i).residueFieldMap y) := by
  classical
  suffices ∀ Z : Closeds U, ∃ (W : X.Opens), x ∈ W ∧ ∃ s : Finset ι,
      ∀ z ∈ Z, g z ∈ W → ∃ i ∈ s, ∃ y : Y i,
        f i y = z ∧ IsIso ((f i).residueFieldMap y) by
    obtain ⟨W, hx, s, hs⟩ := this ⊤
    exact ⟨W, hx, s, fun z hz ↦ hs z (by trivial) hz⟩
  intro Z
  apply (wellFounded_lt (α := Closeds U)).induction Z
  intro Z ih
  let I := (Scheme.IdealSheafData.vanishingIdeal Z).radical
  let T := I.subscheme
  let j : T ⟶ U := I.subschemeι
  have hj : Set.range j = (Z : Set U) := I.range_subschemeι
  have : IsNoetherian T := Scheme.isNoetherian_of_finiteType j
  have : IsReduced T := Scheme.IdealSheafData.isReduced_radical_subscheme _
  by_cases hx : x ∈ closure (Set.range (j ≫ g))
  · obtain ⟨η, hη⟩ := exists_generic_specializes_of_mem_closure_range (j ≫ g) x hx
    let : Field (T.presheaf.stalk η) :=
      (isField_stalk_of_closure_mem_irreducibleComponents T η η.property).toField
    obtain ⟨i, a, ha⟩ := lift_field_of_persistent_residue_lifting g x f hf
      (T.presheaf.stalk η) (T.fromSpecStalk η ≫ j) (by
        change g (j (T.fromSpecStalk η _)) ⤳ x
        rw [Scheme.fromSpecStalk_closedPoint]
        exact hη)
    obtain ⟨V, hηV, t, _, ht⟩ := spread_out_of_isGermInjective' j (f i) a ha
    let C : Closeds U := ⟨j '' (V : Set T)ᶜ,
      j.isClosedEmbedding.isClosedMap _ V.isOpen.isClosed_compl⟩
    have hCZ : C < Z := by
      refine lt_of_le_of_ne ?_ ?_
      · rintro z ⟨r, _, rfl⟩
        exact hj.subset ⟨r, rfl⟩
      · intro he
        have hm : j η ∈ C := by
          rw [he]
          exact hj.subset ⟨η, rfl⟩
        obtain ⟨r, hr, heq⟩ := hm
        exact hr ((j.isClosedEmbedding.injective heq).symm ▸ hηV)
    obtain ⟨W, hxW, s, hs⟩ := ih C hCZ
    refine ⟨W, hxW, insert i s, fun z hz hzW ↦ ?_⟩
    obtain ⟨r, rfl⟩ := hj.symm.subset hz
    by_cases hr : r ∈ V
    · let w : V.toScheme := ⟨r, hr⟩
      have hcomp : IsIso ((V.ι ≫ j).residueFieldMap w) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr
          ⟨((V.ι ≫ j).residueFieldMap w).hom.injective,
            Scheme.Hom.residueFieldMap_surjective _ w⟩
      have hcomp' : IsIso ((t ≫ f i).residueFieldMap w) := by rw [ht]; exact hcomp
      have hi : IsIso ((f i).residueFieldMap (t w)) := by
        apply (ConcreteCategory.isIso_iff_bijective _).mpr
        refine ⟨((f i).residueFieldMap (t w)).hom.injective, ?_⟩
        have h := ((ConcreteCategory.isIso_iff_bijective _).mp hcomp').surjective
        rw [Scheme.residueFieldMap_comp] at h
        change Function.Surjective ((t.residueFieldMap w) ∘
          ((f i).residueFieldMap (t w))) at h
        exact h.of_comp_left (t.residueFieldMap w).hom.injective
      exact ⟨i, Finset.mem_insert_self _ _, t w,
        congrArg (fun q : V.toScheme ⟶ U ↦ q w) ht, hi⟩
    · obtain ⟨k, hk, y, hy, hi⟩ := hs (j r) ⟨r, hr, rfl⟩ hzW
      exact ⟨k, Finset.mem_insert_of_mem hk, y, hy, hi⟩
  · refine ⟨⟨(closure (Set.range (j ≫ g)))ᶜ, isClosed_closure.isOpen_compl⟩,
      hx, ∅, fun z hz hzW ↦ ?_⟩
    obtain ⟨r, rfl⟩ := hj.symm.subset hz
    exact False.elim (hzW (subset_closure ⟨r, rfl⟩))

end AlgebraicGeometry.Nisnevich
