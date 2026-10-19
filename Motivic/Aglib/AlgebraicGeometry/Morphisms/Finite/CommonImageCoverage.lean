/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.CommonImage

/-! # Pointwise coverage of the actual finite common scheme-theoretic image -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace AlgebraicGeometry
variable {ι : Type v} {X Z : Scheme.{u}}
  (D : ι → Scheme.{u}) (f : ∀ i, D i ⟶ Z) (p : Z ⟶ X)

/-- The actual common finite source retains coverage by the original maps. -/
theorem exists_finite_common_source_with_coverage (s : Finset ι) (hs : s.Nonempty)
    (hf : ∀ i ∈ s, IsFinite (f i ≫ p)) :
    ∃ (W : Scheme.{u}) (a : W ⟶ Z), IsFinite (a ≫ p) ∧
      (∀ i ∈ s, ∃ e : D i ⟶ W, e ≫ a = f i) ∧
      ∀ w : W, ∃ i ∈ s, ∃ d : D i, a w = f i d := by
  classical
  revert hf
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
    intro hf
    refine ⟨D i, f i, hf i (Finset.mem_singleton_self i), ?_, ?_⟩
    · intro j hj
      obtain rfl := Finset.mem_singleton.mp hj
      exact ⟨𝟙 _, Category.id_comp _⟩
    · intro w
      exact ⟨i, Finset.mem_singleton_self i, w, rfl⟩
  | cons i s hi hs ih =>
    intro hf
    obtain ⟨W, a, ha, he, hcover⟩ := ih (fun j hj => hf j (Finset.mem_cons_of_mem hj))
    have : IsFinite (f i ≫ p) := hf i (Finset.mem_cons_self i s)
    have : IsFinite (coprod.desc (f i) a ≫ p) := by
      rw [coprod.desc_comp]
      infer_instance
    refine ⟨D i ⨿ W, coprod.desc (f i) a, inferInstance, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_cons.mp hj with hji | hj
      · subst j
        exact ⟨coprod.inl, coprod.inl_desc _ _⟩
      · obtain ⟨e, he⟩ := he j hj
        exact ⟨e ≫ coprod.inr, by simpa only [Category.assoc, coprod.inr_desc] using he⟩
    · intro w
      have hw : w ∈ Set.range (coprod.inl : D i ⟶ D i ⨿ W) ∪
          Set.range (coprod.inr : W ⟶ D i ⨿ W) :=
        (isCompl_range_inl_inr (D i) W).sup_eq_top.ge (Set.mem_univ w)
      rcases hw with ⟨d, rfl⟩ | ⟨z, rfl⟩
      · refine ⟨i, Finset.mem_cons_self i s, d, ?_⟩
        exact congrArg (fun g : D i ⟶ Z => g d) (coprod.inl_desc (f i) a)
      · obtain ⟨j, hj, d, hd⟩ := hcover z
        refine ⟨j, Finset.mem_cons_of_mem hj, d, ?_⟩
        exact (congrArg (fun g : W ⟶ Z => g z) (coprod.inr_desc (f i) a)).trans hd

/-- Every point of the common closed image comes from an original support,
with the actual image inclusion and original map agreeing at that point. -/
theorem exists_finite_common_closed_image_with_coverage [IsSeparated p]
    [LocallyOfFiniteType p] (s : Finset ι) (hs : s.Nonempty)
    (hf : ∀ i ∈ s, IsFinite (f i ≫ p)) :
    ∃ (C : Scheme.{u}) (j : C ⟶ Z), IsClosedImmersion j ∧ IsFinite (j ≫ p) ∧
      (∀ i ∈ s, ∃ r : D i ⟶ C, r ≫ j = f i) ∧
      ∀ z : C, ∃ i ∈ s, ∃ d : D i, j z = f i d := by
  obtain ⟨W, a, ha, he, hcover⟩ :=
    exists_finite_common_source_with_coverage D f p s hs hf
  have : IsFinite a := IsFinite.of_comp a p
  refine ⟨a.image, a.imageι, inferInstance, Scheme.Hom.isFinite_image_projection a p, ?_, ?_⟩
  · intro i hi
    obtain ⟨e, he⟩ := he i hi
    exact ⟨e ≫ a.toImage, by simpa only [Category.assoc, Scheme.Hom.toImage_imageι] using he⟩
  · intro z
    obtain ⟨w, rfl⟩ := a.toImage.surjective z
    obtain ⟨i, hi, d, hd⟩ := hcover w
    refine ⟨i, hi, d, ?_⟩
    exact (congrArg (fun g : W ⟶ Z => g w) a.toImage_imageι).trans hd

end AlgebraicGeometry
