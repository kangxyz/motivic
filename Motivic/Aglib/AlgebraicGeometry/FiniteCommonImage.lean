/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FiniteImageProjection
public import Mathlib.Data.Finset.Insert

/-!
# A finite common closed image over a base

A nonempty finite family of schemes finite over a base has a common actual
closed image in any separated locally finite-type ambient scheme over that
base. Finite binary coproducts provide the source; its scheme-theoretic image
provides the closed scheme. Every original map has a literal factorization
through this common image. No reducedness, integrality or flatness is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable {ι : Type v} {X Z : Scheme.{u}}
  (D : ι → Scheme.{u}) (f : ∀ i, D i ⟶ Z) (p : Z ⟶ X)

set_option backward.isDefEq.respectTransparency false in
/-- A finite binary coproduct supplies a common source, finite over the base,
through which the selected maps all factor. -/
theorem exists_finite_common_source (s : Finset ι) (hs : s.Nonempty)
    (hf : ∀ i ∈ s, IsFinite (f i ≫ p)) :
    ∃ (W : Scheme.{u}) (a : W ⟶ Z), IsFinite (a ≫ p) ∧
      ∀ i ∈ s, ∃ e : D i ⟶ W, e ≫ a = f i := by
  classical
  revert hf
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
    intro hf
    refine ⟨D i, f i, hf i (Finset.mem_singleton_self i), ?_⟩
    intro j hj
    obtain rfl := Finset.mem_singleton.mp hj
    exact ⟨𝟙 _, Category.id_comp _⟩
  | cons i s hi hs ih =>
    intro hf
    obtain ⟨W, a, ha, he⟩ := ih (fun j hj ↦ hf j (Finset.mem_cons_of_mem hj))
    have : IsFinite (f i ≫ p) := hf i (Finset.mem_cons_self i s)
    have : IsFinite (coprod.desc (f i) a ≫ p) := by
      rw [coprod.desc_comp]
      infer_instance
    refine ⟨D i ⨿ W, coprod.desc (f i) a, inferInstance, ?_⟩
    intro j hj
    rcases Finset.mem_cons.mp hj with hji | hj
    · subst j
      exact ⟨coprod.inl, coprod.inl_desc _ _⟩
    · obtain ⟨e, he⟩ := he j hj
      exact ⟨e ≫ coprod.inr, by simpa only [Category.assoc, coprod.inr_desc] using he⟩

set_option backward.isDefEq.respectTransparency false in
/-- The scheme-theoretic image of the finite coproduct is a common closed
support whose projection to the base is genuinely finite. -/
theorem exists_finite_common_closed_image [IsSeparated p] [LocallyOfFiniteType p]
    (s : Finset ι) (hs : s.Nonempty) (hf : ∀ i ∈ s, IsFinite (f i ≫ p)) :
    ∃ (C : Scheme.{u}) (j : C ⟶ Z), IsClosedImmersion j ∧ IsFinite (j ≫ p) ∧
      ∀ i ∈ s, ∃ r : D i ⟶ C, r ≫ j = f i := by
  obtain ⟨W, a, ha, he⟩ := exists_finite_common_source D f p s hs hf
  have : IsFinite a := IsFinite.of_comp a p
  refine ⟨a.image, a.imageι, inferInstance, Motivic.isFinite_image_projection a p, ?_⟩
  intro i hi
  obtain ⟨e, he⟩ := he i hi
  exact ⟨e ≫ a.toImage, by simpa only [Category.assoc, Scheme.Hom.toImage_imageι] using he⟩

end AlgebraicGeometry
