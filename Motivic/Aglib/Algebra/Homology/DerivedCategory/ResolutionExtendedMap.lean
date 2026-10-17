/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived

/-! # Naturality of the actual extended injective-resolution augmentation -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
universe v u
namespace CategoryTheory.InjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]
  {Y Z : C} (I : InjectiveResolution Y) (J : InjectiveResolution Z)

/-- A genuine lift of a coefficient morphism remains a lift after extension to integer degrees. -/
@[reassoc]
theorem extendedι_naturality (g : Y ⟶ Z) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0) :
    I.extendedι ≫ extendMap φ ComplexShape.embeddingUpNat =
      (CochainComplex.singleFunctor C 0).map g ≫ J.extendedι := by
  apply from_single_hom_ext
  simp only [extendedι, comp_f, extendSingleIso_inv_f]
  erw [extendMap_f I.ι ComplexShape.embeddingUpNat (i := 0) rfl,
    extendMap_f φ ComplexShape.embeddingUpNat (i := 0) rfl,
    extendMap_f J.ι ComplexShape.embeddingUpNat (i := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hφ]
  simp [CochainComplex.singleFunctor, single_map_f_self, Category.assoc]

end CategoryTheory.InjectiveResolution
