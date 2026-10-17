/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ImageResolutionExtCoordinates

/-! # Original Ext coordinates for actual image-resolution maps -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe w₁ w₂ w₃ w₄ v₁ v₂ u₁ u₂
namespace CategoryTheory.Adjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  [HasExt.{w₃} C] [HasExt.{w₄} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
  {Y : D} (I : InjectiveResolution Y) (P : C) (N : ℕ)

omit [HasExt C] [HasExt D] [R.Additive] in
/-- The actual mapped single-source shift comparison is natural in its source. -/
theorem imageMappedSourceShiftIso_inv_naturality {P' : C} (a : P' ⟶ P) :
    (DerivedCategory.singleFunctor D 0).map (L.map a) ≫
        (imageMappedSourceShiftIso (L := L) P N).inv =
      (imageMappedSourceShiftIso (L := L) P' N).inv ≫
        (L.mapDerivedCategory.map ((DerivedCategory.singleFunctor C (N : ℤ)).map a))⟦(N : ℤ)⟧' := by
  dsimp only [imageMappedSourceShiftIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app]
  simp only [Category.assoc]
  have h0 := (L.mapDerivedCategorySingleFunctor 0).inv.naturality a
  dsimp only [Functor.comp_map] at h0
  rw [reassoc_of% h0]
  rw [← Functor.map_comp_assoc]
  have h := ((DerivedCategory.singleFunctors C).shiftIso
    (N : ℤ) 0 N (add_zero _)).inv.naturality a
  dsimp only [Functor.comp_map] at h
  change _ ≫ L.mapDerivedCategory.map
    ((DerivedCategory.singleFunctor C 0).map a ≫
      ((DerivedCategory.singleFunctors C).shiftIso (N : ℤ) 0 N (add_zero _)).inv.app P) ≫ _ = _
  rw [h]
  simp only [Functor.map_comp, Category.assoc]
  rw [L.mapDerivedCategory.commShiftIso_hom_naturality]
  rfl

omit [HasExt C] in
/-- Original Ext coordinates respect genuine contravariant source maps. -/
theorem imageResolutionExtAddEquiv_naturality {P' : C} (a : P' ⟶ P)
    (f : (DerivedCategory.singleFunctor C (N : ℤ)).obj P ⟶ (I.imageTriangle R).obj₂) :
    adj.imageResolutionExtAddEquiv I P' N
        ((DerivedCategory.singleFunctor C (N : ℤ)).map a ≫ f) =
      (Ext.mk₀ (L.map a)).comp (adj.imageResolutionExtAddEquiv I P N f) (zero_add N) := by
  apply Ext.homEquiv.injective
  change (adj.imageResolutionExtAddEquiv I P' N
    ((DerivedCategory.singleFunctor C (N : ℤ)).map a ≫ f)).hom =
      ((Ext.mk₀ (L.map a)).comp (adj.imageResolutionExtAddEquiv I P N f) (zero_add N)).hom
  rw [imageResolutionExtAddEquiv_hom, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, imageResolutionExtAddEquiv_hom]
  rw [adj.imageResolutionHomAddEquiv_eq, adj.imageResolutionHomAddEquiv_eq]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [reassoc_of% (imageMappedSourceShiftIso_inv_naturality (L := L) P N a)]

end CategoryTheory.Adjunction
