/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionExtEdgeWindow

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

/-- Shifting the original degree-N single source back to degree zero. -/
def imageSourceShiftIso :
    ((DerivedCategory.singleFunctor C (N : ℤ)).obj P)⟦(N : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor C 0).obj P :=
  ((DerivedCategory.singleFunctors C).shiftIso (N : ℤ) 0 N (add_zero _)).app P

/-- The source comparison is built from the actual exact functor and its shift comparison. -/
def imageMappedSourceShiftIso :
    (L.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C (N : ℤ)).obj P))⟦(N : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor D 0).obj (L.obj P) :=
  (L.mapDerivedCategory.commShiftIso (N : ℤ)).symm.app _ ≪≫
    L.mapDerivedCategory.mapIso (imageSourceShiftIso P N) ≪≫
      (L.mapDerivedCategorySingleFunctor 0).app P

/-- Original Ext classes are the shifted original single-source morphisms. -/
def imageSourceExtAddEquiv :
    ((DerivedCategory.singleFunctor C (N : ℤ)).obj P ⟶
      (DerivedCategory.singleFunctor C 0).obj (R.obj Y)) ≃+ Ext P (R.obj Y) N :=
  (AddEquiv.ofBijective (shiftFunctor (DerivedCategory C) (N : ℤ)).mapAddHom
    ⟨(shiftFunctor (DerivedCategory C) (N : ℤ)).map_injective,
      (shiftFunctor (DerivedCategory C) (N : ℤ)).map_surjective⟩).trans
    ((Iso.homCongrAddEquiv (imageSourceShiftIso P N) (Iso.refl _)).trans
      Ext.homAddEquiv.symm)

/-- The actual adjunction on injective resolutions, in original Ext coordinates. -/
def imageResolutionExtAddEquiv :
    ((DerivedCategory.singleFunctor C (N : ℤ)).obj P ⟶ (I.imageTriangle R).obj₂) ≃+
      Ext (L.obj P) Y N :=
  (adj.imageResolutionHomAddEquiv I ((CochainComplex.singleFunctor C (N : ℤ)).obj P)).trans
    ((Iso.homCongrAddEquiv
      (L.mapDerivedCategoryFactors.symm.app ((CochainComplex.singleFunctor C (N : ℤ)).obj P))
      (asIso (DerivedCategory.Q.map I.extendedι)).symm).trans
      ((AddEquiv.ofBijective (shiftFunctor (DerivedCategory D) (N : ℤ)).mapAddHom
        ⟨(shiftFunctor (DerivedCategory D) (N : ℤ)).map_injective,
          (shiftFunctor (DerivedCategory D) (N : ℤ)).map_surjective⟩).trans
        ((Iso.homCongrAddEquiv (imageMappedSourceShiftIso (L := L) P N) (Iso.refl _)).trans
          Ext.homAddEquiv.symm)))

omit [Abelian D] [HasDerivedCategory D] [HasExt D] [R.Additive] in
/-- The source coordinate change has its literal shifted-map formula. -/
theorem imageSourceExtAddEquiv_hom
    (f : (DerivedCategory.singleFunctor C (N : ℤ)).obj P ⟶
      (DerivedCategory.singleFunctor C 0).obj (R.obj Y)) :
    (imageSourceExtAddEquiv (R := R) P N f).hom =
      (imageSourceShiftIso P N).inv ≫ f⟦(N : ℤ)⟧' := by
  change Ext.homAddEquiv (Ext.homAddEquiv.symm _) = _
  rw [AddEquiv.apply_symm_apply]
  simp [Iso.homCongrAddEquiv]

omit [HasExt C] in
/-- The resolution coordinate change retains the actual adjunction and augmentation. -/
theorem imageResolutionExtAddEquiv_hom
    (f : (DerivedCategory.singleFunctor C (N : ℤ)).obj P ⟶ (I.imageTriangle R).obj₂) :
    (adj.imageResolutionExtAddEquiv I P N f).hom =
      (imageMappedSourceShiftIso (L := L) P N).inv ≫
        (L.mapDerivedCategoryFactors.hom.app
          ((CochainComplex.singleFunctor C (N : ℤ)).obj P) ≫
            adj.imageResolutionHomAddEquiv I _ f ≫
              inv (DerivedCategory.Q.map I.extendedι))⟦(N : ℤ)⟧' := by
  change Ext.homAddEquiv (Ext.homAddEquiv.symm _) = _
  rw [AddEquiv.apply_symm_apply]
  simp [Iso.homCongrAddEquiv, Iso.homCongr]

/-- The actual augmentation becomes the original exact-functor/counit Ext edge. -/
theorem imageResolutionExtAddEquiv_augmentation
    (f : (DerivedCategory.singleFunctor C (N : ℤ)).obj P ⟶ (I.imageTriangle R).obj₁) :
    adj.imageResolutionExtAddEquiv I P N (f ≫ (I.imageTriangle R).mor₁) =
      adj.extEdge N (imageSourceExtAddEquiv (R := R) P N f) := by
  apply Ext.homEquiv.injective
  change (adj.imageResolutionExtAddEquiv I P N
    (f ≫ (I.imageTriangle R).mor₁)).hom =
      (adj.extEdge N (imageSourceExtAddEquiv (R := R) P N f)).hom
  rw [imageResolutionExtAddEquiv_hom, adj.extEdge_hom_formula,
    imageSourceExtAddEquiv_hom]
  change (imageMappedSourceShiftIso (L := L) P N).inv ≫
    (L.mapDerivedCategoryFactors.hom.app _ ≫
      adj.imageResolutionHomAddEquiv I _ (f ≫ DerivedCategory.Q.map (I.imageExtendedι R)) ≫
        inv (DerivedCategory.Q.map I.extendedι))⟦(N : ℤ)⟧' = _
  rw [adj.imageResolutionHomAddEquiv_augmentation, adj.derivedImageEdge_eq]
  dsimp only [imageMappedSourceShiftIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app_assoc, IsIso.hom_inv_id, Functor.map_id, Category.comp_id]
  change _ ≫ _ ≫ (L.mapDerivedCategory.commShiftIso (N : ℤ)).hom.app _ ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  rw [← L.mapDerivedCategory.commShiftIso_hom_naturality_assoc]
  rfl

end CategoryTheory.Adjunction
