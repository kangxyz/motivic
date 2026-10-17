/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerivedFunctoriality
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ResolutionExtendedMap

/-! # Coefficient naturality for the original Ext and right-derived comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex CochainComplex.HomComplex
universe w v u
namespace CategoryTheory.InjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  [HasExt.{w} C] {Y Z : C} (I : InjectiveResolution Y) (J : InjectiveResolution Z)
  (g : Y ⟶ Z) (φ : I.cocomplex ⟶ J.cocomplex)
  (hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0) (X : C) (n : ℕ)
attribute [local instance] HasDerivedCategory.standard
include hφ

/-- Actual coefficient maps commute with the inverse comparison. -/
theorem extRightDerivedAddEquiv_symm_naturality_right
    (y : ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y) :
    ((I.extRightDerivedAddEquiv X n).symm y).comp (Abelian.Ext.mk₀ g) (add_zero n) =
      (J.extRightDerivedAddEquiv X n).symm
        (((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).map g y) := by
  have hi : ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).map g ≫
        (J.homComplexHomologyRightDerivedIso X n).inv =
      (I.homComplexHomologyRightDerivedIso X n).inv ≫
        homologyMap (map (𝟙 _) (extendMap φ ComplexShape.embeddingUpNat)) (n : ℤ) := by
    apply (cancel_epi (I.homComplexHomologyRightDerivedIso X n).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← I.homComplexHomologyRightDerivedIso_naturality_right n g J φ hφ X,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hy := ConcreteCategory.congr_hom hi y
  change (J.homComplexHomologyRightDerivedIso X n).inv
      (((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).map g y) =
    homologyMap (map (𝟙 _) (extendMap φ ComplexShape.embeddingUpNat)) (n : ℤ)
      ((I.homComplexHomologyRightDerivedIso X n).inv y) at hy
  have hs : inv (DerivedCategory.Q.map I.extendedι) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map g) =
    DerivedCategory.Q.map (extendMap φ ComplexShape.embeddingUpNat) ≫
      inv (DerivedCategory.Q.map J.extendedι) := by
    apply (cancel_epi (DerivedCategory.Q.map I.extendedι)).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [← Functor.map_comp, I.extendedι_naturality J g φ hφ,
      Functor.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  apply Abelian.Ext.ext
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀,
    I.extRightDerivedAddEquiv_symm_hom, J.extRightDerivedAddEquiv_symm_hom,
    hy, homologyAddEquiv_naturality, CohomologyClass.derivedHomAddEquiv_naturality]
  change (_ ≫ (shiftFunctor _ (n : ℤ)).map (inv (DerivedCategory.Q.map I.extendedι))) ≫
    (shiftFunctor _ (n : ℤ)).map (DerivedCategory.Q.map
      ((CochainComplex.singleFunctor C 0).map g)) = _
  simp only [Functor.map_id, Category.id_comp, Category.assoc]
  rw [← Functor.map_comp, hs, Functor.map_comp]

/-- Forward coefficient naturality for the original Ext comparison. -/
theorem extRightDerivedAddEquiv_naturality_right (x : Abelian.Ext.{w} X Y n) :
    J.extRightDerivedAddEquiv X n (x.comp (Abelian.Ext.mk₀ g) (add_zero n)) =
      ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).map g
        (I.extRightDerivedAddEquiv X n x) := by
  obtain ⟨y, rfl⟩ := (I.extRightDerivedAddEquiv X n).symm.surjective x
  rw [I.extRightDerivedAddEquiv_symm_naturality_right J g φ hφ X n]
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

end CategoryTheory.InjectiveResolution
