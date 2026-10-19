/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ImageResolution

/-! # The actual augmentation under the extension-by-zero comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v₁ v₂ u₁ u₂
namespace CategoryTheory.InjectiveResolution
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] {Y : C} (I : InjectiveResolution Y)
  (R : C ⥤ D) [R.Additive]

/-- The cone augmentation agrees with the image of the original resolution augmentation. -/
@[reassoc]
theorem imageExtendedι_mapExtendIso :
    I.imageExtendedι R ≫ (I.cocomplex.mapExtendIso R ComplexShape.embeddingUpNat).inv =
      (singleMapHomologicalComplex R (.up ℤ) 0).inv.app Y ≫
        (R.mapHomologicalComplex (.up ℤ)).map I.extendedι := by
  apply from_single_hom_ext
  simp only [imageExtendedι, extendedι, comp_f, extendSingleIso_inv_f,
    Functor.mapHomologicalComplex_map_f, singleMapHomologicalComplex_inv_app_self,
    Functor.map_comp]
  erw [extendMap_f (I.imageι R) ComplexShape.embeddingUpNat (i := 0) rfl,
    extendMap_f I.ι ComplexShape.embeddingUpNat (i := 0) rfl]
  have hh (a : Option ℕ) (h : a = some 0) :
      (extend.XIso ((R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) h).inv ≫
        (extend.mapXIso I.cocomplex R a).inv = R.map (extend.XIso I.cocomplex h).inv := by
    subst a
    simp [extend.XIso, extend.mapXIso, extend.X, Functor.mapHomologicalComplex]
  simp only [mapExtendIso, mapExtendXIso, imageι_f_zero, imageComplex,
    singleObjXSelf, singleObjXIsoOfEq, extendXIso,
    Functor.mapHomologicalComplex_obj_X, CochainComplex.single₀_obj_zero,
    Iso.refl_inv, Category.id_comp, ComplexShape.embeddingUpNat_f, Int.cast_ofNat_Int,
    Category.assoc, Iso.inv_hom_id_assoc, Functor.comp_obj, Functor.map_id, Functor.map_comp,
    Iso.map_inv_hom_id_assoc, Iso.cancel_iso_hom_left, Hom.isoOfComponents_inv_f, eqToIso_refl]
  erw [hh]
  erw [Functor.map_id, Category.id_comp]
  erw [Category.id_comp]

end CategoryTheory.InjectiveResolution
