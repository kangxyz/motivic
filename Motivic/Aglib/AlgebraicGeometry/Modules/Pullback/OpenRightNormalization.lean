/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestrictionUnit
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PairNormalization
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Restriction

/-! # Normalization of the actual restricted unit coefficient -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Pullback.OpenRestriction

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Normalize the unit coefficient after restriction using the canonical maps. -/
def openRightNormalization {C : Scheme.{u}} (U : C.Opens) (T : C.Modules) :
    (restrictFunctor U.ι).obj (tensorSheaf C T (SheafOfModules.unit C.ringCatSheaf)) ⟶
      (restrictFunctor U.ι).obj T :=
  (tensorRestrictionIso U.ι T (SheafOfModules.unit C.ringCatSheaf)).inv ≫
    (tensorSheafIso U.toScheme (Iso.refl _) (restrictUnitIso U.ι)).hom ≫
    (tensorSheafRightUnit U.toScheme ((restrictFunctor U.ι).obj T)).hom

/-- Literal coefficient compatibility of normalization with local pullback. -/
@[reassoc] theorem openRightNormalization_pullback {Z C : Scheme.{u}}
    (z : Z ⟶ C) (U : C.Opens) (T : C.Modules) :
    (Scheme.Modules.pullback (z ∣_ U)).map (openRightNormalization U T) ≫
      (localPullbackIso z U).inv.app T =
    (localPullbackIso z U).inv.app (tensorSheaf C T (SheafOfModules.unit C.ringCatSheaf)) ≫
      (restrictFunctor (z ⁻¹ᵁ U).ι).map
        (pullbackTensorMap z T (SheafOfModules.unit C.ringCatSheaf)) ≫
      (tensorRestrictionIso (z ⁻¹ᵁ U).ι ((Scheme.Modules.pullback z).obj T)
        ((Scheme.Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf))).inv ≫
      tensorSheafMap (z ⁻¹ᵁ U).toScheme (𝟙 _)
        ((restrictFunctor (z ⁻¹ᵁ U).ι).map (pullbackUnitIso z).hom ≫
          (restrictUnitIso (z ⁻¹ᵁ U).ι).hom) ≫
      (tensorSheafRightUnit (z ⁻¹ᵁ U).toScheme
        ((restrictFunctor (z ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback z).obj T))).hom := by
  apply (cancel_epi ((Scheme.Modules.pullback (z ∣_ U)).map
    (tensorRestrictionIso U.ι T (SheafOfModules.unit C.ringCatSheaf)).hom)).mp
  simp only [openRightNormalization, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [show (tensorRestrictionIso U.ι T (SheafOfModules.unit C.ringCatSheaf)).hom =
    restrictTensorMap C U T (SheafOfModules.unit C.ringCatSheaf) from rfl,
    pullbackTensorMap_restrict_assoc]
  simp only [restrictTensorMap, Iso.hom_inv_id_assoc]
  rw [tensorSheafMap_comp_assoc]
  simp only [Category.comp_id]
  rw [localPullbackIso_inv_unit]
  rw [← pullbackTensorMap_rightUnit]
  change (Scheme.Modules.pullback (z ∣_ U)).map
      (tensorSheafMap U.toScheme (𝟙 _) (restrictUnitIso U.ι).hom) ≫ _ = _
  simp only [Category.assoc]
  rw [pullbackTensorMap_naturality_assoc]
  simp only [CategoryTheory.Functor.map_id]
  have hn := (SheafOfModulesOfCommRing.tensorRightUnitIso (z ⁻¹ᵁ U).toScheme.sheaf).hom.naturality
    ((localPullbackIso z U).inv.app T)
  change tensorSheafMap (z ⁻¹ᵁ U).toScheme ((localPullbackIso z U).inv.app T) (𝟙 _) ≫
      (tensorSheafRightUnit _ _).hom =
    (tensorSheafRightUnit _ _).hom ≫ (localPullbackIso z U).inv.app T at hn
  erw [← hn]
  rw [tensorSheafMap_comp_assoc, tensorSheafMap_comp_assoc]
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- The restricted normalized section retains its literal pulled coefficient. -/
theorem pullbackSectionMap_openRightNormalization {Z C : Scheme.{u}}
    (z : Z ⟶ C) (U : C.Opens) (T : C.Modules)
    (b : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (restrictFunctor U.ι).obj (tensorSheaf C T (SheafOfModules.unit C.ringCatSheaf))) :
    Invertible.pullbackSectionMap (z ∣_ U) (b ≫ openRightNormalization U T) ≫
      (localPullbackIso z U).inv.app T =
    Invertible.pullbackSectionMap (z ∣_ U) b ≫
      (localPullbackIso z U).inv.app (tensorSheaf C T (SheafOfModules.unit C.ringCatSheaf)) ≫
      (restrictFunctor (z ⁻¹ᵁ U).ι).map
        (pullbackTensorMap z T (SheafOfModules.unit C.ringCatSheaf)) ≫
      (tensorRestrictionIso (z ⁻¹ᵁ U).ι ((Scheme.Modules.pullback z).obj T)
        ((Scheme.Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf))).inv ≫
      tensorSheafMap (z ⁻¹ᵁ U).toScheme (𝟙 _)
        ((restrictFunctor (z ⁻¹ᵁ U).ι).map (pullbackUnitIso z).hom ≫
          (restrictUnitIso (z ⁻¹ᵁ U).ι).hom) ≫
      (tensorSheafRightUnit (z ⁻¹ᵁ U).toScheme
        ((restrictFunctor (z ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback z).obj T))).hom := by
  simp only [Invertible.pullbackSectionMap, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [openRightNormalization_pullback]

end AlgebraicGeometry.Scheme.Modules
