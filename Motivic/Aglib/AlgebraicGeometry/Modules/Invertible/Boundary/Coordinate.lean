/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.Frame
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PairNormalization

/-! # The unchanged original coordinate in the restricted boundary frame -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Pullback.OpenRestriction

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The unit source of a restricted section is transported by the native unit square. -/
private theorem localPullbackIso_inv_unit_source {Z C : Scheme.{u}}
    (z : Z ⟶ C) (U : C.Opens) :
    (pullbackUnitIso (z ∣_ U)).inv ≫
      (Modules.pullback (z ∣_ U)).map (restrictUnitIso U.ι).inv ≫
      (localPullbackIso z U).inv.app (SheafOfModules.unit C.ringCatSheaf) =
    (restrictUnitIso (z ⁻¹ᵁ U).ι).inv ≫
      (restrictFunctor (z ⁻¹ᵁ U).ι).map (pullbackUnitIso z).inv := by
  apply (cancel_mono ((restrictFunctor (z ⁻¹ᵁ U).ι).map (pullbackUnitIso z).hom ≫
    (restrictUnitIso (z ⁻¹ᵁ U).ι).hom)).mp
  simp only [Category.assoc]
  rw [localPullbackIso_inv_unit]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

/-- An actual section expressed in the restricted frame has its original coefficient. -/
theorem pullbackSectionMap_openBoundaryFrame {Z C : Scheme.{u}}
    (z : Z ⟶ C) (U : C.Opens) (M : C.Modules) {N : U.toScheme.Modules}
    (q : (restrictFunctor U.ι).obj M ≅ N)
    (E : (Modules.pullback z).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)
    (δ : SheafOfModules.unit C.ringCatSheaf ⟶ M) :
    pullbackSectionMap (z ∣_ U)
      ((restrictUnitIso U.ι).inv ≫ (restrictFunctor U.ι).map δ ≫ q.hom) ≫
        (openBoundaryFrame z U M q E).hom =
    (restrictUnitIso (z ⁻¹ᵁ U).ι).inv ≫
      (restrictFunctor (z ⁻¹ᵁ U).ι).map (pullbackSectionMap z δ ≫ E.hom) ≫
      (restrictUnitIso (z ⁻¹ᵁ U).ι).hom := by
  simp only [pullbackSectionMap, openBoundaryFrame, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_inv, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← (Modules.pullback (z ∣_ U)).map_comp_assoc q.hom q.inv,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (localPullbackIso z U).inv.naturality δ
  dsimp only [CategoryTheory.Functor.comp_map] at hn
  erw [reassoc_of% hn, reassoc_of% (localPullbackIso_inv_unit_source z U)]

/-- Restricting the original canonical dual section does not change its boundary coordinate. -/
theorem pullbackSectionMap_openDualBoundaryFrame {Z C : Scheme.{u}}
    (z : Z ⟶ C) (U : C.Opens) (I : LineBundle C)
    (φ : I.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (E : (Modules.pullback z).obj (dualLineBundle C I).val ≅
      SheafOfModules.unit Z.ringCatSheaf) :
    pullbackSectionMap (z ∣_ U)
      (canonicalDualHom U.toScheme (restrictLineBundle U.ι I).val
        ((restrictFunctor U.ι).map φ ≫ (restrictUnitIso U.ι).hom)) ≫
      (openDualBoundaryFrame z U I E).hom =
    (restrictUnitIso (z ⁻¹ᵁ U).ι).inv ≫
      (restrictFunctor (z ⁻¹ᵁ U).ι).map
        (pullbackSectionMap z (canonicalDualHom C I.val φ) ≫ E.hom) ≫
      (restrictUnitIso (z ⁻¹ᵁ U).ι).hom := by
  rw [← restrictDualIso_canonicalDualHom]
  exact pullbackSectionMap_openBoundaryFrame z U (dualLineBundle C I).val
    (restrictDualIso U.ι I) E (canonicalDualHom C I.val φ)

end AlgebraicGeometry.Scheme.Modules.Invertible
