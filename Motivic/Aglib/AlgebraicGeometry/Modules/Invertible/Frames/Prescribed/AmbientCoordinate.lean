/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.FunctionalCoordinate

/-! # The exact original ambient coordinate in a prescribed affine extension

The affine-chart and boundary comparison maps cancel canonically. The given
original full-boundary frame and its component values are therefore preserved
by the same extension, without imposing a new scalar normalization.


Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.AmbientCoordinate`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.PrescribedGraphCoordinate`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {P B : Scheme.{u}} (A : P.affineOpens) (b : B ⟶ A.val.toScheme)
  (β : B ⟶ P) (hc : b ≫ A.val.ι = β) (L : LineBundle P)
  (e : (Modules.pullback β).obj L.val ≅ SheafOfModules.unit B.ringCatSheaf)
  (E : PrescribedAffineFrameExtension A b L
    ((Modules.pullbackComp b A.val.ι).app L.val ≪≫
      (Modules.pullbackCongr hc).app L.val ≪≫ e))

/-- The original functional retains the exact original whole-boundary coordinate. -/
theorem prescribedExtension_original_coordinate
    (φ : L.val ⟶ SheafOfModules.unit P.ringCatSheaf) :
    Scheme.Hom.unitEndomorphismPullback E.boundaryLift
      (E.frame.inv ≫ pullbackUnitMap E.inclusion (pullbackUnitMap A.val.ι φ)) =
        e.inv ≫ pullbackUnitMap β φ := by
  rw [E.boundary_functional_coordinate]
  simp only [Iso.trans_inv, Category.assoc]
  rw [← pullbackUnitMap_comp, Iso.inv_hom_id_assoc]
  rw [← pullbackUnitMap_congr hc, Iso.inv_hom_id_assoc]

/-- An actual marked or infinity component keeps its original coordinate after
extension through the same affine neighborhood. -/
theorem prescribedExtension_component_coordinate {Z : Scheme.{u}} (r : Z ⟶ B)
    (φ : L.val ⟶ SheafOfModules.unit P.ringCatSheaf) :
    Scheme.Hom.unitEndomorphismPullback (r ≫ E.boundaryLift)
      (E.frame.inv ≫ pullbackUnitMap E.inclusion (pullbackUnitMap A.val.ι φ)) =
    Scheme.Hom.unitEndomorphismPullback r (e.inv ≫ pullbackUnitMap β φ) := by
  rw [← Scheme.Hom.unitEndomorphismPullback_comp,
    prescribedExtension_original_coordinate A b β hc L e E]

end AlgebraicGeometry.Scheme.Modules.Invertible
