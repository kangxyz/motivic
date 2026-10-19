/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.OpenRangeFrame
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.IdealFrameBoundaryScalar

/-! # Exact functional coordinates in the same prescribed frame extension

This is the ideal-functional side of the boundary comparison. It does not
replace that functional by a coordinate of a dual line without an identification.


Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.FunctionalCoordinate`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.AmbientCoordinate`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible.PrescribedAffineFrameExtension

variable {P B : Scheme.{u}} {A : P.affineOpens} {b : B ⟶ A.val.toScheme}
  {L : LineBundle P}
  {e : (Modules.pullback b).obj (pullbackLineBundle A.val.ι L).val ≅
    SheafOfModules.unit B.ringCatSheaf}
  (E : PrescribedAffineFrameExtension A b L e)

/-- The exact prescribed-frame equation preserves the original functional,
including every nonreduced component of the boundary. -/
theorem boundary_functional_coordinate
    (φ : (pullbackLineBundle A.val.ι L).val ⟶
      SheafOfModules.unit A.val.toScheme.ringCatSheaf) :
    Scheme.Hom.unitEndomorphismPullback E.boundaryLift
      (E.frame.inv ≫ pullbackUnitMap E.inclusion φ) =
        e.inv ≫ pullbackUnitMap b φ := by
  have he := congrArg Iso.inv E.frame_eq
  rw [← he]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
  rw [pullbackUnitMap_congr, pullbackUnitMap_comp]
  simp only [Scheme.Hom.unitEndomorphismPullback, pullbackUnitMap,
    Functor.map_comp, Category.assoc]

/-- Evaluating the same functional at one gives its exact full-boundary scalar
under the original structural ring map. -/
theorem boundary_functional_scalar
    (φ : (pullbackLineBundle A.val.ι L).val ⟶
      SheafOfModules.unit A.val.toScheme.ringCatSheaf) :
    E.boundaryLift.appTop
      (Modules.Hom.app (E.frame.inv ≫ pullbackUnitMap E.inclusion φ) ⊤
        (1 : Γ(E.neighborhood, ⊤))) =
      Modules.Hom.app (e.inv ≫ pullbackUnitMap b φ) ⊤ (1 : Γ(B, ⊤)) := by
  rw [← Scheme.Hom.unitEndomorphismPullback_app_one, E.boundary_functional_coordinate]

end AlgebraicGeometry.Scheme.Modules.Invertible.PrescribedAffineFrameExtension
