/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.OpenGraphTriangle
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.IdealFrameBoundaryScalar

/-! # The original ideal functional in the same transported chart frame

The canonical Cartesian ideal map retains the ideal inclusion, so the scalar
used by the Fitting norm comparison is the original prescribed functional's
coordinate, not an independently normalized generator.


Intended upstream module:
`Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FlatChartIdealCoordinate`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.ParameterGraphPullback`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairNormIdeal`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {D D' X Y : Scheme.{u}}
  (i : D ⟶ X) (i' : D' ⟶ Y) (v : Y ⟶ X) (a : D' ⟶ D)
  (H : IsPullback a i' i v) [IsClosedImmersion i] [IsClosedImmersion i'] [Flat v]
  (hI : IsLocallyRankOne X (idealModule i))
  (e : (Modules.pullback v).obj (idealModule i) ≅ SheafOfModules.unit Y.ringCatSheaf)

/-- The same transported frame preserves the literal original ideal functional. -/
theorem flatChartIdealFrame_coordinate :
    ((flatChartIdealIso i i' v a H hI).symm ≪≫ e).inv ≫ idealInclusion i' =
      e.inv ≫ pullbackUnitMap v (idealInclusion i) := by
  simp only [Iso.trans_inv, Iso.symm_inv, flatChartIdealIso, asIso_hom, Category.assoc]
  rw [idealPullbackMap_inclusion]
  rfl

/-- The actual Fitting-norm chart generator is the SAME original functional coordinate. -/
theorem flatChartIdealTopFrame_scalar :
    idealFrameScalar i' ⊤ (flatChartIdealTopFrame i i' v a H hI e) =
      Modules.Hom.app (e.inv ≫ pullbackUnitMap v (idealInclusion i)) ⊤ (1 : Γ(Y, ⊤)) := by
  change idealFrameScalar i' ⊤ ((SheafOfModules.overFunctor Y.ringCatSheaf ⊤).mapIso
    ((flatChartIdealIso i i' v a H hI).symm ≪≫ e)) = _
  rw [idealFrameScalar_top_eq_app_one, flatChartIdealFrame_coordinate]

/-- Its full-boundary value follows from the original prescribed functional
coordinate equation, without a new generator-normalization assumption. -/
theorem flatChartIdealTopFrame_boundary_scalar {B : Scheme.{u}} (b : B ⟶ Y)
    (θ : SheafOfModules.unit B.ringCatSheaf ⟶ SheafOfModules.unit B.ringCatSheaf)
    (hb : unitEndomorphismPullback b (e.inv ≫ pullbackUnitMap v (idealInclusion i)) = θ) :
    b.appTop (idealFrameScalar i' ⊤ (flatChartIdealTopFrame i i' v a H hI e)) =
      Modules.Hom.app θ ⊤ (1 : Γ(B, ⊤)) := by
  rw [flatChartIdealTopFrame_scalar, ← unitEndomorphismPullback_app_one, hb]

end AlgebraicGeometry.Scheme.Hom
