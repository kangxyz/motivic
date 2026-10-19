/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateUnitOnOpen
public import Motivic.Aglib.AlgebraicGeometry.Divisors.Order.IdealFrameOrderCancellation
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PullbackRatioScalar

/-!
# Scalar evaluation of the original ideal frame on the full boundary

The original unit-endomorphism equation is evaluated on one using the actual
structure ring map. No new frame, reduced boundary, or invertible graph scalar
is introduced. Concrete marked and residual coordinate equations remain inputs.


Intended upstream module:
`Aglib.AlgebraicGeometry.EffectiveCartierDivisor.IdealFrameBoundaryScalar`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FlatChartIdealCoordinate`,
`Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.FunctionalCoordinate`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLocalRatio`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.CoherentIdealCoordinate`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.GraphScalar`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphCoordinate`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.BoundaryRatio`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalRatioBoundary`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- Actual pullback of a unit endomorphism retains its original scalar at one. -/
theorem unitEndomorphismPullback_app_one {X Y : Scheme.{u}} (b : Y ⟶ X)
    (θ : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (show Γ(Y, ⊤) from
      Modules.Hom.app (unitEndomorphismPullback b θ) ⊤ (1 : Γ(Y, ⊤))) =
      b.appTop (Modules.Hom.app θ ⊤ (1 : Γ(X, ⊤))) := by
  have hid : pullbackUnitMap b (𝟙 (SheafOfModules.unit X.ringCatSheaf)) =
      (pullbackUnitIso b).hom := by simp [pullbackUnitMap]
  have : IsIso (pullbackUnitMap b (𝟙 (SheafOfModules.unit X.ringCatSheaf))) := by
    rw [hid]
    infer_instance
  have h := pullback_ratio_mul_section b θ (𝟙 _) (1 : Γ(X, ⊤))
  change (Modules.Hom.app (pullbackUnitIso b).hom ⊤)
      ((Modules.Hom.app ((Modules.pullback b).map θ) ⊤)
        ((Modules.Hom.app (pullbackUnitIso b).inv ⊤) (1 : Γ(Y, ⊤)))) = _
  simpa [hid, pullbackUnitMap] using h

/-- The whole-space chart scalar is evaluation of the SAME global ideal frame. -/
theorem idealFrameScalar_top_eq_app_one {D X : Scheme.{u}} (i : D ⟶ X)
    (e : idealModule i ≅ SheafOfModules.unit X.ringCatSheaf) :
    idealFrameScalar i ⊤ ((SheafOfModules.overFunctor X.ringCatSheaf ⊤).mapIso e) =
      Modules.Hom.app (e.inv ≫ idealInclusion i) ⊤ (1 : Γ(X, ⊤)) := rfl

/-- An actual full-boundary endomorphism equality determines the exact image of
its original ideal-frame scalar, even where that scalar vanishes. -/
theorem idealFrameScalar_boundary_eq {D X Y : Scheme.{u}} (i : D ⟶ X)
    (e : idealModule i ≅ SheafOfModules.unit X.ringCatSheaf) (b : Y ⟶ X)
    (θ : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (h : unitEndomorphismPullback b (e.inv ≫ idealInclusion i) = θ) :
    b.appTop (idealFrameScalar i ⊤
      ((SheafOfModules.overFunctor X.ringCatSheaf ⊤).mapIso e)) =
        Modules.Hom.app θ ⊤ (1 : Γ(Y, ⊤)) := by
  rw [idealFrameScalar_top_eq_app_one, ← unitEndomorphismPullback_app_one, h]

end AlgebraicGeometry.Scheme.Hom
