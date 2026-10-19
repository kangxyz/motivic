/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphCoordinate
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedTargetChartFrame

/-! # The original target section-pair coefficient on the retained parameter chart

The target frame is determined by the same numerator and pole, then transported
along the original retained map. No prescribed affine extension is chosen.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.RetainedSectionPairCoefficient`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairNativeTargetScalar`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairNormIdeal`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S C P X Y W : Scheme.{u}} (π : P ⟶ S) [IsSeparated π]
  (f : C ⟶ P) (jB : Y ⟶ C) (jA : X ⟶ P) [IsOpenImmersion jA]
  [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) [Flat p] (h : jB ≫ f = p ≫ jA)
  [IsClosedImmersion (Hom.targetCompactificationGraph π f jB)]
  (T : LineBundle (pullback (jA ≫ π) π))
  (aS : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ T (dualLineBundle _
      (Hom.relativeCompactificationGraphLine π jA))).val)
  (bS : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ T.val)
  (v : W ⟶ pullback (jA ≫ π) π)
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ T bS) v)]
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
    (tensorLineBundle _ T (dualLineBundle _
      (Hom.relativeCompactificationGraphLine π jA))) aS) v)]

local instance : IsClosedImmersion (Hom.compactificationGraph π jA) := by
  dsimp [Hom.compactificationGraph]
  infer_instance

/-- The actual transported target ideal frame has the original section-pair
coefficient, pulled along the literal inverse-chart projection. -/
theorem retainedSectionPairChartFrame_coordinate :
    (Hom.retainedTargetChartFrame π f jB jA p h
      (Hom.relativeCompactificationGraphLine π jA).property v
      (sectionPairIdealFrame v (Hom.relativeCompactificationGraphLine π jA) T bS aS)).inv ≫
      pullbackUnitMap (pullback.fst (Hom.retainedParameterProductMap π f jB jA p h) v)
        (Hom.idealInclusion (Hom.targetCompactificationGraph π f jB)) =
    Hom.unitEndomorphismPullback
      (pullback.snd (Hom.retainedParameterProductMap π f jB jA p h) v)
      (sectionPairGraphCoefficient π jA T aS bS v) :=
  Hom.retainedTargetChartFrame_coordinate π f jB jA p h
    (Hom.relativeCompactificationGraphLine π jA).property v
    (sectionPairIdealFrame v (Hom.relativeCompactificationGraphLine π jA) T bS aS)

/-- Evaluation retains the exact original structural maps. The graph coefficient
is not assumed invertible, including on the marked incidence scheme. -/
theorem retainedSectionPairChartFrame_scalar {B : Scheme.{u}}
    (r : B ⟶ pullback (Hom.retainedParameterProductMap π f jB jA p h) v) :
    r.appTop (Modules.Hom.app
      ((Hom.retainedTargetChartFrame π f jB jA p h
        (Hom.relativeCompactificationGraphLine π jA).property v
        (sectionPairIdealFrame v (Hom.relativeCompactificationGraphLine π jA) T bS aS)).inv ≫
        pullbackUnitMap (pullback.fst (Hom.retainedParameterProductMap π f jB jA p h) v)
          (Hom.idealInclusion (Hom.targetCompactificationGraph π f jB))) ⊤
      (1 : Γ(pullback (Hom.retainedParameterProductMap π f jB jA p h) v, ⊤))) =
    (r ≫ pullback.snd (Hom.retainedParameterProductMap π f jB jA p h) v).appTop
      (Modules.Hom.app (sectionPairGraphCoefficient π jA T aS bS v) ⊤ (1 : Γ(W, ⊤))) := by
  rw [retainedSectionPairChartFrame_coordinate]
  have hscalar := congrArg
    (fun c : Γ(pullback (Hom.retainedParameterProductMap π f jB jA p h) v, ⊤) => r.appTop c)
    (Hom.unitEndomorphismPullback_app_one
      (pullback.snd (Hom.retainedParameterProductMap π f jB jA p h) v)
      (sectionPairGraphCoefficient π jA T aS bS v))
  simpa only [Hom.comp_appTop, CommRingCat.comp_apply] using hscalar

end AlgebraicGeometry.Scheme.RelativeCurvePencil
