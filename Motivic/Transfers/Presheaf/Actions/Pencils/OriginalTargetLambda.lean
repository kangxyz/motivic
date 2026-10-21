/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.StaticBoundaryPencilAction
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionActionGeometry
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CorrespondenceSites
/-! # One target lambda from the unchanged target section pair

The E3 and E5 callers use this one numerator-minus-pole correspondence. Its
sections and line bundle are arguments from the single original target choice;
there is no section producer, coefficient shrink, or action premise here.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
/-- The smoothness instance used in this module. -/
local instance originalTargetLambdaSmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

variable (k : Type u) [Field k] {S X A C Z D : Scheme.{u}}
  [IsAffine S] [IsAffine X] [IsAffine A]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (π : C ⟶ S) [IsProper π]
  (j : X ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (z : Z ⟶ X) (d : D ⟶ C)
  (a : A ⟶ X) [IsOpenImmersion a]
  [SmoothOfRelativeDimension 1 ((a ≫ j) ≫ π)]
  (hc : ∀ x : C, x ∈ Set.range (a ≫ j) ∨ x ∈ Set.range d ∨
    x ∈ Set.range (z ≫ j))
  (L : LineBundle (pullback (j ≫ π) π))
  (aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ L (dualLineBundle _ (relativeCompactificationGraphLine π j))).val)
  (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ L.val)
  [IsIso (pullbackSectionMap (fullBoundaryProductMap π j d z) aS)]
  [IsIso (pullbackSectionMap (fullBoundaryProductMap π j d z) bS)]

/-- The literal single target correspondence, shared by both middle comparisons. -/
def originalTargetLambda :
    Cor.mk (lambdaSourceSite k t π j) ⟶ Cor.mk (relativeTargetSite k t π (a ≫ j)) := by
  let X₀ := lambdaSourceSite k t π j
  let Q := relativeTargetSite k t π (a ≫ j)
  let i := retainedProductInclusion (j ≫ π) π (a ≫ j)
  let : IsAffine X₀.left := ‹IsAffine X›
  let : IsAffine (retainedProduct (j ≫ π) π (a ≫ j)) :=
    retainedProduct_affine (j ≫ π) π (a ≫ j)
  let : SmoothOfRelativeDimension 1 (i ≫ pullback.fst (j ≫ π) π) :=
    retainedProduct_smooth (j ≫ π) π (a ≫ j)
  let hcover := lambdaBoundary_retained_cover π j z d (a ≫ j) hc
  let hb := retainedProduct_structure (j ≫ π) π (a ≫ j) t
  exact Cor.boundarySection X₀ Q (fullBoundaryProductMap π j d z)
      (pullback.fst (j ≫ π) π) i
      (tensorLineBundle _ L (dualLineBundle _ (relativeCompactificationGraphLine π j)))
      hcover (pullback.snd (j ≫ π) ((a ≫ j) ≫ π)) hb aS -
    Cor.boundarySection X₀ Q (fullBoundaryProductMap π j d z)
      (pullback.fst (j ≫ π) π) i L hcover
      (pullback.snd (j ≫ π) ((a ≫ j) ≫ π)) hb bS

end AlgebraicGeometry.Scheme.RelativeCurvePencil
