/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ContractionBoundaryProjectionCompatibility
public import Motivic.Cohomology.A1.ContractionBoundaryMono
public import Motivic.Cohomology.A1.PresheafBoundaryOpenZero
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleA1Coefficient
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedSupportUnit
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-! # The actual ambient projection on the literal split cylinder

The original boundary projection square and the genuine support units imply
invertibility of the original ambient cokernel map. Support is used only on
the two literal cylinder models. The canonical boundary epimorphisms remain
explicit inputs; the open-support premise is discharged from the original
restriction map, not supplied as a purity hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.FiniteEtaleSite

variable {k : Type u} [Field k] (X : SmoothSite (Spec (CommRingCat.of k)))
  (F : SheafWithTransfers.{u + 1} k)

local notation "X₁" => SmoothSite.a1Cylinder (CommRingCat.of k) X
local notation "π" => SmoothSite.a1Projection (CommRingCat.of k) X
local notation "p" => SmoothSite.a1Map (CommRingCat.of k) π
local notation "j₀" => SmoothSite.contractionOpen (CommRingCat.of k) X
local notation "j₁" => SmoothSite.contractionOpen (CommRingCat.of k) X₁
local notation "i₀" => SmoothSite.a1Section (CommRingCat.of k) X 0
local notation "i₁" => SmoothSite.a1Section (CommRingCat.of k) X₁ 0
local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F

/-- The actual boundary projection is invertible once the two original
canonical boundary epimorphisms are supplied. Only ordinary HI is used. -/
theorem contractionBoundaryProjection_isIso (hF : F.obj.IsA1Invariant)
    (hE₀ : Epi (contractionToBoundary X F hF))
    (hE₁ : Epi (contractionToBoundary X₁ F hF)) :
    IsIso (contractionBoundaryProjection X F) := by
  let := hE₀
  let := hE₁
  let := contractionToBoundary_mono X F hF
  let := contractionToBoundary_mono X₁ F hF
  let : IsIso (contractionToBoundary X F hF) := isIso_of_mono_of_epi _
  let : IsIso (contractionToBoundary X₁ F hF) := isIso_of_mono_of_epi _
  let H := (SheafWithTransfers.toSheaf k).obj (SheafWithTransfers.contraction F hF)
  let := a1RestrictionCoefficient_isIso (CommRingCat.of k) X H
    (SheafWithTransfers.contraction_isA1Invariant F hF)
  let : IsIso (contractionToBoundary X F hF ≫ contractionBoundaryProjection X F) := by
    rw [contractionToBoundary_projection]
    infer_instance
  exact IsIso.of_isIso_comp_left (contractionToBoundary X F hF) _

/-- The literal cylinder's actual ambient quotient is carried isomorphically
by its genuine zero-section support unit. Its open restriction vanishes by
the original identity-open cokernel calculation. -/
theorem contractionAmbientSupportUnit_isIso :
    IsIso ((imageAdjunction (i₀).left).unit.app (boundaryAmbientCokernel G j₀)) := by
  exact splitClosed_support_unit_isIso (i₀).left (π).left
    (congrArg (fun f ↦ f.left) (SmoothSite.a1Section_projection (CommRingCat.of k) X 0))
    (j₀).left (SmoothSite.range_a1Section_zero (CommRingCat.of k) X)
    (boundaryAmbientCokernel G j₀)
    (inverseImage_open_boundaryAmbientCokernel_isZero G j₀)

/-- The original ambient cokernel projection is invertible. This follows from
the exact original unit square, not an abstract purity isomorphism or any
support assertion on a later étale neighborhood. -/
theorem contractionAmbientProjection_isIso (hF : F.obj.IsA1Invariant)
    (hE₀ : Epi (contractionToBoundary X F hF))
    (hE₁ : Epi (contractionToBoundary X₁ F hF)) :
    IsIso (contractionAmbientProjectionMap X F) := by
  let := contractionBoundaryProjection_isIso X F hF hE₀ hE₁
  let := contractionAmbientSupportUnit_isIso X F
  let := contractionAmbientSupportUnit_isIso X₁ F
  let t := (directImage (p).left).map
      ((imageAdjunction (i₁).left).unit.app (boundaryAmbientCokernel G j₁)) ≫
    (contractionZeroProjectionDirectImageIso X).hom.app (zeroSectionBoundary X₁ F)
  let : IsIso t := by
    dsimp only [t]
    infer_instance
  let : IsIso (contractionAmbientProjectionMap X F ≫ t) := by
    change IsIso (contractionAmbientProjectionMap X F ≫
      (directImage (p).left).map
        ((imageAdjunction (i₁).left).unit.app (boundaryAmbientCokernel G j₁)) ≫
      (contractionZeroProjectionDirectImageIso X).hom.app (zeroSectionBoundary X₁ F))
    rw [← contractionBoundaryProjection_unit]
    infer_instance
  exact IsIso.of_isIso_comp_right (contractionAmbientProjectionMap X F) t

end Motivic.FiniteEtaleSite
