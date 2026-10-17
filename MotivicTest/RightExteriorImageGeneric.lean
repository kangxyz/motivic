/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightExteriorImageGeneric

/-!
# Actual right exterior generic-support consumers

The arbitrary-field consumers expose both original Cartesian squares, the
finite whole-image projection, the literal commuting equality, and genericity
without genericity-preservation or geometric purity supplied as hypotheses.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.RightExteriorImageGeneric

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The first step is over the original normal smooth Z, with H as finite support. -/
theorem actualFirstSupportCartesianSquare :
    IsPullback (F.rightExteriorFirstSupportMap G H)
      (pullback.snd (F.targetProjection ≫ Y.hom) (G.incidenceSource H ≫ Y.hom) ≫
        G.incidenceSnd H)
      (pullback.snd (F.targetProjection ≫ Y.hom) (G.projection ≫ Y.hom) ≫
        G.targetProjection)
      H.projection :=
  F.rightExteriorFirstSupportMap_isPullback G H

/-- The second step is over the original normal smooth Y, with G as finite support. -/
theorem actualSecondSupportCartesianSquare :
    IsPullback (F.rightExteriorFirstSourceMap G)
      (pullback.snd (F.targetProjection ≫ Y.hom) (G.projection ≫ Y.hom))
      (pullback.snd (F.targetProjection ≫ Y.hom) Y.hom) G.projection :=
  F.rightExteriorFirstSourceMap_isPullback G

/-- The whole image structure is retained in its finite projection. -/
theorem actualImageSourceFinite : IsFinite (F.rightExteriorImageSourceMap G H) :=
  F.isFinite_rightExteriorImageSourceMap k G H

/-- The geometry used for generic reflection is attached to the actual image map. -/
theorem actualImageSourceCommutativity :
    F.rightIntermediateImageMap G H ≫ F.rightExteriorImageSourceMap G H =
      F.rightExteriorSourceMap G H :=
  F.rightIntermediateImageMap_source G H

/-- Arbitrary original source generics, with all collisions allowed, map to generics. -/
theorem actualExteriorImageGeneric (w : genericPoints (F.rightIntermediateSupportProduct G H)) :
    F.rightIntermediateImageMap G H w.1 ∈ genericPoints (F.rightIntermediateImageProduct G H) :=
  F.rightIntermediateImageMap_mem_genericPoints k G H w.1 w.2

end MotivicTest.RightExteriorImageGeneric
