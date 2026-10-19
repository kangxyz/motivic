/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedAffineCover
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Diagonal.IntermediateLists

/-!
# Whole intermediate finite-preimage ambient covers

The cover includes every point in the actual finite inverse image. Its size
is derived from quasi-compactness, with no integrality or dimension restriction.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace Motivic.MotivicTest.ClosedAffineCover

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated g]

/-- The entire original first-stage finite preimage admits an actual finite
ambient affine cover. No selected source stalk replaces the inverse image. -/
theorem actualWholeIntermediatePreimage [IsSeparated h]
    (U : (F.leftIntermediateImageProduct G H).affineOpens) :
    ∃ s : Finset (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens,
      (∀ V ∈ s, (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ V ≤
        (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) ∧
      (⨆ V ∈ s, (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ V) =
        (F.leftIntermediateImageMap G H) ⁻¹ᵁ U :=
  _root_.AlgebraicGeometry.Scheme.Hom.ClosedAffineCover.finiteMap_exists_whole_preimage_cover
    (F.leftIntermediateAmbientInclusion G H) (F.leftIntermediateImageMap G H) U

/-- The genuine ambient inverse images are affine, as required by the Tor charts. -/
theorem actualIntermediateChartAffine
    (V : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens) :
    IsAffineOpen ((F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ V) :=
  _root_.AlgebraicGeometry.Scheme.Hom.ClosedAffineCover.preimage_isAffineOpen _ V

/-- An arbitrary source neighborhood is respected, not merely the point itself. -/
theorem actualIntermediateNeighborhood
    (V : (F.leftIntermediateSupportProduct G H).Opens)
    {x : F.leftIntermediateSupportProduct G H} (hx : x ∈ V) :
    ∃ U : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens,
      x ∈ (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ U ∧
      (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ U ≤ V :=
  _root_.AlgebraicGeometry.Scheme.Hom.ClosedAffineCover.exists_ambient_affine_neighborhood _ V hx

end Motivic.MotivicTest.ClosedAffineCover
