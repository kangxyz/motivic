/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticOriginalOpen
/-! The original affine source, not a further neighborhood, is detected by h on each chart. -/
set_option linter.hashCommand false
public noncomputable section
open AlgebraicGeometry ProjectiveSpace
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  [IsNoetherianRing R] {σ : Type u} (g : σ → R)
  (hg : Algebra.adjoin k (Set.range g) = ⊤)

example : Set.range (quadraticOriginalToImage k R g) =
    (quadraticProjectiveGenericMap k R g).imageι ⁻¹'
      (coordinateOpen k (Exponent σ) constantIndex : Set _) :=
  quadraticOriginalToImage_range k R g hg

example (j : Exponent σ) (hj : monomialFunction k R g j ≠ 0) :
    quadraticRatioChartToImage k R g j hj ⁻¹' Set.range (quadraticOriginalToImage k R g) =
      (PrimeSpectrum.basicOpen (infinityCoordinate k R g j)).carrier :=
  quadraticRatioChartToImage_preimage_original k R g hg j hj

#print axioms quadraticOriginalToImage_range
#print axioms quadraticRatioChartToImage_preimage_original
end QuadraticIncidence.InfinityChart
