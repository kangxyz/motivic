/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.GlobalChartCoordinates
/-! Direct original-closure and whole-chart coordinate consumers. -/
set_option linter.hashCommand false
public noncomputable section
open CategoryTheory Limits AlgebraicGeometry ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} (g : σ → R) (j : Exponent σ)
  (hj : monomialFunction k R g j ≠ 0)

example : (quadraticOriginalMap k R g).ker = (quadraticProjectiveGenericMap k R g).ker :=
  quadraticOriginalMap_ker k R g

example : pullback (quadraticChartInclusion k j)
    (quadraticProjectiveGenericMap k R g).imageι ≅ Spec (.of (chart k R g j)) :=
  quadraticProjectiveImageChartIso k R g j hj

example : quadraticRatioChartToImage k R g j hj ≫
    (quadraticProjectiveGenericMap k R g).imageι =
    Spec.map (CommRingCat.ofHom (nativeChartMapToRatioRing k R g j hj)) ≫
      quadraticChartInclusion k j :=
  quadraticRatioChartToImage_inclusion k R g j hj

example : quadraticRatioChartToImage k R g j hj ⁻¹ᵁ
    ((quadraticProjectiveGenericMap k R g).imageι ⁻¹ᵁ
      coordinateOpen k (Exponent σ) constantIndex) =
      PrimeSpectrum.basicOpen (infinityCoordinate k R g j) :=
  quadraticRatioChartToImage_preimage_constant k R g j hj

example (x : quadraticProjectiveImage k R g) :
    ∃ j : Exponent σ, monomialFunction k R g j ≠ 0 ∧
      (quadraticProjectiveGenericMap k R g).imageι x ∈ coordinateOpen k (Exponent σ) j :=
  quadraticProjectiveImage_exists_chart k R g x

#print axioms quadraticOriginalMap_ker
#print axioms quadraticProjectiveImageChartIso
#print axioms quadraticRatioChartToImage_inclusion
#print axioms quadraticRatioChartToImage_preimage_constant
#print axioms quadraticProjectiveImage_exists_chart
end QuadraticIncidence.InfinityChart
