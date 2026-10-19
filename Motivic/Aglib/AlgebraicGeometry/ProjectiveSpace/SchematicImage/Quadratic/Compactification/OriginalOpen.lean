/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Compactification.OriginalCompactification
/-! # The original affine open is exactly the complement of the quadratic infinity coordinate -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry ProjectiveSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  [IsNoetherianRing R] {σ : Type u} (g : σ → R)

/-- This identifies the entire original source, rather than a smaller smooth neighborhood. -/
theorem quadraticOriginalToImage_range (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    Set.range (quadraticOriginalToImage k R g) =
      (quadraticProjectiveGenericMap k R g).imageι ⁻¹'
        (coordinateOpen k (Exponent σ) constantIndex : Set _) := by
  rw [← range_eq_range_of_surjective
    (pullback.snd (quadraticChartInclusion k constantIndex)
      (quadraticProjectiveGenericMap k R g).imageι)
    (quadraticOriginalToImage k R g)
    (quadraticOriginalConstantChartIso k R g hg).hom
    (quadraticOriginalConstantChartIso_hom_toImage k R g hg)]
  rw [Scheme.Pullback.range_snd, ← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
  rfl

/-- The actual affine source pulls back on each native ratio chart to the original D(h_j). -/
theorem quadraticRatioChartToImage_preimage_original
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (j : Exponent σ) (hj : monomialFunction k R g j ≠ 0) :
    quadraticRatioChartToImage k R g j hj ⁻¹' Set.range (quadraticOriginalToImage k R g) =
      (PrimeSpectrum.basicOpen (infinityCoordinate k R g j)).carrier := by
  rw [quadraticOriginalToImage_range k R g hg]
  exact congrArg SetLike.coe (quadraticRatioChartToImage_preimage_constant k R g j hj)

end QuadraticIncidence.InfinityChart
