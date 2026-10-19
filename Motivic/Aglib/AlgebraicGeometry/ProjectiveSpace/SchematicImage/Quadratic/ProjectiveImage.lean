/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.ChartOverlap
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.AffineImageChart
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.OpenChart
/-! # One actual projective schematic image for the original quadratic coordinates -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry ProjectiveSpace _root_.MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} (g : σ → R)

/-- The original native projective coordinate-chart immersion. -/
abbrev quadraticChartInclusion (j : Exponent σ) :=
  Proj.awayι (homogeneousSubmodule (Exponent σ) k) (X j)
    (isHomogeneous_X k j) Nat.zero_lt_one

/-- One projective generic point, defined using the original constant monomial. -/
def quadraticProjectiveGenericMap :
    Spec (.of (FractionRing R)) ⟶ ProjectiveSpace k (Exponent σ) :=
  nativeChartGenericMap k R g constantIndex ≫ quadraticChartInclusion k constantIndex

/-- Every original nonzero monomial chart factors the same projective map. -/
theorem nativeChartGenericMap_projective (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) :
    nativeChartGenericMap k R g j ≫ quadraticChartInclusion k j =
      quadraticProjectiveGenericMap k R g := by
  have hc : monomialFunction k R g (constantIndex (σ := σ)) ≠ 0 := by simp
  dsimp only [nativeChartGenericMap, quadraticProjectiveGenericMap]
  rw [nativeDehomogenization_eq_awayEvaluation k R g j hj,
    nativeDehomogenization_eq_awayEvaluation k R g constantIndex hc]
  exact homogeneousAwayEvaluation_projective_eq k R g _ _ _ _ _ _

/-- The actual projective schematic image, not independently specified affine charts. -/
abbrev quadraticProjectiveImage := (quadraticProjectiveGenericMap k R g).image

/-- Every nonzero quadratic chart of the single global schematic image has the
actual original monomial-ratio algebra as its coordinate ring. -/
def quadraticProjectiveImageChartIso (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) :
    pullback (quadraticChartInclusion k j) (quadraticProjectiveGenericMap k R g).imageι ≅
      Spec (.of (chart k R g j)) :=
  Scheme.imageOpenChartIso (quadraticProjectiveGenericMap k R g)
    (quadraticChartInclusion k j) (nativeChartGenericMap k R g j)
    (nativeChartGenericMap_projective k R g j hj) ≪≫ nativeChartImageIso k R g j hj

end QuadraticIncidence.InfinityChart
