/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.AffineImageChart
/-! Actual quadratic coordinate maps and their native schematic images, not assumed chart rings. -/
set_option linter.hashCommand false
public noncomputable section
open AlgebraicGeometry ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} (g : σ → R) (j : Exponent σ)
  (hj : monomialFunction k R g j ≠ 0)

example : (nativeChartGenericMap k R g j).image ≅ Spec (.of (chart k R g j)) :=
  nativeChartImageIso k R g j hj

example : (nativeDehomogenization k R g j).range = (chart k R g j).toSubring :=
  nativeDehomogenization_range k R g j hj

example (e : Exponent σ) :
    nativeDehomogenization k R g j (coordinateRatio k (Exponent σ) j e) = ratio k R g j e :=
  nativeDehomogenization_ratio k R g j e hj

#print axioms nativeChartImageIso
#print axioms nativeDehomogenizationQuotientEquiv
end QuadraticIncidence.InfinityChart
