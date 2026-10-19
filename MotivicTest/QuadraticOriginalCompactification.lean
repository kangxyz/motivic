/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Compactification.OriginalCompactification
/-! Actual original affine open in its same quadratic proper closure. -/
set_option linter.hashCommand false
public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  [IsNoetherianRing R] {σ : Type u} [Finite σ] (g : σ → R)
  (hg : Algebra.adjoin k (Set.range g) = ⊤)

example : IsProper (quadraticImageProjection k R g) := inferInstance

example : IsOpenImmersion (quadraticOriginalToImage k R g) :=
  quadraticOriginalToImage_isOpenImmersion k R g hg

example : quadraticOriginalToImage k R g ≫ quadraticImageProjection k R g =
    Spec.map (CommRingCat.ofHom (algebraMap k R)) :=
  quadraticOriginalToImage_projection k R g

example : pullback (quadraticChartInclusion k constantIndex)
    (quadraticProjectiveGenericMap k R g).imageι ≅ Spec (.of R) :=
  quadraticOriginalConstantChartIso k R g hg

example (j : Exponent σ) (hj : monomialFunction k R g j ≠ 0) :
    quadraticRatioChartToImage k R g j hj ≫ quadraticImageProjection k R g =
      Spec.map (CommRingCat.ofHom (algebraMap k (chart k R g j))) :=
  quadraticRatioChartToImage_projection k R g j hj

#print axioms quadraticRatioChartToImage_projection
#print axioms quadraticOriginalToImage_isPullback
#print axioms quadraticOriginalToImage_projection
#print axioms quadraticOriginalConstantChartIso
end QuadraticIncidence.InfinityChart
