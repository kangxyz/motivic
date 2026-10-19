/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Compactification.OriginalEmbedding
/-! The actual original affine embedding needs only the given algebra generators. -/
set_option linter.hashCommand false
public noncomputable section
open AlgebraicGeometry
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  {σ : Type u} (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)

example : Function.Surjective (quadraticConstantChartMap k R g) :=
  quadraticConstantChartMap_surjective k R g hg

example : IsImmersion (quadraticOriginalMap k R g) :=
  quadraticOriginalMap_isImmersion k R g hg

example [IsNoetherianRing R] : IsOpenImmersion (quadraticOriginalMap k R g).toImage :=
  quadraticOriginalMap_toImage_isOpenImmersion k R g hg

#print axioms quadraticOriginalMap_isImmersion
#print axioms quadraticOriginalMap_toImage_isOpenImmersion
end QuadraticIncidence.InfinityChart
