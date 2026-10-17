/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticGraphNoInfinity
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.OpenGraphFinite
/-! # The unchanged quadratic tuple is finite from actual same-family infinity avoidance -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  [IsNoetherianRing R] {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)

/-- The original tuple, not a newly chosen projection, is finite. Its proof uses the
whole schematic graph and the entire original affine source. -/
theorem quadraticTupleMap_isFinite
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (c : Fin (d + 1) × Exponent σ → k) (hc : NoCommonInfinityZero k R g d c) :
    IsFinite (quadraticTupleMap k R g d c) := by
  have := quadraticOriginalToImage_isOpenImmersion k R g hg
  exact Scheme.isFinite_of_graph_image_range (quadraticOriginalToImage k R g)
    (quadraticImageProjection k R g)
    (Spec.map (CommRingCat.ofHom (C : k →+* MvPolynomial (Fin (d + 1)) k)))
    (quadraticTupleMap k R g d c) _
    (quadraticOriginalGraph_no_infinity k R g d hg c hc)

end QuadraticIncidence.InfinityChart
