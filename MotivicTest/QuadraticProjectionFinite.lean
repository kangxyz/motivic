/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticProjectionFinite
/-! Finiteness of the unchanged original tuple, not a second choice of coordinates. -/
set_option linter.hashCommand false
public noncomputable section
open AlgebraicGeometry
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  [IsNoetherianRing R] {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)
  (hg : Algebra.adjoin k (Set.range g) = ⊤)
  (c : Fin (d + 1) × Exponent σ → k) (hc : NoCommonInfinityZero k R g d c)

example : IsFinite (quadraticTupleMap k R g d c) :=
  quadraticTupleMap_isFinite k R g d hg c hc

#print axioms quadraticTupleMap_isFinite
end QuadraticIncidence.InfinityChart
