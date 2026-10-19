/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.ZeroRow
/-! Padding and erasing the auxiliary zero row leaves every original coordinate unchanged. -/
set_option linter.hashCommand false
public noncomputable section
open _root_.MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)

example (c : Fin d × Exponent σ → k) :
    quadraticCoordinateHom k R g (d + 1) (prependParameters k d 0 c) =
      (quadraticCoordinateHom k R g d c).comp (eraseZeroRow k d) :=
  quadraticCoordinateHom_prepend_zero k R g d c

example (c : Fin 0 × Exponent σ → k) :
    quadraticCoordinateHom k R g 1 (prependParameters k 0 0 c) =
      (quadraticCoordinateHom k R g 0 c).comp (eraseZeroRow k 0) :=
  quadraticCoordinateHom_prepend_zero k R g 0 c

#print axioms quadraticCoordinateHom_prepend_zero
#print axioms noCommonInfinityZero_prepend_zero
end QuadraticIncidence.InfinityChart
