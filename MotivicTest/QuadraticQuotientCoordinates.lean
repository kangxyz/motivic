/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.QuotientCoordinates
/-! Exact generators and coordinates on the original quotient, including nilpotent thickenings. -/
set_option linter.hashCommand false
public noncomputable section
open AlgebraicGeometry
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ) (I : Ideal R)

example (c : Fin d × Exponent σ → k) :
    quadraticCoordinateHom k (R ⧸ I ^ 2) (Ideal.Quotient.mk (I ^ 2) ∘ g) d c =
      (Ideal.Quotient.mk (I ^ 2)).comp (quadraticCoordinateHom k R g d c) :=
  quadraticCoordinateHom_quotient k R g d (I ^ 2) c

example (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    Algebra.adjoin k (Set.range (Ideal.Quotient.mk (I ^ 2) ∘ g)) = ⊤ :=
  quadraticGenerators_quotient k R g (I ^ 2) hg

#print axioms quadraticGenerators_quotient
#print axioms quadraticCoordinateHom_quotient
end QuadraticIncidence.InfinityChart
