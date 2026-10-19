/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.ClosedProjectionFinite
/-! The original closed scheme and the zero-row edge case retain their exact coordinate maps. -/
set_option linter.hashCommand false
public noncomputable section
open AlgebraicGeometry
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  [IsNoetherianRing R] {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)
  (I : Ideal R) (hg : Algebra.adjoin k (Set.range g) = ⊤)

example (c : Fin d × Exponent σ → k) (hc : NoCommonClosedInfinityZero k R I g d c) :
    IsFinite (Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k R g d c)))) :=
  quadraticClosedTuple_isFinite k R g d I hg c hc

example (c : Fin 0 × Exponent σ → k) (hc : NoCommonClosedInfinityZero k R I g 0 c) :
    IsFinite (Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k R g 0 c)))) :=
  quadraticClosedTuple_isFinite k R g 0 I hg c hc

#print axioms quadraticClosedTuple_isFinite
end QuadraticIncidence.InfinityChart
