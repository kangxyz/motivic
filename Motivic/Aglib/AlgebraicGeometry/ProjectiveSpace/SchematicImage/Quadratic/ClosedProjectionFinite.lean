/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.ProjectionFinite
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.QuotientCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.MinimalComponentQuotient
public import Motivic.Aglib.RingTheory.Bertini.QuadraticClosedInfinityAvoidance
/-! # The unchanged projection is finite on the full original closed subscheme -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry _root_.MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  [IsNoetherianRing R] {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)

/-- Any number of rows is allowed. The zero auxiliary row is eliminated from the
finite algebra action, leaving the literal original projection. -/
theorem quadraticCoordinateHom_finite_of_no_infinity [IsDomain R]
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (c : Fin d × Exponent σ → k)
    (h : ∀ j : Exponent σ, monomialFunction k R g j ≠ 0 →
      ∀ (K : Type u) [Field K] [Algebra k K] [Algebra (boundaryRing k R g j) K]
        [IsScalarTower k (boundaryRing k R g j) K],
        ¬ ProjectiveEvaluationIncidence.Vanishes k (boundaryRing k R g j) K
          (boundaryCoordinate k R g j) d c) :
    (quadraticCoordinateHom k R g d c).Finite := by
  have hf : (quadraticCoordinateHom k R g (d + 1) (prependParameters k d 0 c)).Finite :=
    (IsFinite.SpecMap_iff _).mp (quadraticTupleMap_isFinite k R g d hg _
      (noCommonInfinityZero_prepend_zero k R g d c h))
  rw [quadraticCoordinateHom_prepend_zero] at hf
  exact RingHom.Finite.of_comp_finite hf

/-- The original possibly nonreduced closed scheme, not its reduction, is finite
under the unchanged tail projection; d = 0 is included. -/
theorem quadraticClosedTuple_isFinite (I : Ideal R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (c : Fin d × Exponent σ → k) (hc : NoCommonClosedInfinityZero k R I g d c) :
    IsFinite (Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k R g d c)))) := by
  apply isFinite_quotient_of_minimal_components
  intro P hP
  let : P.IsPrime := hP.isPrime
  apply (IsFinite.SpecMap_iff _).mpr
  rw [← quadraticCoordinateHom_quotient]
  exact quadraticCoordinateHom_finite_of_no_infinity k (R ⧸ P)
    (Ideal.Quotient.mk P ∘ g) d (quadraticGenerators_quotient k R g P hg) c (hc ⟨P, hP⟩)

end QuadraticIncidence.InfinityChart
