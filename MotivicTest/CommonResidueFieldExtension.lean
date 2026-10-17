/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.CommonResidueFieldExtension
public import Motivic.Aglib.RingTheory.Kaehler.ResidueIndependentSmoothMap
public import Lean

/-! # Genuine same-fiber points acquire original-map relative curve neighborhoods -/
public noncomputable section
open Module TensorProduct KaehlerDifferential AlgebraicGeometry QuadraticIncidence
universe u
namespace MotivicTest.CommonResidueFieldExtension

/-- Distinct residue fields over a common image are handled without a chosen embedding. -/
theorem actual_common_residue_field (k A R : Type u) [Field k] [CommRing A] [CommRing R]
    [Algebra k A] [Algebra k R] (φ : A →ₐ[k] R) (P Q : PrimeSpectrum R)
    (hPQ : Ideal.comap φ.toRingHom P.asIdeal = Ideal.comap φ.toRingHom Q.asIdeal) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (i : P.asIdeal.ResidueField →ₐ[k] K) (j : Q.asIdeal.ResidueField →ₐ[k] K),
      ∀ a : A, i (algebraMap R P.asIdeal.ResidueField (φ a)) =
        j (algebraMap R Q.asIdeal.ResidueField (φ a)) :=
  exists_common_residue_field k A R φ P Q hPQ

/-- The all-field condition is consumed at the unchanged prime and unchanged polynomial map. -/
theorem actual_same_fiber_smooth_neighborhood
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P Q : PrimeSpectrum R) (d : ℕ) (f : Fin d → R)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (hPQ : Ideal.comap (MvPolynomial.aeval (R := k) f).toRingHom P.asIdeal =
      Ideal.comap (MvPolynomial.aeval (R := k) f).toRingHom Q.asIdeal)
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [Algebra R K]
      [Algebra (ClosedPoint.CoefficientRing k R P) K]
      [IsScalarTower k (ClosedPoint.CoefficientRing k R P) K]
      [IsScalarTower R (ClosedPoint.CoefficientRing k R P) K],
      (∀ i, algebraMap R K (f i) = algebraMap (ClosedPoint.CoefficientRing k R P) K
        (ClosedPoint.selectedValue k R P (f i))) →
      LinearIndependent K (fun i => (1 ⊗ₜ[R] D k R (f i) : K ⊗[R] Ω[R⁄k]))) :
    ∃ r : R, Q ∈ PrimeSpectrum.basicOpen r ∧ SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
        (MvPolynomial.aeval (R := k) f).toRingHom))) := by
  exact exists_smooth_one_of_residue_independent k R Q.asIdeal d f hd
    (independent_differentials_of_same_fiber k R P Q d f hPQ h)

open Lean in
run_cmd do
  for name in #[``actual_common_residue_field, ``actual_same_fiber_smooth_neighborhood,
      ``exists_common_field, ``exists_common_residue_field, ``independent_differentials_descend,
      ``independent_differentials_of_same_fiber] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Common actual residue extension and same-fiber smooth neighborhoods: audited."

end MotivicTest.CommonResidueFieldExtension
