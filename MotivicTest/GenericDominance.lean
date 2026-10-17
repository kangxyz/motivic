/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.GenericDominance
public import Motivic.Aglib.RingTheory.Ideal.GoingDown.MinimalPrimes
public import Mathlib.Algebra.DualNumber
public meta import Lean.Util.CollectAxioms

/-!
# Consumers of minimal-prime and generic-component dominance

The extension ring is never required to be reduced or a domain. Finite flat
algebras give an actual scheme-level consumer; the product algebra tests a
disconnected source rather than assuming every source scheme irreducible.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic

universe u v

namespace MotivicTest.GenericDominance

/-- Minimal-prime contraction allows independent ring universes. -/
theorem arbitrary_algebra {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.HasGoingDown R S] (P : Ideal S) (hP : IsMinimalPrime P) :
    IsMinimalPrime (P.under R) :=
  Ideal.minimalPrime_under_of_goingDown (R := R) P hP

/-- Only the base ring needs to be a domain. -/
theorem domain_base {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Algebra.HasGoingDown R S] (P : Ideal S) (hP : P ∈ minimalPrimes S) : P.under R = ⊥ :=
  Ideal.minimalPrime_under_eq_bot_of_goingDown (R := R) P hP

/-- The contraction uses the original algebra map, with no replacement algebra. -/
theorem contraction_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S] (P : Ideal S)
    (hP : IsMinimalPrime P) : IsMinimalPrime (Ideal.comap (algebraMap R S) P) :=
  Ideal.minimalPrime_under_of_goingDown (R := R) P hP

/-- Dual numbers contain an actual nonzero square-zero element. -/
theorem dual_numbers_nonzero_square_zero (k : Type u) [Field k] :
    (DualNumber.eps : DualNumber k) ≠ 0 ∧ (DualNumber.eps : DualNumber k) ^ 2 = 0 := by
  refine ⟨?_, DualNumber.eps_pow_two⟩
  intro h
  have := congrArg TrivSqZeroExt.snd h
  simp at this

/-- Minimal primes still contract to zero in the whole nonreduced dual-number algebra. -/
theorem dual_numbers_minimalPrime_under (k : Type u) [Field k]
    (P : Ideal (DualNumber k)) (hP : P ∈ minimalPrimes (DualNumber k)) : P.under k = ⊥ :=
  Ideal.minimalPrime_under_eq_bot_of_goingDown P hP

/-- Each reduced component of a finite flat algebra surjects onto the integral base. -/
theorem finite_flat_component_surjective (R S : Type u) [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    (x : genericPoints (Spec (.of S))) :
    Function.Surjective
      ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  apply surjective_pointClosure_of_finite_generalizing _ _ x.val x.property
  change GeneralizingMap (PrimeSpectrum.comap (algebraMap R S))
  exact Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp inferInstance

/-- The preceding component conclusion includes an actual disconnected source. -/
theorem product_component_surjective (R : Type u) [CommRing R] [IsDomain R]
    (x : genericPoints (Spec (.of (R × R)))) :
    Function.Surjective
      ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))) :=
  finite_flat_component_surjective R (R × R) x

open Lean in
run_cmd do
  for name in #[``Ideal.minimalPrime_under_of_goingDown,
      ``Ideal.minimalPrime_under_eq_bot_of_goingDown,
      ``arbitrary_algebra, ``domain_base, ``contraction_map,
      ``dual_numbers_nonzero_square_zero, ``dual_numbers_minimalPrime_under,
      ``finite_flat_component_surjective, ``product_component_surjective] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Minimal-prime contraction and its generic-component consumers use standard foundations."

end MotivicTest.GenericDominance
