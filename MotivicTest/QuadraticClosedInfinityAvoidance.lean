/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticClosedInfinityAvoidance
public import Motivic.Aglib.RingTheory.Bertini.WholeFiberSmoothProjection
public import Lean

/-! # Original minimal components and whole-fiber smoothness share one quadratic tuple -/
public noncomputable section
open MvPolynomial AlgebraicGeometry QuadraticIncidence QuadraticIncidence.InfinityChart
universe u
namespace MotivicTest.QuadraticClosedInfinityAvoidance

/-- The zero-dimensional case has no hidden positive-dimension premise. -/
theorem zero_dimension_actual_boundary (k R : Type u) [Field k] [CommRing R]
    [IsDomain R] [Algebra k R] {σ : Type u} (g : σ → R) (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) (hd : Algebra.trdeg k R = 0) :
    Subsingleton (boundaryRing k R g j) :=
  boundaryRing_subsingleton_of_trdeg_zero k R g j hj hd.le

/-- An arbitrary, possibly nonradical original ideal supplies its actual component family. -/
theorem actual_closed_components (k R : Type u) [Field k] [CommRing R]
    [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I ≠ ⊥) {σ : Type u} [Finite σ] (g : σ → R) (d : ℕ)
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1) :
    ∃ q : MvPolynomial (Fin d × Exponent σ) k, q ≠ 0 ∧
      ∀ c, eval c q ≠ 0 → NoCommonClosedInfinityZero k R I g d c :=
  exists_closed_infinity_avoidance_polynomial k R I hI g d hd

/-- The genuine smooth-fiber producer consumes the component avoidance polynomial,
so neither the functions nor their monomial coefficients are independently chosen. -/
theorem same_tuple_smooth_and_closed_infinity (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (I : Ideal R) (hI : I ≠ ⊥) (P : PrimeSpectrum R) [P.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ c : Fin d × Exponent σ → k, eval c q ≠ 0 ∧ NoCommonClosedInfinityZero k R I g d c ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∀ Q : PrimeSpectrum R,
        Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
          Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal →
        ∃ r ∉ Q.asIdeal, SmoothOfRelativeDimension 1
          (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
            (aeval (R := k) f).toRingHom))) := by
  obtain ⟨q₀, hq₀, hzero⟩ := exists_closed_infinity_avoidance_polynomial k R I hI g d
    (by simpa using hd.le)
  obtain ⟨c, hc, hsmooth⟩ := exists_wholeFiber_smooth_projection k R P g hg d hd
    (q₀ * q) (mul_ne_zero hq₀ hq)
  rw [map_mul, mul_ne_zero_iff] at hc
  exact ⟨c, hc.2, hzero c hc.1, hsmooth⟩

open Lean in
run_cmd do
  for name in #[``zero_dimension_actual_boundary, ``actual_closed_components,
      ``same_tuple_smooth_and_closed_infinity, ``boundaryRing_subsingleton_of_trdeg_zero,
      ``exists_closed_infinity_avoidance_polynomial] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual closed components, dimension zero, and same-tuple smoothness: audited."

end MotivicTest.QuadraticClosedInfinityAvoidance
