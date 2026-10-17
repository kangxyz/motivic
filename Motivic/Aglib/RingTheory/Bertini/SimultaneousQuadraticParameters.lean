/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.WholeFiberEtaleInfinity
public import Motivic.Aglib.RingTheory.Bertini.QuadraticClosedInfinityAvoidance

/-! # Simultaneous original quadratic parameters for the target presentation -/
@[expose] public noncomputable section
open MvPolynomial AlgebraicGeometry
universe u
namespace QuadraticIncidence

/-- Only one auxiliary compactifying row is fixed; the original curve-base rows
simultaneously satisfy whole-fiber smoothness, infinity avoidance, and any given open.
Actual projective-image finiteness is the separate geometric consumer. -/
theorem exists_simultaneous_quadratic_parameters (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal] (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k), eval c q ≠ 0 ∧
      InfinityChart.NoCommonClosedInfinityZero k R I g d c ∧
      InfinityChart.NoCommonInfinityZero k R g d (prependParameters k d a c) ∧
      (∃ r ∉ P.asIdeal, ((algebraMap R (Localization.Away r)).comp
        (aeval (R := k) (fun i => aeval g
          (parameterTuple k σ (d + 1) (prependParameters k d a c) i).val)).toRingHom).Etale) ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∀ Q : PrimeSpectrum R,
        Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
          Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal →
        ∃ r ∉ Q.asIdeal, SmoothOfRelativeDimension 1
          (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
            (aeval (R := k) f).toRingHom))) := by
  obtain ⟨Q, hQ, hclosed⟩ := InfinityChart.exists_closed_infinity_avoidance_polynomial
    k R I hI g d (by simpa only [Nat.cast_add, Nat.cast_one] using hd.le)
  obtain ⟨a, c, hc, hinfinity, hetale, hsmooth⟩ := exists_wholeFiber_etale_infinity
    k R P g hg d hd (Q * q) (mul_ne_zero hQ hq)
  rw [map_mul] at hc
  exact ⟨a, c, (mul_ne_zero_iff.mp hc).2, hclosed c (mul_ne_zero_iff.mp hc).1,
    hinfinity, hetale, hsmooth⟩

end QuadraticIncidence
