/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.AuxiliaryQuadraticParameter
public import Motivic.Aglib.RingTheory.Bertini.WholeFiberSmoothProjection

/-! # The same quadratic projection has whole-fiber smoothness and infinity avoidance -/
@[expose] public noncomputable section
open _root_.MvPolynomial AlgebraicGeometry
universe u
namespace QuadraticIncidence

/-- Only one auxiliary compactifying row is fixed; the original curve-base rows
simultaneously satisfy whole-fiber smoothness, infinity avoidance, and any given open.
Actual projective-image finiteness is the separate geometric consumer. -/
theorem exists_wholeFiber_smooth_infinity (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k), eval c q ≠ 0 ∧
      InfinityChart.NoCommonInfinityZero k R g d (prependParameters k d a c) ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∀ Q : PrimeSpectrum R,
        Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
          Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal →
        ∃ r ∉ Q.asIdeal, SmoothOfRelativeDimension 1
          (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
            (aeval (R := k) f).toRingHom))) := by
  obtain ⟨F, hF, hgood⟩ := InfinityChart.exists_infinity_avoidance_polynomial k R g d
    (by simpa only [Nat.cast_add, Nat.cast_one] using hd.le)
  obtain ⟨a, ha⟩ := exists_specializeAuxiliary_ne_zero k d F hF
  obtain ⟨c, hc, hsmooth⟩ := exists_wholeFiber_smooth_projection k R P g hg d hd
    (specializeAuxiliary k d a F * q) (mul_ne_zero ha hq)
  rw [map_mul] at hc
  refine ⟨a, c, (mul_ne_zero_iff.mp hc).2, ?_, hsmooth⟩
  apply hgood
  rw [← eval_specializeAuxiliary]
  exact (mul_ne_zero_iff.mp hc).1

end QuadraticIncidence
