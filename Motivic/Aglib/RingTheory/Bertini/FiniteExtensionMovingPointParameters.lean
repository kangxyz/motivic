/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.MovingPointParameterAvoidance
public import Motivic.Aglib.RingTheory.FiniteExtensionPolynomialAvoidance

/-!
# Finite-extension parameters for the original moving-point bad charts

The original chart relations are unchanged. Only the final parameter choice is
made over a sufficiently large finite extension. This does not yet transport
the selected-point derivative or the complete original étale presentation.
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace QuadraticIncidence.MovingPointChart

/-- The original common relation vanishes on every normalized bad-point chart,
while a single parameter over every sufficiently large finite extension avoids
that relation and the supplied open condition. -/
theorem exists_parameter_choice_avoiding_charts_finiteExtension
    (k R B : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R] [CommRing B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    [Module.Finite R B] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    {σ : Type u} [Fintype σ]
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → B) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (f : MvPolynomial (Fin d × Exponent σ) k) (N : ℕ),
      f ≠ 0 ∧
      (∀ (i₀ : Fin d) (j : σ), chartParameterMap k R B g a d i₀ j f = 0) ∧
      ∀ (n : ℕ) [NeZero n], N < n →
        ∃ c : Fin d × Exponent σ → FiniteField.Extension k p n,
          eval₂ (algebraMap k (FiniteField.Extension k p n)) c f ≠ 0 ∧
          eval₂ (algebraMap k (FiniteField.Extension k p n)) c q ≠ 0 := by
  obtain ⟨f, hf, hz⟩ := exists_nonzero_common_parameter_relation k R B g hg a d hd
  refine ⟨f, (f * q).totalDegree, hf, hz, ?_⟩
  intro n _ hn
  obtain ⟨c, hc⟩ := exists_eval₂_ne_zero_finiteExtension k p (f * q)
    (mul_ne_zero hf hq) n hn
  rw [eval₂_mul] at hc
  exact ⟨c, (mul_ne_zero_iff.mp hc).1, (mul_ne_zero_iff.mp hc).2⟩

end QuadraticIncidence.MovingPointChart
