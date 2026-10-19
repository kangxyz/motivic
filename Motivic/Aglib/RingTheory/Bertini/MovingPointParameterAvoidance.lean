/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.MovingPointNonDominance
public import Mathlib.Algebra.MvPolynomial.Funext

/-! # One ground-field parameter choice avoids every normalized bad-point chart

All chart relations live in the same original quadratic parameter algebra.
Their product can therefore be combined with any other nonzero open condition
on that same parameter family without choosing a second projection.
-/
@[expose] public noncomputable section
open _root_.MvPolynomial
universe u
namespace QuadraticIncidence.MovingPointChart
variable (k R B : Type u) [Field k] [CommRing R] [IsDomain R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
  [Module.Finite R B] [Algebra.Smooth k R] {σ : Type u} [Fintype σ]

/-- One nonzero equation vanishes on every normalized off-diagonal chart. -/
theorem exists_nonzero_common_parameter_relation
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → B) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ)) :
    ∃ f : MvPolynomial (Fin d × Exponent σ) k, f ≠ 0 ∧
      ∀ (i₀ : Fin d) (j : σ), chartParameterMap k R B g a d i₀ j f = 0 := by
  classical
  choose f hf hz using fun q : Fin d × σ =>
    exists_nonzero_parameter_relation k R B g hg a d hd q.1 q.2
  refine ⟨∏ q, f q, Finset.prod_ne_zero_iff.mpr (fun q _ => hf q), ?_⟩
  intro i₀ j
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ (i₀, j)) (hz (i₀, j))

/-- Over an infinite field, one original coefficient tuple avoids all bad-chart
relations and any prescribed nonempty principal open in the same parameter space. -/
theorem exists_parameter_choice_avoiding_charts [Infinite k]
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → B) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (f : MvPolynomial (Fin d × Exponent σ) k) (c : Fin d × Exponent σ → k),
      f ≠ 0 ∧ eval c f ≠ 0 ∧ eval c q ≠ 0 ∧
        ∀ (i₀ : Fin d) (j : σ), chartParameterMap k R B g a d i₀ j f = 0 := by
  obtain ⟨f, hf, hz⟩ := exists_nonzero_common_parameter_relation k R B g hg a d hd
  have hprod : f * q ≠ 0 := mul_ne_zero hf hq
  have hex : ∃ c : Fin d × Exponent σ → k, eval c (f * q) ≠ 0 := by
    by_contra! h
    exact hprod (MvPolynomial.funext fun c => by simpa using h c)
  obtain ⟨c, hc⟩ := hex
  rw [map_mul] at hc
  exact ⟨f, c, hf, (mul_ne_zero_iff.mp hc).1, (mul_ne_zero_iff.mp hc).2, hz⟩

end QuadraticIncidence.MovingPointChart
