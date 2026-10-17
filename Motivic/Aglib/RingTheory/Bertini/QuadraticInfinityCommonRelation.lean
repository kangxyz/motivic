/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticInfinityParameterRelation
public import Mathlib.Algebra.MvPolynomial.Funext

/-! # One nonzero relation controls all original quadratic infinity charts -/
@[expose] public noncomputable section
open MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} [Finite σ]

/-- The actual same-parameter product excludes every nonempty homogeneous chart. -/
theorem exists_nonzero_common_infinity_relation (g : σ → R) (d : ℕ)
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1) :
    ∃ f : MvPolynomial (Fin (d + 1) × Exponent σ) k, f ≠ 0 ∧
      ∀ j : Exponent σ, monomialFunction k R g j ≠ 0 →
        ProjectiveEvaluationIncidence.parameterMap (boundaryRing k R g j) k
          (boundaryCoordinate k R g j) (d + 1) f = 0 := by
  classical
  let J := {j : Exponent σ // monomialFunction k R g j ≠ 0}
  choose f hf hz using fun j : J =>
    exists_nonzero_infinity_parameter_relation k R g j.1 j.2 d hd
  refine ⟨∏ j, f j, Finset.prod_ne_zero_iff.mpr (fun j _ => hf j), ?_⟩
  intro j hj
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨j, hj⟩ : J)) (hz ⟨j, hj⟩)

/-- The same quadratic family meets its infinity-avoidance open and any other
specified nonempty principal open, with no second independently chosen projection. -/
theorem exists_parameters_avoiding_infinity_relations [Infinite k]
    (g : σ → R) (d : ℕ) (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1)
    (q : MvPolynomial (Fin (d + 1) × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (f : MvPolynomial (Fin (d + 1) × Exponent σ) k)
      (c : Fin (d + 1) × Exponent σ → k),
      f ≠ 0 ∧ eval c f ≠ 0 ∧ eval c q ≠ 0 ∧
      ∀ j : Exponent σ, monomialFunction k R g j ≠ 0 →
        ProjectiveEvaluationIncidence.parameterMap (boundaryRing k R g j) k
          (boundaryCoordinate k R g j) (d + 1) f = 0 := by
  obtain ⟨f, hf, hz⟩ := exists_nonzero_common_infinity_relation k R g d hd
  have hprod : f * q ≠ 0 := mul_ne_zero hf hq
  have hex : ∃ c : Fin (d + 1) × Exponent σ → k, eval c (f * q) ≠ 0 := by
    by_contra! h
    exact hprod (MvPolynomial.funext fun c => by simpa using h c)
  obtain ⟨c, hc⟩ := hex
  rw [map_mul] at hc
  exact ⟨f, c, hf, (mul_ne_zero_iff.mp hc).1, (mul_ne_zero_iff.mp hc).2, hz⟩

end QuadraticIncidence.InfinityChart
