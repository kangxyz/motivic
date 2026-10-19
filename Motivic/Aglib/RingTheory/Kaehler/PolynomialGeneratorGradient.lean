/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Kaehler.ResidueGeneratorGradient
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # The generator gradient is the differential of the original polynomial function -/
@[expose] public noncomputable section
open Module TensorProduct _root_.MvPolynomial
universe u
namespace KaehlerDifferential
variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
  {σ : Type u} [Fintype σ]

/-- The chain rule in the original affine algebra, with its unchanged generators. -/
theorem differential_aeval_generator (g : σ → R) (p : MvPolynomial σ k) :
    D k R (aeval g p) = ∑ i, aeval g (pderiv i p) • D k R (g i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    simp only [map_add, add_smul, Finset.sum_add_distrib, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, Derivation.leibniz, aeval_X, hp]
    simp only [pderiv_mul, map_add, map_mul, aeval_X, add_smul, mul_smul,
      Finset.sum_add_distrib]
    have hs : ∑ i, aeval g p • aeval g (pderiv i (X j : MvPolynomial σ k)) • D k R (g i) =
        aeval g p • D k R (g j) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [pderiv_X_of_ne (Ne.symm hij)]
      · simp
    rw [hs]
    rw [add_comm]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

end KaehlerDifferential
