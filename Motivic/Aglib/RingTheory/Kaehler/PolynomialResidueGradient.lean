/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Kaehler.PolynomialGeneratorGradient

/-! # The actual residue gradient of unchanged original polynomial functions -/
@[expose] public noncomputable section
open Module TensorProduct MvPolynomial
universe u
namespace KaehlerDifferential
variable (k R K : Type u) [CommRing k] [CommRing R] [CommRing K]
  [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
  {σ : Type u}

/-- Evaluating the coefficient extension is the original function evaluated at
the original field-valued point. -/
theorem eval_map_generator_polynomial (g : σ → R) (p : MvPolynomial σ k) :
    eval (fun i => algebraMap R K (g i)) (MvPolynomial.map (algebraMap k K) p) =
      algebraMap R K (aeval g p) := by
  rw [eval_map, aeval_def, eval₂_comp_left, ← IsScalarTower.algebraMap_eq k R K]
  rfl

variable [Fintype σ]

/-- The actual derivative vector used in the incidence equations is exactly
`1 ⊗ D` of the original polynomial function in the unchanged affine algebra. -/
theorem residueGeneratorGradient_map_polynomial (g : σ → R) (p : MvPolynomial σ k) :
    residueGeneratorGradient k R K g
      (fun i => eval (fun j => algebraMap R K (g j))
        (pderiv i (MvPolynomial.map (algebraMap k K) p))) =
      1 ⊗ₜ[R] D k R (aeval g p) := by
  simp only [residueGeneratorGradient, Fintype.linearCombination_apply, pderiv_map,
    eval_map_generator_polynomial, differential_aeval_generator, tmul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [TensorProduct.tmul_smul]
  exact IsScalarTower.algebraMap_smul K _ _

end KaehlerDifferential
