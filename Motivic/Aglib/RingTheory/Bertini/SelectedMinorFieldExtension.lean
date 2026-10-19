/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.QuadraticParameterBaseChange
public import Motivic.Aglib.RingTheory.Kaehler.PolynomialResidueGradient
public import Motivic.Aglib.RingTheory.Bertini.SelectedDeterminantScalarEvaluation
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Original selected minors at arbitrary extension-field coefficient tuples -/

@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential _root_.MvPolynomial
open scoped TensorProduct

namespace QuadraticIncidence

universe u

/-- Arbitrary K-valued quadratic coefficients are allowed. The basis of the
actual original cotangent module over K is constructed by tensor cancellation,
not supplied as a compatibility assumption. -/
theorem independent_selectedDerivative_of_eval₂_minor
    (k R κ K : Type u) [Field k] [CommRing R] [Field κ] [Field K]
    [Algebra k R] [Algebra k κ] [Algebra k K]
    [Algebra R κ] [Algebra R K] [Algebra κ K]
    [IsScalarTower k R κ] [IsScalarTower k R K] [IsScalarTower R κ K]
    {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)
    (B : Basis (Fin (d + 1)) κ (κ ⊗[R] Ω[R⁄k]))
    (c : Fin d × Exponent σ → K)
    (hc : eval₂ (algebraMap κ K) c
      (selectedDeterminant d B (selectedDerivative (k := k) (L := κ) g)) ≠ 0) :
    LinearIndependent K (fun i => selectedDerivative (k := k) (L := K) g
      (parameterTuple K σ d c i)) := by
  classical
  let e := AlgebraTensorModule.cancelBaseChange R κ K K Ω[R⁄k]
  let B' : Basis (Fin (d + 1)) K (K ⊗[R] Ω[R⁄k]) := (B.baseChange K).map e
  have hD (t : R) (j : Fin (d + 1)) :
      B'.repr (1 ⊗ₜ[R] D k R t) j =
        algebraMap κ K (B.repr (1 ⊗ₜ[R] D k R t) j) := by
    simp [B', e, Basis.map, Algebra.smul_def]
  have hmono (A : Type u) [Field A] [Algebra k A] [Algebra R A]
      [IsScalarTower k R A] (q : Fin d × Exponent σ) (i : Fin d) :
      selectedDerivative (k := k) (L := A) g (parameterBasis A σ d q i) =
        1 ⊗ₜ[R] D k R (aeval g (parameterBasis k σ d q i).val) := by
    change residueGeneratorGradient k R A g
      (fun j => eval (fun l => algebraMap R A (g l))
        (pderiv j (parameterBasis A σ d q i).val)) = _
    rw [← parameterBasis_map (algebraMap k A)]
    exact residueGeneratorGradient_map_polynomial k R A g _
  have hcoord (i : Fin d) (j : Fin (d + 1)) :
      B'.repr (selectedDerivative (k := k) (L := K) g
        (parameterTuple K σ d c i)) j =
        ∑ q, algebraMap κ K
          (B.repr (selectedDerivative (k := k) (L := κ) g
            (parameterBasis κ σ d q i)) j) * c q := by
    simp only [parameterTuple, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, hmono, hD]
    apply Finset.sum_congr rfl
    intro q _
    exact mul_comm _ _
  let π : (K ⊗[R] Ω[R⁄k]) →ₗ[K] (Fin d → K) :=
    { toFun := fun w j => B'.repr w j.castSucc
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply LinearIndependent.of_comp π
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  have he : (fun i j : Fin d =>
      π (selectedDerivative (k := k) (L := K) g (parameterTuple K σ d c i)) j) =
      fun i j => ∑ q, algebraMap κ K
        (B.repr (selectedDerivative (k := k) (L := κ) g
          (parameterBasis κ σ d q i)) j.castSucc) * c q := by
    funext i j
    exact hcoord i j.castSucc
  change Matrix.det (fun i j : Fin d =>
    π (selectedDerivative (k := k) (L := K) g (parameterTuple K σ d c i)) j) ≠ 0
  rw [he]
  exact (eval₂_selectedDeterminant (algebraMap κ K) d B
    (selectedDerivative (k := k) (L := κ) g) c) ▸ hc

end QuadraticIncidence
