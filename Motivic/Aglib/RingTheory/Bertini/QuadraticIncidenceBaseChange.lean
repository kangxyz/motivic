module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceAlgebra
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Base change of the original quadratic incidence coefficients

The value coordinates use finite-product base change, and the cotangent coordinates
use tensor cancellation. Both retain the original affine generators and the original
module of differentials. No flatness or field hypothesis is needed.
-/
@[expose] public noncomputable section
open MvPolynomial Module TensorProduct KaehlerDifferential
universe u v w x z
namespace QuadraticIncidence

variable (k : Type u) (R : Type v) (A : Type w) (K : Type x)
  [CommRing k] [CommRing R] [CommRing A] [CommRing K]
  [Algebra k R] [Algebra R A] [Algebra R K] [Algebra A K]
  [IsScalarTower R A K] {σ : Type z}

/-- Evaluation of a coefficient-one monomial commutes with changing coefficients. -/
theorem map_eval_monomial_one (a : σ → A) (e : σ →₀ ℕ) :
    algebraMap A K (eval a (monomial e (1 : A))) =
      eval (algebraMap A K ∘ a) (monomial e (1 : K)) := by
  rw [map_eval]
  simp

/-- The same coherence holds for each formal partial derivative. -/
theorem map_eval_pderiv_monomial_one (a : σ → A) (e : σ →₀ ℕ) (i : σ) :
    algebraMap A K (eval a (pderiv i (monomial e (1 : A)))) =
      eval (algebraMap A K ∘ a) (pderiv i (monomial e (1 : K))) := by
  rw [map_eval, ← pderiv_map]
  simp

variable [Fintype σ]

/-- Cancellation of scalar extension transports the actual generator gradient. -/
theorem baseChange_residueGeneratorGradient (g : σ → R) (c : σ → A) :
    AlgebraTensorModule.cancelBaseChange R A K K Ω[R⁄k]
        (1 ⊗ₜ[A] residueGeneratorGradient k R A g c) =
      residueGeneratorGradient k R K g (algebraMap A K ∘ c) := by
  simp only [residueGeneratorGradient, Fintype.linearCombination_apply,
    tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [smul_tmul', Algebra.smul_def]

/-- The native base-change equivalence on the literal incidence target. -/
def coefficientBaseChange (d : ℕ) :
    K ⊗[A] ((Fin d → A) × (A ⊗[R] Ω[R⁄k])) ≃ₗ[K]
      (Fin d → K) × (K ⊗[R] Ω[R⁄k]) :=
  TensorProduct.prodRight A K K (Fin d → A) (A ⊗[R] Ω[R⁄k]) ≪≫ₗ
    (TensorProduct.piScalarRight A K K (Fin d)).prodCongr
      (AlgebraTensorModule.cancelBaseChange R A K K Ω[R⁄k])

/-- Explicit value component of the base-change equivalence. -/
theorem coefficientBaseChange_tmul_fst (d : ℕ)
    (v : (Fin d → A) × (A ⊗[R] Ω[R⁄k])) :
    (coefficientBaseChange k R A K d (1 ⊗ₜ[A] v)).1 = algebraMap A K ∘ v.1 := by
  ext i
  simp [coefficientBaseChange, Algebra.smul_def]

/-- Explicit cotangent component of the base-change equivalence. -/
theorem coefficientBaseChange_tmul_snd (d : ℕ)
    (v : (Fin d → A) × (A ⊗[R] Ω[R⁄k])) :
    (coefficientBaseChange k R A K d (1 ⊗ₜ[A] v)).2 =
      AlgebraTensorModule.cancelBaseChange R A K K Ω[R⁄k] (1 ⊗ₜ[A] v.2) := by
  rfl

/-- The original universal quadratic coefficients specialize literally, with the
same generators, monomials, and cotangent module. -/
theorem coefficientBaseChange_coefficientVector (g : σ → R) (a : σ → A)
    (d : ℕ) (w : Fin d → A) (q : Fin d × Exponent σ) :
    coefficientBaseChange k R A K d (1 ⊗ₜ[A] coefficientVector k R A g a d w q) =
      coefficientVector k R K g (algebraMap A K ∘ a) d (algebraMap A K ∘ w) q := by
  have hb : (algebraMap A K ∘ fun i => algebraMap R A (g i)) =
      fun i => algebraMap R K (g i) := by
    ext i
    exact (IsScalarTower.algebraMap_apply R A K (g i)).symm
  apply Prod.ext
  · rw [coefficientBaseChange_tmul_fst]
    ext i
    simp only [coefficientVector, Function.comp_apply, Pi.single_apply]
    split_ifs <;> simp [map_eval_monomial_one, hb]
  · rw [coefficientBaseChange_tmul_snd]
    change AlgebraTensorModule.cancelBaseChange R A K K Ω[R⁄k]
        (1 ⊗ₜ[A] (w q.1 • residueGeneratorGradient k R A g
          (fun i => eval (fun j => algebraMap R A (g j))
            (pderiv i (monomial q.2.val (1 : A)))))) = _
    rw [tmul_smul, smul_tmul', Algebra.smul_def, mul_one]
    have hs (v : A ⊗[R] Ω[R⁄k]) :
        algebraMap A K (w q.1) ⊗ₜ[A] v =
          algebraMap A K (w q.1) • ((1 : K) ⊗ₜ[A] v) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [hs, map_smul, baseChange_residueGeneratorGradient]
    congr 1
    apply congrArg (residueGeneratorGradient k R K g)
    ext i
    simpa only [Function.comp_apply, hb] using
      map_eval_pderiv_monomial_one A K (fun j => algebraMap R A (g j)) q.2.val i

/-- Arbitrary scalar multiples of the original coefficients have the same coherence. -/
theorem coefficientBaseChange_tmul_coefficientVector (g : σ → R) (a : σ → A)
    (d : ℕ) (w : Fin d → A) (q : Fin d × Exponent σ) (r : K) :
    coefficientBaseChange k R A K d (r ⊗ₜ[A] coefficientVector k R A g a d w q) =
      r • coefficientVector k R K g (algebraMap A K ∘ a) d
        (algebraMap A K ∘ w) q := by
  have hr : r ⊗ₜ[A] coefficientVector k R A g a d w q =
      r • ((1 : K) ⊗ₜ[A] coefficientVector k R A g a d w q) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [hr, map_smul, coefficientBaseChange_coefficientVector]

/-- The full incidence equation, not merely its individual coefficients, transports
under the native base-change equivalence. -/
theorem coefficientBaseChange_sum (g : σ → R) (a : σ → A)
    (d : ℕ) (w : Fin d → A) (x : Fin d × Exponent σ → K) :
    coefficientBaseChange k R A K d
        (∑ q, x q ⊗ₜ[A] coefficientVector k R A g a d w q) =
      ∑ q, x q • coefficientVector k R K g (algebraMap A K ∘ a) d
        (algebraMap A K ∘ w) q := by
  simp only [map_sum, coefficientBaseChange_tmul_coefficientVector]

/-- Vanishing of the base-changed universal vector is exactly the literal
specialized incidence equation. -/
theorem sum_coefficientVector_eq_zero_iff (g : σ → R) (a : σ → A)
    (d : ℕ) (w : Fin d → A) (x : Fin d × Exponent σ → K) :
    (∑ q, x q ⊗ₜ[A] coefficientVector k R A g a d w q) = 0 ↔
      (∑ q, x q • coefficientVector k R K g (algebraMap A K ∘ a) d
        (algebraMap A K ∘ w) q) = 0 := by
  constructor
  · intro h
    rw [← coefficientBaseChange_sum k R A K g a d w x, h, map_zero]
  · intro h
    apply (coefficientBaseChange k R A K d).injective
    rw [map_zero, coefficientBaseChange_sum, h]

end QuadraticIncidence
